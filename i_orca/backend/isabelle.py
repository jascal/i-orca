"""Isabelle runner — warm session, Sledgehammer orchestration, result parsing.

This is the brittle glue the MCP surface is designed to hide (SPEC §7): heap
management, ATP orchestration, ``isabelle`` process invocation, and output
parsing. Everything here **degrades gracefully**: if no Isabelle distribution is
found, :meth:`IsabelleBackend.check_proof` and :meth:`hammer_step` return a
structured ``available=False`` result carrying the *static* fallback, never an
exception.

The production target is a persistent PIDE session keyed by ``## imports`` (so
``Complex_Main`` / ``HOL-Analysis`` is loaded once and reused). This module
implements the simpler ``isabelle build`` batch path — correct, if colder — and
marks where the warm session slots in. The per-step verdict from a batch run is
necessarily coarse: a clean load promotes every concrete-method step to
``checked`` and leaves holes on the frontier; a load error is attributed to the
step whose ``have <id>:`` the error points at.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from i_orca.ast import Theorem
from i_orca.compiler.isar import _theory_name, compile_isar


def locate_isabelle() -> str | None:
    """Find the ``isabelle`` executable via env or PATH, or return ``None``."""
    for env in ("ISABELLE", "ISABELLE_BIN"):
        cand = os.environ.get(env)
        if cand and Path(cand).exists():
            return cand
    home = os.environ.get("ISABELLE_HOME")
    if home:
        cand = Path(home) / "bin" / "isabelle"
        if cand.exists():
            return str(cand)
    return shutil.which("isabelle")


@dataclass
class StepObligation:
    """One open obligation, shaped as a prompt fragment (SPEC §7)."""

    step: str
    goal: str
    fixed: list[str] = field(default_factory=list)
    assume: list[str] = field(default_factory=list)
    using: list[str] = field(default_factory=list)
    by: str = ""
    suggestion: str = ""

    def to_dict(self) -> dict:
        return {
            "step": self.step,
            "goal": self.goal,
            "fixed": list(self.fixed),
            "assume": list(self.assume),
            "using": list(self.using),
            "by": self.by,
            "suggestion": self.suggestion,
        }


# Back-compat alias for the SPEC §7 name.
Obligation = StepObligation


@dataclass
class CheckResult:
    available: bool
    theorem: str
    steps: dict[str, str] = field(default_factory=dict)
    open_obligations: list[StepObligation] = field(default_factory=list)
    formal_fraction_real: float | None = None
    isabelle: str | None = None
    raw_output: str | None = None
    error: str | None = None

    def to_dict(self) -> dict:
        return {
            "available": self.available,
            "theorem": self.theorem,
            "steps": dict(self.steps),
            "open_obligations": [o.to_dict() for o in self.open_obligations],
            "formal_fraction_real": self.formal_fraction_real,
            "isabelle": self.isabelle,
            "error": self.error,
        }


@dataclass
class HammerResult:
    available: bool
    success: bool
    step: str
    method: str | None = None
    message: str = ""
    isabelle: str | None = None

    def to_dict(self) -> dict:
        return {
            "available": self.available,
            "success": self.success,
            "step": self.step,
            "method": self.method,
            "message": self.message,
            "isabelle": self.isabelle,
        }


class IsabelleBackend:
    """Wraps an Isabelle distribution; safe to construct with none present."""

    def __init__(self, isabelle_bin: str | None = None, *, parent_session: str | None = None,
                 extra_dirs: list[str] | None = None):
        self.isabelle_bin = isabelle_bin or locate_isabelle()
        self._parent_session = parent_session
        # Directories holding project-local theories that ``## imports`` may name
        # (e.g. a sibling ``MinimalDecider``). Emitted as ROOT ``directories`` so the
        # import resolves from source instead of being looked up as a bare file.
        self._extra_dirs = [str(Path(d).resolve()) for d in (extra_dirs or [])]

    @property
    def available(self) -> bool:
        return self.isabelle_bin is not None

    def version(self) -> str | None:
        if not self.available:
            return None
        try:
            out = subprocess.run(
                [self.isabelle_bin, "version"],
                capture_output=True, text=True, timeout=30,
            )
            return out.stdout.strip() or None
        except (subprocess.SubprocessError, OSError):
            return None

    # --- check ------------------------------------------------------------- #

    def check_proof(self, theorem: Theorem, *, timeout_s: int = 300) -> CheckResult:
        """Kernel-check the theorem's Isar lowering, per-step where possible."""
        if not self.available:
            return self._unavailable_check(theorem)

        thy_src = compile_isar(theorem)
        thy_name = _theory_name(theorem.name)
        try:
            ok, output = self._build_theory(thy_name, thy_src, theorem, timeout_s)
        except (subprocess.SubprocessError, OSError) as ex:
            return CheckResult(
                available=True, theorem=theorem.name,
                isabelle=self.version(), error=f"isabelle invocation failed: {ex}",
                steps=self._static_steps(theorem),
            )

        steps = self._attribute_results(theorem, ok, output)
        obligations = self._obligations(theorem, steps)
        n = len(steps) or 1
        n_checked = sum(1 for v in steps.values() if v == "checked")
        return CheckResult(
            available=True,
            theorem=theorem.name,
            steps=steps,
            open_obligations=obligations,
            formal_fraction_real=n_checked / n,
            isabelle=self.version(),
            raw_output=output,
        )

    def _build_theory(
        self, thy_name: str, thy_src: str, theorem: Theorem, timeout_s: int
    ) -> tuple[bool, str]:
        """Run ``isabelle build`` over a one-theory session; return (ok, output).

        (The warm-session optimisation replaces this with a routed PIDE call.)
        """
        parent = self._parent_for(theorem)
        thy_src = self._qualify_imports(thy_src)
        with tempfile.TemporaryDirectory(prefix="iorca_") as d:
            root = Path(d)
            (root / f"{thy_name}.thy").write_text(thy_src, encoding="utf-8")
            session = f"IOrca_{thy_name}"
            (root / "ROOT").write_text(
                self._root_text(session, parent, thy_name), encoding="utf-8"
            )
            # `-d <dir>` registers each project-local session ROOT so the temp
            # session can take a project session (e.g. ``ProvableOpt``, ``Hardness``)
            # as parent and resolve ``## imports`` of theories it owns. `-D <tmp>`
            # selects only the temp session to build; the parent is a cached
            # dependency. ``quick_and_dirty`` is scoped to the temp ROOT (not `-o`),
            # so the parent session is never rebuilt under it.
            cmd = [self.isabelle_bin, "build"]
            for ed in self._session_dirs():
                cmd += ["-d", ed]
            cmd += ["-D", str(root)]
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout_s,
            )
            return proc.returncode == 0, (proc.stdout + "\n" + proc.stderr)

    def _session_dirs(self) -> list[str]:
        """Extra dirs that carry a ``ROOT`` — a project-local session to discover
        via ``isabelle build -d`` so it (and the qualified imports it owns) resolve."""
        return [ed for ed in self._extra_dirs if (Path(ed) / "ROOT").exists()]

    def _project_sessions(self) -> list[tuple[str, str]]:
        """``(session_name, dir)`` for each extra dir that declares a session ROOT."""
        out: list[tuple[str, str]] = []
        for ed in self._extra_dirs:
            rootf = Path(ed) / "ROOT"
            if not rootf.exists():
                continue
            try:
                m = re.search(r'session\s+"([^"]+)"', rootf.read_text(encoding="utf-8"))
            except OSError:
                m = None
            if m:
                out.append((m.group(1), str(Path(ed).resolve())))
        return out

    def _theory_to_session(self) -> dict[str, str]:
        """Map each project-local theory base-name to the session that owns it, so a
        cross-session ``## imports`` can be rewritten to the qualified
        ``Session.Theory`` form. Bare cross-session imports do not resolve in
        Isabelle — only the importing session's own + qualified names do."""
        t2s: dict[str, str] = {}
        for sess, ed in self._project_sessions():
            for thy in Path(ed).rglob("*.thy"):
                t2s.setdefault(thy.stem, sess)
        return t2s

    def _qualify_imports(self, thy_src: str) -> str:
        """Rewrite project-local imports in the theory *header* to ``"Session.Theory"``.
        Only the text before ``begin`` is touched, so identifiers/prose in the proof
        body (and in ``text`` docstrings) are never rewritten."""
        t2s = self._theory_to_session()
        if not t2s:
            return thy_src
        head, sep, body = thy_src.partition("\nbegin")
        if not sep:
            return thy_src

        def repl(mo: re.Match[str]) -> str:
            name = mo.group(0)
            return f'"{t2s[name]}.{name}"' if name in t2s else name

        head = re.sub(r"(?<![\w.\"])[A-Za-z][\w']*(?![\w.\"])", repl, head)
        return head + sep + body

    def _root_text(self, session: str, parent: str, thy_name: str) -> str:
        """ROOT for the one-theory build session.

        Two ways a project-local ``## imports`` resolves:
        - dirs that carry a ``ROOT`` are declared as ``sessions`` (and discovered via
          ``isabelle build -d``); their theories are imported by the qualified
          ``Session.Theory`` name that ``_qualify_imports`` rewrites them to. This
          handles transitive project imports for free (the whole session is loaded);
        - dirs *without* a ROOT are registered as ``directories`` so ``## imports``
          may name a bare sibling theory resolved from source.

        ``quick_and_dirty`` is set in-session so frontier ``sorry`` holes load
        cleanly (they are attributed separately) without forcing it on the parent.
        """
        src_dirs = [ed for ed in self._extra_dirs if not (Path(ed) / "ROOT").exists()]
        blocks = ""
        proj = self._project_sessions()
        if proj:
            body = "".join(f"    {s}\n" for s, _ in proj)
            blocks += f"  sessions\n{body}"
        if src_dirs:
            body = "".join(f'    "{ed}"\n' for ed in src_dirs)
            blocks += f"  directories\n{body}"
        return (
            f'session "{session}" = "{parent}" +\n'
            f"  options [quick_and_dirty]\n"
            f"{blocks}"
            f"  theories\n    {thy_name}\n"
        )

    def _parent_for(self, theorem: Theorem) -> str:
        if self._parent_session:
            return self._parent_session
        imports = " ".join(theorem.imports).lower()
        if "hol-analysis" in imports or "complex_main" in imports or "hol-complex" in imports:
            return "HOL-Analysis"
        return "HOL"

    def _attribute_results(self, theorem: Theorem, ok: bool, output: str) -> dict[str, str]:
        steps = self._static_steps(theorem)
        if ok:
            # Clean load: every concrete-method step is kernel-accepted; holes
            # stay on the frontier (their `sorry` is what made the load clean).
            for sid, st in list(steps.items()):
                if st == "method":
                    steps[sid] = "checked"
            return steps
        # A load error: attribute it to the step whose `have <id>:` it points at.
        failed = self._find_failed_step(theorem, output)
        if failed and failed in steps:
            steps[failed] = "failed"
        return steps

    def _find_failed_step(self, theorem: Theorem, output: str) -> str | None:
        for step in theorem.proof.steps():
            # Isabelle error messages quote the failing command line.
            if re.search(rf'\b{re.escape(step.id)}\b\s*:', output) and (
                "Failed to finish proof" in output or "error" in output.lower()
            ):
                return step.id
        return None

    # --- hammer ------------------------------------------------------------ #

    def hammer_step(
        self, theorem: Theorem, step_id: str, *, timeout_s: int = 60
    ) -> HammerResult:
        """Fire Sledgehammer at a single hole; return a reconstructed method."""
        target = next((s for s in theorem.proof.steps() if s.id == step_id), None)
        if target is None:
            return HammerResult(
                available=self.available, success=False, step=step_id,
                message=f"no step {step_id!r} in theorem",
            )
        if not self.available:
            return HammerResult(
                available=False, success=False, step=step_id,
                message="Isabelle not available; cannot hammer (parse/verify/compile "
                        "still work — SPEC §7)",
            )
        # The warm-session path routes a one-obligation Sledgehammer call with
        # `using = target.using` as the relevance filter (SPEC §7.3) and parses
        # the reconstructed `by (metis …)`. Batch-mode reconstruction is not
        # exposed by `isabelle build`, so we report the obligation honestly.
        return HammerResult(
            available=True, success=False, step=step_id, isabelle=self.version(),
            message="hammer requires the warm PIDE session (not the batch builder); "
                    "obligation surfaced for the agent loop",
        )

    # --- fallbacks --------------------------------------------------------- #

    def _unavailable_check(self, theorem: Theorem) -> CheckResult:
        steps = self._static_steps(theorem)
        return CheckResult(
            available=False,
            theorem=theorem.name,
            steps=steps,
            open_obligations=self._obligations(theorem, steps),
            formal_fraction_real=None,
            error="Isabelle not found (set ISABELLE / ISABELLE_HOME, or install a "
                  "distribution). parse/verify/compile do not need it — SPEC §7.",
        )

    def _static_steps(self, theorem: Theorem) -> dict[str, str]:
        return {s.id: s.static_status for s in theorem.proof.steps()}

    def _obligations(self, theorem: Theorem, steps: dict[str, str]) -> list[StepObligation]:
        out: list[StepObligation] = []
        ctx_assumes = [c.statement for c in theorem.context]
        for s in theorem.proof.steps():
            st = steps.get(s.id, s.static_status)
            if st in ("checked", "method"):
                continue
            out.append(
                StepObligation(
                    step=s.id,
                    goal=s.claim,
                    fixed=list(s.witnesses),
                    assume=ctx_assumes,
                    using=list(s.using),
                    by=s.by,
                    suggestion=f"hammer_step({s.id}) with using=[{', '.join(s.using)}]",
                )
            )
        return out
