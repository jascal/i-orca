"""Report types and the verification orchestrator.

``verify(theorem)`` runs five decidable check families in dependency order and
returns a :class:`VerificationReport` carrying errors (ill-formed → block the
Isar lowering), warnings, advisories (decidable only when the splitting
principle is declared — SPEC §5), the *frontier* of holes, and the static
metrics. Truth is never asserted here (SPEC §2).
"""
from __future__ import annotations

from dataclasses import dataclass, field

from i_orca.ast import Theorem
from i_orca.metrics import ProofMetrics, compute_metrics
from i_orca.verifier import cases as _cases
from i_orca.verifier import discharge as _discharge
from i_orca.verifier import naming as _naming
from i_orca.verifier import scope as _scope
from i_orca.verifier import structural as _structural
from i_orca.verifier.resolution import build_resolution

SEVERITIES = ("error", "warning", "advisory")


@dataclass
class VerificationError:
    code: str
    message: str
    suggestion: str | None = None
    severity: str = "error"   # "error" | "warning" | "advisory"
    step: str | None = None

    def to_dict(self) -> dict:
        return {
            "code": self.code,
            "message": self.message,
            "suggestion": self.suggestion,
            "severity": self.severity,
            "step": self.step,
        }


@dataclass
class FrontierHole:
    """A step on the formalization frontier — a structured hole, never an error."""

    step: str
    claim: str
    kind: str   # "hammer" | "sketched"
    by: str = ""
    using: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "step": self.step,
            "claim": self.claim,
            "kind": self.kind,
            "by": self.by,
            "using": list(self.using),
        }


@dataclass
class VerificationReport:
    theorem: str
    valid: bool = True
    errors: list[VerificationError] = field(default_factory=list)
    warnings: list[VerificationError] = field(default_factory=list)
    advisories: list[VerificationError] = field(default_factory=list)
    frontier: list[FrontierHole] = field(default_factory=list)
    dag: dict = field(default_factory=dict)
    metrics: ProofMetrics = field(default_factory=ProofMetrics)

    # --- recording helpers -------------------------------------------------- #

    def add(
        self,
        code: str,
        message: str,
        suggestion: str | None = None,
        severity: str = "error",
        step: str | None = None,
    ) -> None:
        err = VerificationError(code, message, suggestion, severity, step)
        if severity == "error":
            self.errors.append(err)
            self.valid = False
        elif severity == "warning":
            self.warnings.append(err)
        else:
            self.advisories.append(err)

    def add_error(self, code, message, suggestion=None, step=None) -> None:
        self.add(code, message, suggestion, "error", step)

    def add_warning(self, code, message, suggestion=None, step=None) -> None:
        self.add(code, message, suggestion, "warning", step)

    def add_advisory(self, code, message, suggestion=None, step=None) -> None:
        self.add(code, message, suggestion, "advisory", step)

    def to_dict(self) -> dict:
        return {
            "theorem": self.theorem,
            "valid": self.valid,
            "errors": [e.to_dict() for e in self.errors],
            "warnings": [w.to_dict() for w in self.warnings],
            "advisories": [a.to_dict() for a in self.advisories],
            "frontier": [h.to_dict() for h in self.frontier],
            "formal_fraction_static": self.metrics.formal_fraction_static,
            "metrics": self.metrics.to_dict(),
            "dag": self.dag,
        }


def verify(theorem: Theorem, *, strict: bool = False) -> VerificationReport:
    """Run the full structural pipeline against one theorem."""
    report = VerificationReport(theorem=theorem.name)
    report.metrics = compute_metrics(theorem)
    _collect_frontier(theorem, report)

    res = build_resolution(theorem)
    report.dag = _build_dag(theorem, res)

    # Stage 1 — DAG well-formedness (duplicates, cycles, forward refs, orphans).
    structural_ok = _structural.check(theorem, res, report)
    # Naming resolves Using references against context/scope; runs regardless so
    # an LLM gets every dangling-name error in one pass.
    _naming.check(theorem, res, report)
    # Scope is meaningful even if the DAG has issues; it reads the same res.
    _scope.check(theorem, res, report)
    # Discharge (goal closed, iff both ways, existentials witnessed).
    _discharge.check(theorem, res, report)
    # Cases / induction exhaustiveness and arm presence.
    _cases.check(theorem, res, report)

    # ``structural_ok`` is informational: later stages already guard themselves.
    del structural_ok

    if strict:
        for w in list(report.warnings):
            report.errors.append(w)
            report.valid = False
        report.warnings.clear()

    return report


def verify_document(theorems: list[Theorem], *, strict: bool = False) -> list[VerificationReport]:
    return [verify(t, strict=strict) for t in theorems]


def _collect_frontier(theorem: Theorem, report: VerificationReport) -> None:
    for step in theorem.proof.steps():
        st = step.static_status
        if st in ("hammer", "sketched"):
            report.frontier.append(
                FrontierHole(
                    step=step.id,
                    claim=step.claim,
                    kind=st,
                    by=step.by,
                    using=list(step.using),
                )
            )


def _build_dag(theorem: Theorem, res) -> dict:
    nodes = [loc.step.id for loc in res.located]
    edges = []
    known = res.all_step_ids() | res.context_names
    for loc in res.located:
        for dep in loc.step.using:
            edges.append({"from": loc.step.id, "to": dep, "resolved": dep in known})
    return {"nodes": nodes, "edges": edges, "context": sorted(res.context_names)}
