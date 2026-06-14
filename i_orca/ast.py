"""Abstract syntax for i-orca proof documents.

An ``.i.orca.md`` file declares one or more ``# theorem`` blocks. Each theorem
carries Isabelle ``imports``, a ``context`` of named ambient facts, a single
``goal`` proposition, and a ``proof`` made of *steps* (rows of the proof table)
and *blocks* (``## case`` / ``## base`` / ``## step`` scoped sub-proofs for case
splits and induction).

The AST is deliberately flat and dataclass-only: it is the single source of
truth the verifier (``i_orca.verifier``) and the three compilers
(``i_orca.compiler.{isar,tex,lean4}``) read. Nothing here depends on Isabelle.

Vocabulary (SPEC §3, §4):

* ``Step`` — one ``| Id | Claim | By | Using | Method | Status |`` row. The
  ``Claim`` is the *single source of truth*; Isar/TeX/Lean statements all derive
  from it.
* ``Block`` — a scoped sub-proof (``case`` / ``base`` / ``step``). Opens its own
  ``fix``/``assume`` scope; the verifier tracks visibility into and out of it.
* ``StepStatus`` — the lifecycle of a step (SPEC §3 table). Authored as intent;
  a backend run overwrites it with the real kernel verdict.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal, Union

# Step lifecycle (SPEC §3). ``checked``/``failed`` are populated only by a real
# Isabelle backend run; everything else is author intent / static estimate.
StepStatus = Literal["sketched", "hammer", "method", "checked", "failed"]

#: Methods that are *structured holes* rather than concrete discharge — they
#: lower to ``sorry`` and count toward the formalization *frontier*, never the
#: static formal fraction.
HOLE_METHODS = frozenset({"sledgehammer", "hammer", "sorry"})


@dataclass
class ContextFact:
    """A named ambient fact (a declared lemma/def assumed available).

    Doubles as the namespace against which ``UNKNOWN_LEMMA_REFERENCE`` resolves
    and as a Sledgehammer relevance hint.
    """

    name: str
    statement: str
    lineno: int | None = None


@dataclass
class Goal:
    """The proposition a theorem proves (the ``## goal`` section)."""

    statement: str
    lineno: int | None = None


@dataclass
class Step:
    """One proof-step row: ``| Id | Claim | By | Using | Method | Status |``."""

    id: str
    claim: str
    by: str = ""
    using: list[str] = field(default_factory=list)
    method: str | None = None
    status: StepStatus = "sketched"
    # Witnesses named on an existential claim → lowers to ``obtain <vars> where``.
    witnesses: list[str] = field(default_factory=list)
    lineno: int | None = None

    # --- derived classification (pure, no Isabelle) ------------------------- #

    @property
    def is_hole(self) -> bool:
        """A structured hole: no method, or a method that lowers to ``sorry``."""
        if self.method is None:
            return True
        return self.method.strip().lower() in HOLE_METHODS

    @property
    def has_concrete_method(self) -> bool:
        """A method present and expected to check (not a hole)."""
        return not self.is_hole

    @property
    def static_status(self) -> StepStatus:
        """Status implied by the row's syntax alone (no backend run).

        An authored ``checked``/``failed`` is backend truth and is preserved;
        otherwise we classify from the method column.
        """
        if self.status in ("checked", "failed"):
            return self.status
        if self.method is None:
            return "sketched"
        m = self.method.strip().lower()
        if m in HOLE_METHODS:
            return "hammer" if m in ("sledgehammer", "hammer") else "sketched"
        return "method"


# A proof body element is either a single step or a nested scoped block.
ProofElement = Union[Step, "Block"]

BlockKind = Literal["case", "base", "step"]


@dataclass
class Block:
    """A scoped sub-proof: ``## case <name>`` / ``## base`` / ``## step (ih: …)``.

    Each block opens a local scope. ``case`` blocks may ``fix`` fresh variables
    and ``assume`` the case hypothesis; an induction ``step`` block binds the
    induction hypothesis ``ih`` as a scoped fact. The verifier uses ``fixes`` /
    ``assumes`` / ``ih_name`` to decide what is visible inside the block and to
    flag hypotheses leaking out of it (``HYP_OUT_OF_SCOPE``).
    """

    kind: BlockKind
    name: str = ""               # case name (``## case c`` → ``c``); "" for base/step
    ih_name: str | None = None   # induction-hypothesis fact name (``ih``)
    ih_statement: str | None = None
    fixes: list[str] = field(default_factory=list)
    assumes: list[str] = field(default_factory=list)
    elements: list[ProofElement] = field(default_factory=list)
    lineno: int | None = None

    def steps(self) -> list[Step]:
        out: list[Step] = []
        for el in self.elements:
            if isinstance(el, Step):
                out.append(el)
            else:
                out.extend(el.steps())
        return out


@dataclass
class Proof:
    """The ``## proof [(method)]`` section: an outer method plus a step DAG."""

    outer_method: str | None = None     # ``(rule ccontr)``, ``(induction n)``, …
    elements: list[ProofElement] = field(default_factory=list)
    lineno: int | None = None

    def steps(self) -> list[Step]:
        """All steps, flattened depth-first (including those inside blocks)."""
        out: list[Step] = []
        for el in self.elements:
            if isinstance(el, Step):
                out.append(el)
            else:
                out.extend(el.steps())
        return out

    @property
    def induction_var(self) -> str | None:
        """The variable named in ``(induction x)`` / ``(induct x)``, if any."""
        if not self.outer_method:
            return None
        m = self.outer_method.strip()
        for kw in ("induction", "induct"):
            if m.startswith(kw):
                rest = m[len(kw):].strip()
                return rest.split()[0] if rest else None
        return None

    @property
    def cases_subject(self) -> str | None:
        """The discriminant named in ``(cases x)``, if the proof opens with one."""
        if not self.outer_method:
            return None
        m = self.outer_method.strip()
        if m.startswith("cases"):
            rest = m[len("cases"):].strip()
            return rest or None
        return None


@dataclass
class Theorem:
    """One ``# theorem Name`` block — the unit the verifier and compilers act on."""

    name: str
    description: str | None = None
    imports: list[str] = field(default_factory=list)
    context: list[ContextFact] = field(default_factory=list)
    goal: Goal | None = None
    proof: Proof = field(default_factory=Proof)
    lineno: int | None = None

    @property
    def context_names(self) -> set[str]:
        return {c.name for c in self.context}


@dataclass
class Document:
    """A parsed ``.i.orca.md`` file: one or more theorems."""

    theorems: list[Theorem] = field(default_factory=list)
