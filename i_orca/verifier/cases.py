"""Case-split and induction structure (SPEC §5, class *Cases/Induction*).

Codes: ``INDUCTION_MISSING_BASE``, ``INDUCTION_MISSING_STEP`` (decidable from the
``(induction …)`` heading) and ``NON_EXHAUSTIVE_CASES`` — decidable only when the
splitting disjunction is *declared*; otherwise it degrades to **advisory** (SPEC
§5: parallel to n-orca's opaque-but-consistent symbolic dims).
"""
from __future__ import annotations

import re

from i_orca.ast import Block, Theorem
from i_orca.verifier.resolution import Resolution

_DISJ_TOKENS = ("∨", r"\/", " or ", "|")


def check(theorem: Theorem, res: Resolution, report) -> bool:
    ok = True
    proof = theorem.proof
    outer = (proof.outer_method or "").lower()
    blocks = [el for el in proof.elements if isinstance(el, Block)]

    if outer.startswith(("induction", "induct")):
        kinds = {b.kind for b in blocks}
        if "base" not in kinds:
            report.add_error(
                "INDUCTION_MISSING_BASE",
                f"`{proof.outer_method}` declares induction but no `## base` block",
                "add a `## base` block proving the base case",
            )
            ok = False
        if "step" not in kinds:
            report.add_error(
                "INDUCTION_MISSING_STEP",
                f"`{proof.outer_method}` declares induction but no `## step` block",
                "add a `## step (ih: …)` block proving the inductive step",
            )
            ok = False

    case_blocks = [b for b in blocks if b.kind == "case"]
    if case_blocks:
        ok = _check_exhaustive(theorem, res, case_blocks, report) and ok

    return ok


def _check_exhaustive(theorem, res, case_blocks, report) -> bool:
    case_names = [b.name for b in case_blocks if b.name]
    declared = _declared_disjunctions(theorem)

    if not declared:
        report.add_advisory(
            "NON_EXHAUSTIVE_CASES",
            f"case split into {case_names!r} cannot be confirmed exhaustive: no "
            f"splitting disjunction is declared",
            "declare the disjunction in `## context` (e.g. `P x ∨ ¬ P x`) or open "
            "the proof with `(cases <typed subject>)`",
        )
        return True  # advisory only — not ill-formed

    # A declared disjunction is present: every case name should appear as a
    # token in some declared disjunction.
    covered = set()
    for name in case_names:
        for disj in declared:
            if _word_in(name, disj):
                covered.add(name)
                break
    missing = [n for n in case_names if n not in covered]
    if missing:
        report.add_error(
            "NON_EXHAUSTIVE_CASES",
            f"cases {missing!r} are not covered by any declared disjunction",
            "name every disjunct of the splitting principle as a `## case`",
        )
        return False
    return True


def _declared_disjunctions(theorem: Theorem) -> list[str]:
    out: list[str] = []
    for c in theorem.context:
        if _has_disj(c.statement):
            out.append(c.statement)
    for s in theorem.proof.steps():
        if _has_disj(s.claim):
            out.append(s.claim)
    return out


def _has_disj(text: str) -> bool:
    low = f" {text} "
    return any(tok in low for tok in _DISJ_TOKENS)


def _word_in(word: str, text: str) -> bool:
    return re.search(rf"(?<![\w']){re.escape(word)}(?![\w'])", text, re.IGNORECASE) is not None
