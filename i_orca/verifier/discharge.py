"""Goal discharge (SPEC §5, class *Discharge*).

Codes:

* ``UNDISCHARGED_GOAL`` — the goal is neither claimed by a step nor reached via a
  contradiction / induction / case structure, and is not explicitly held open.
* ``IFF_ONE_DIRECTION`` — the goal is an ``⟷`` but the proof establishes only one
  implication.
* ``EXISTS_NO_WITNESS`` — an existential is depended upon but never given a
  witness (no ``obtain … where``).
"""
from __future__ import annotations

import re

from i_orca.ast import Theorem
from i_orca.verifier.resolution import Resolution

_IFF_TOKENS = ("⟷", "<->", "<=>", "↔", " iff ")
_IMP_TOKENS = ("⟹", "⟶", "-->", "==>", "→", " implies ", "⇒")
_EXISTS_PREFIXES = ("∃", "\\exists", "ex ", "ex!", "∃!")
_FALSE_FORMS = {"false", "⊥", "thesis_false"}
_CONTRADICTION_RULES = ("ccontr", "noti", "classical")


def _norm(s: str) -> str:
    return re.sub(r"\s+", "", s).strip().lower()


def check(theorem: Theorem, res: Resolution, report) -> bool:
    ok = True
    goal = theorem.goal.statement if theorem.goal else None
    steps = theorem.proof.steps()

    if goal:
        if not _goal_discharged(theorem, goal, steps):
            report.add_error(
                "UNDISCHARGED_GOAL",
                f"goal {goal!r} is never concluded by a step, contradiction, or "
                f"case/induction structure",
                "add a final step whose Claim is the goal (or `False` under "
                "`rule ccontr`), or split into exhaustive cases",
            )
            ok = False

        if _is_iff(goal) and not _iff_both_directions(goal, steps):
            report.add_error(
                "IFF_ONE_DIRECTION",
                f"goal {goal!r} is an iff but only one direction is established",
                "prove both `P ⟹ Q` and `Q ⟹ P`, or the iff directly in one step",
            )
            ok = False

    _check_existentials(res, report)
    return ok


def _goal_discharged(theorem: Theorem, goal: str, steps) -> bool:
    ng = _norm(goal)
    claims = [_norm(s.claim) for s in steps]

    # (a) A step states the goal directly.
    if ng in claims:
        return True

    outer = (theorem.proof.outer_method or "").lower()

    # (b) Contradiction proof concluding `False`.
    if any(rule in outer for rule in _CONTRADICTION_RULES):
        if any(c in _FALSE_FORMS for c in claims):
            return True

    # (c) Induction / case structure: discharge is structural, judged by
    #     cases.py (base+step present / arms exhaustive). Defer to it.
    if outer.startswith(("induction", "induct", "cases")):
        return True
    if any(getattr(el, "kind", None) in ("base", "step", "case")
           for el in theorem.proof.elements):
        return True

    # (d) Final step concludes `False` even without an explicit ccontr method
    #     (the author may have set it on the proof heading textually).
    if claims and claims[-1] in _FALSE_FORMS and "false" not in ng:
        # Only accept if the heading hints at contradiction.
        return any(rule in outer for rule in _CONTRADICTION_RULES)

    return False


def _is_iff(text: str) -> bool:
    low = f" {text.lower()} "
    return any(tok in low for tok in _IFF_TOKENS)


def _split_iff(text: str) -> tuple[str, str] | None:
    for tok in ("⟷", "<->", "<=>", "↔"):
        if tok in text:
            lhs, rhs = text.split(tok, 1)
            return lhs.strip(), rhs.strip()
    if " iff " in f" {text} ":
        parts = re.split(r"\biff\b", text, maxsplit=1)
        if len(parts) == 2:
            return parts[0].strip(), parts[1].strip()
    return None


def _iff_both_directions(goal: str, steps) -> bool:
    ng = _norm(goal)
    claims = [_norm(s.claim) for s in steps]
    # The iff proved directly in one step counts as both directions.
    if ng in claims:
        return True
    split = _split_iff(goal)
    if not split:
        return True  # cannot decompose → do not over-claim a failure
    lhs, rhs = _norm(split[0]), _norm(split[1])

    def has_imp(a: str, b: str) -> bool:
        for s in steps:
            c = _norm(s.claim)
            for tok in ("⟹", "⟶", "-->", "==>", "→", "⇒", "implies"):
                t = _norm(tok)
                if t and t in c:
                    left, right = c.split(t, 1)
                    if a in left and b in right:
                        return True
        return False

    return has_imp(lhs, rhs) and has_imp(rhs, lhs)


def _is_existential(claim: str) -> bool:
    low = claim.strip().lower()
    return any(low.startswith(p) for p in _EXISTS_PREFIXES)


def _check_existentials(res: Resolution, report) -> None:
    cited: set[str] = set()
    for loc in res.located:
        cited.update(loc.step.using)
    for loc in res.located:
        s = loc.step
        if not _is_existential(s.claim) or s.witnesses:
            continue
        if s.id in cited and s.is_hole:
            report.add_warning(
                "EXISTS_NO_WITNESS",
                f"step {s.id!r} asserts an existential that later steps depend on "
                f"but never names a witness",
                "use the `obtain <vars> where <prop>` Claim form to bind a witness",
                step=s.id,
            )
