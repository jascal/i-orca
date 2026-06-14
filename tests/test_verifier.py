"""Verifier tests: one per stable error code, plus the happy path."""
from __future__ import annotations

from i_orca.parser import parse
from i_orca.verifier import verify


def _verify(src: str):
    return verify(parse(src).theorems[0])


def _codes(rep) -> set[str]:
    return {e.code for e in rep.errors} | {w.code for w in rep.warnings} | {
        a.code for a in rep.advisories
    }


def test_valid_proof_passes(valid_source):
    rep = _verify(valid_source)
    assert rep.valid
    assert not rep.errors


def _proof(rows: str, goal: str = "P", method: str = "## proof") -> str:
    return f"""\
# theorem T
## goal
| Statement |
|-----------|
| {goal} |
{method}
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
{rows}
"""


def test_forward_reference():
    rep = _verify(_proof("| s0 | A | x | s1 | simp | method |\n"
                         "| s1 | P | x | — | simp | method |"))
    assert "FORWARD_REFERENCE" in _codes(rep)
    assert not rep.valid


def test_circular_dependency_self_loop():
    rep = _verify(_proof("| s0 | P | x | s0 | simp | method |"))
    assert "CIRCULAR_DEPENDENCY" in _codes(rep)
    assert not rep.valid


def test_unknown_lemma_reference():
    rep = _verify(_proof("| s0 | P | x | nonesuch | simp | method |"))
    assert "UNKNOWN_LEMMA_REFERENCE" in _codes(rep)
    assert not rep.valid


def test_orphan_step_is_warning():
    rep = _verify(_proof("| s0 | A | x | — | simp | method |\n"
                         "| s1 | P | x | — | simp | method |"))
    # s0 is used by nothing and is not the concluding step → warning, still valid
    assert "ORPHAN_STEP" in _codes(rep)
    assert rep.valid


def test_duplicate_step_id():
    rep = _verify(_proof("| s0 | A | x | — | simp | method |\n"
                         "| s0 | P | x | — | simp | method |"))
    assert "DUPLICATE_STEP_ID" in _codes(rep)
    assert not rep.valid


def test_undischarged_goal():
    rep = _verify(_proof("| s0 | A | x | — | simp | method |", goal="ZZZ"))
    assert "UNDISCHARGED_GOAL" in _codes(rep)
    assert not rep.valid


def test_iff_one_direction():
    src = _proof(
        "| s0 | P ⟹ Q | x | — | simp | method |\n"
        "| s1 | P ⟷ Q | x | s0 | simp | method |",
        goal="P ⟷ Q",
    )
    rep = _verify(src)
    # The iff is proved directly by s1 (claim == goal) → both directions OK.
    assert "IFF_ONE_DIRECTION" not in _codes(rep)

    src2 = _proof("| s0 | P ⟹ Q | x | — | simp | method |", goal="P ⟷ Q")
    rep2 = _verify(src2)
    assert "IFF_ONE_DIRECTION" in _codes(rep2)


def test_induction_missing_arms():
    src = """\
# theorem T
## goal
| Statement |
|-----------|
| P n |
## proof (induction n)
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
## base
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| b0 | P 0 | base | — | simp | method |
"""
    rep = _verify(src)
    codes = _codes(rep)
    assert "INDUCTION_MISSING_STEP" in codes
    assert "INDUCTION_MISSING_BASE" not in codes  # base IS present


def test_hyp_out_of_scope():
    src = """\
# theorem T
## goal
| Statement |
|-----------|
| P |
## proof (cases x)
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
## case foo
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| f0 | A | x | — | simp | method |
## case bar
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| b0 | P | x | f0 | simp | method |
"""
    rep = _verify(src)
    assert "HYP_OUT_OF_SCOPE" in _codes(rep)


def test_non_exhaustive_cases_advisory_without_disjunction():
    src = """\
# theorem T
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
## case foo
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| f0 | P | x | — | simp | method |
"""
    rep = _verify(src)
    assert "NON_EXHAUSTIVE_CASES" in {a.code for a in rep.advisories}
    assert rep.valid  # advisory, not an error


def test_frontier_collects_holes():
    src = _proof(
        "| s0 | A | x | — | sledgehammer | hammer |\n"
        "| s1 | P | x | s0 | simp | method |"
    )
    rep = _verify(src)
    assert [h.step for h in rep.frontier] == ["s0"]
    assert rep.frontier[0].kind == "hammer"
