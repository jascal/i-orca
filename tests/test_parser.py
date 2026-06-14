"""Parser tests: headings, tables, blocks, witnesses, status inference."""
from __future__ import annotations

import pytest

from i_orca.parser import ParseError, parse


def test_parse_basic(valid_source):
    doc = parse(valid_source)
    assert len(doc.theorems) == 1
    t = doc.theorems[0]
    assert t.name == "Trivial"
    assert t.description == "a trivial identity"
    assert t.imports == ["Main"]
    assert [c.name for c in t.context] == ["zero"]
    assert t.context[0].statement == "0 = 0"
    assert t.goal.statement == "x = x"
    steps = t.proof.steps()
    assert [s.id for s in steps] == ["s0", "s1"]
    assert steps[1].using == ["s0"]
    assert steps[0].method == "simp"


def test_status_inference():
    src = """\
# theorem T
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| a | P1 | x | — | — | |
| b | P2 | x | — | sledgehammer | |
| c | P3 | x | — | sorry | |
| d | P  | x | a,b,c | simp | |
"""
    t = parse(src).theorems[0]
    by_id = {s.id: s for s in t.proof.steps()}
    assert by_id["a"].static_status == "sketched"  # no method
    assert by_id["b"].static_status == "hammer"     # sledgehammer
    assert by_id["c"].static_status == "sketched"   # sorry
    assert by_id["d"].static_status == "method"


def test_obtain_witnesses():
    src = """\
# theorem T
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | obtain p q where P p q | def | — | blast | method |
| s1 | P | x | s0 | simp | method |
"""
    t = parse(src).theorems[0]
    s0 = t.proof.steps()[0]
    assert s0.witnesses == ["p", "q"]
    assert s0.claim == "P p q"


def test_induction_blocks():
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
## step (ih: P n)
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | P (Suc n) | step | ih | simp | method |
"""
    t = parse(src).theorems[0]
    assert t.proof.outer_method == "induction n"
    assert t.proof.induction_var == "n"
    kinds = [getattr(el, "kind", None) for el in t.proof.elements]
    assert "base" in kinds and "step" in kinds
    # ih is bound on the step block
    step_block = [el for el in t.proof.elements if getattr(el, "kind", None) == "step"][0]
    assert step_block.ih_name == "ih"


def test_multiple_theorems():
    src = VALID2 = """\
# theorem A
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s | P | x | — | simp | method |

# theorem B
## goal
| Statement |
|-----------|
| Q |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s | Q | x | — | simp | method |
"""
    del VALID2
    doc = parse(src)
    assert [t.name for t in doc.theorems] == ["A", "B"]


def test_no_theorem_raises():
    with pytest.raises(ParseError):
        parse("## just a section\n| a |\n|---|\n| b |\n")


def test_dash_cells_are_empty():
    src = """\
# theorem T
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | P | — | — | — | |
"""
    s0 = parse(src).theorems[0].proof.steps()[0]
    assert s0.using == []
    assert s0.method is None
    assert s0.by == ""
