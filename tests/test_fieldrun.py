"""End-to-end: the fieldrun paper proofs parse, verify, and compile."""
from __future__ import annotations

import pytest

from i_orca.compiler import compile_isar, compile_lean4, compile_tex
from i_orca.compiler.isar import compile_isar_document
from i_orca.parser import parse_file
from i_orca.verifier import verify

EXPECTED = {
    "CardinalityInertness",
    "NonTruthFunctionalityBudget",
    "WeightedThresholdExpressivity",
    "WeightedThresholdGeneralSeparation",
    "RecoveredProbability",
    "Diffuseness",
    "DiffusenessAsymptotic",
    "TwoTemperatureSoundness",
    "PropPowerDiagram",
    "PropMarginDistance",
}


@pytest.fixture
def theorems(fieldrun_path):
    return parse_file(fieldrun_path).theorems


def test_all_paper_theorems_present(theorems):
    assert {t.name for t in theorems} == EXPECTED


def test_every_theorem_is_structurally_valid(theorems):
    for t in theorems:
        rep = verify(t)
        assert rep.valid, f"{t.name} invalid: {[e.code for e in rep.errors]}"


def test_algebraic_theorems_are_fully_methodised(theorems):
    """The closed-form results carry a concrete method on every step."""
    fully_formal = {
        "CardinalityInertness", "NonTruthFunctionalityBudget",
        "WeightedThresholdExpressivity", "RecoveredProbability",
        "PropPowerDiagram", "PropMarginDistance",
    }
    by_name = {t.name: t for t in theorems}
    for name in fully_formal:
        rep = verify(by_name[name])
        assert rep.metrics.formal_fraction_static == 1.0, name
        assert not rep.frontier, name


def test_open_results_are_honest_frontier(theorems):
    """The parts the paper leaves open are frontier holes, not false methods."""
    by_name = {t.name: t for t in theorems}
    for name in ("WeightedThresholdGeneralSeparation", "DiffusenessAsymptotic"):
        rep = verify(by_name[name])
        assert rep.valid
        assert rep.frontier, f"{name} should carry an explicit frontier hole"


def test_compiles_to_all_backends(theorems):
    for t in theorems:
        assert compile_isar(t).startswith("theory ")
        assert "\\begin{proof}" in compile_tex(t)
        assert "STRUCTURE ONLY" in compile_lean4(t)


def test_combined_theory_is_single_unit(theorems):
    out = compile_isar_document(theorems, theory_name="Fieldrun")
    assert out.startswith("theory Fieldrun")
    assert out.rstrip().endswith("end")
    # one lemma per paper result
    assert out.count("theorem ") == len(EXPECTED)


def test_corpus_kernel_shape_is_locked(theorems):
    """Regression guard on the kernel-checked corpus (Isabelle2025-2, exit 0).

    Exactly five steps are deliberate `sorry` frontier holes — the points the
    paper itself leaves open/cited. The other 21 proof steps are concrete
    methods that Isabelle's kernel accepts. If this count drifts, the corpus or
    the lowering changed and the kernel claim must be re-verified.
    """
    out = compile_isar_document(theorems, theory_name="Fieldrun")
    assert out.count("sorry") == 5

    fully_proved = {
        "CardinalityInertness", "NonTruthFunctionalityBudget",
        "WeightedThresholdExpressivity", "RecoveredProbability",
        "PropPowerDiagram", "PropMarginDistance",
    }
    by_name = {t.name: t for t in theorems}
    for name in fully_proved:
        rep = verify(by_name[name])
        assert not rep.frontier, f"{name} should be hole-free"
    # The four with holes carry exactly the paper's open/cited points.
    holes = {t.name: len(verify(t).frontier) for t in theorems if verify(t).frontier}
    assert holes == {
        "WeightedThresholdGeneralSeparation": 1,
        "Diffuseness": 1,
        "DiffusenessAsymptotic": 1,
        "TwoTemperatureSoundness": 2,
    }
