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
    "MuZeroNotIrreducible",
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


def test_every_theorem_is_fully_methodised(theorems):
    """After hammering, every step of every theorem carries a concrete method:
    formal_fraction_static = 1.0 and no frontier holes anywhere."""
    for t in theorems:
        rep = verify(t)
        assert rep.metrics.formal_fraction_static == 1.0, t.name
        assert not rep.frontier, t.name


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

    After hammering all frontier holes, the combined theory lowers with ZERO
    `sorry`: every step of every theorem is a concrete method Isabelle's kernel
    accepts. If a `sorry` reappears, the corpus or the lowering regressed and the
    kernel claim must be re-verified.
    """
    out = compile_isar_document(theorems, theory_name="Fieldrun")
    assert out.count("sorry") == 0
    for t in theorems:
        assert not verify(t).frontier, f"{t.name} should be hole-free"
