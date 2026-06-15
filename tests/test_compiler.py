"""Compiler tests: Isar (primary), TeX (always emits), Lean 4 (skeleton)."""
from __future__ import annotations

from i_orca.compiler import compile_isar, compile_lean4, compile_tex
from i_orca.compiler.isar import compile_isar_document
from i_orca.parser import parse


def _thm(src: str):
    return parse(src).theorems[0]


HOLE_SRC = """\
# theorem H
## imports
| Theory |
|--------|
| Main   |
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | A | reason | — | sledgehammer | hammer |
| s1 | P | reason | s0 | simp | method |
"""


SYMBOL_SRC = """\
# theorem Sym
## imports
| Theory       |
|--------------|
| Complex_Main |
## goal
| Statement |
|-----------|
| (∑e∈Es. card (M e - H)) ≤ d * card (⋃e∈Es. (M e - H)) |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | (∑e∈Es. card (M e - H)) ≤ d * card (⋃e∈Es. (M e - H)) | cite | — | (rule foo) | method |
"""


def test_isar_translates_big_union_and_friends():
    # ⋃ / ⋂ are the indexed (big) operators — distinct from binary ∪ / ∩ — and must
    # lower to \<Union> / \<Inter>, else the batch lexer chokes on raw Unicode.
    out = compile_isar(_thm(SYMBOL_SRC))
    assert r"\<Union>" in out
    assert "⋃" not in out
    assert r"\<Sum>" in out and r"\<le>" in out


def test_isar_structure():
    out = compile_isar(_thm(HOLE_SRC))
    assert out.startswith("theory H")
    assert "imports Main" in out
    assert "theorem h:" in out
    assert 'shows "P"' in out
    assert "proof -" in out and out.rstrip().endswith("end")
    # hole → sorry, concrete method → by simp
    assert "sorry" in out
    assert "by simp" in out


def test_isar_uses_clause_and_context_assumptions():
    src = """\
# theorem C
## context
| Name | Statement |
|------|-----------|
| ax | Q |
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | P | from ax | ax | (metis ax) | method |
"""
    out = compile_isar(_thm(src))
    assert 'ax: "Q"' in out          # context → assumption
    assert "using ax by (metis ax)" in out


def test_isar_contradiction_emits_negation():
    src = """\
# theorem K
## goal
| Statement |
|-----------|
| P |
## proof (rule ccontr)
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | False | contra | neg | simp | method |
"""
    out = compile_isar(_thm(src))
    assert "proof (rule ccontr)" in out
    assert r'assume neg: "\<not> (P)"' in out


def test_tex_always_emits_for_holes():
    out = compile_tex(_thm(HOLE_SRC))
    assert "\\begin{theorem}" in out
    assert "\\begin{proof}" in out
    assert "[hammer]" in out  # the hole is annotated, not dropped


def test_lean_is_skeleton_only():
    out = compile_lean4(_thm(HOLE_SRC))
    assert "STRUCTURE ONLY" in out
    assert "theorem h : True := by" in out
    assert "trivial" in out
    # claims carried as comments, never as real Lean
    assert "-- goal: P" in out


def test_isar_document_unions_imports():
    src = HOLE_SRC + """

# theorem H2
## imports
| Theory       |
|--------------|
| Complex_Main |
## goal
| Statement |
|-----------|
| Q |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | Q | x | — | simp | method |
"""
    doc = parse(src)
    out = compile_isar_document(doc.theorems, theory_name="Combined")
    assert out.startswith("theory Combined")
    assert "Main" in out and "Complex_Main" in out
    assert out.count("theorem ") == 2
    assert out.rstrip().endswith("end")
