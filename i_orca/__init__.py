"""i-orca — a Markdown-table DSL for LLM-register mathematical proofs.

``i-orca : Isabelle  ::  n-orca : PyTorch  ::  orca-lang : XState``.

A document is parsed to an AST (:mod:`i_orca.ast`), checked by a decidable
*structural* verifier (:mod:`i_orca.verifier`) that runs with **zero Isabelle**,
and compiled to one of three backends (:mod:`i_orca.compiler`): Isar (primary,
checkable), TeX (always emits), and Lean 4 (best-effort skeleton). The optional
:mod:`i_orca.backend` binds the Isar output to a real, warm Isabelle session for
``check``/``hammer`` — the only part that needs the heavy dependency.
"""
from __future__ import annotations

from i_orca.ast import (
    Block,
    ContextFact,
    Document,
    Goal,
    Proof,
    Step,
    Theorem,
)
from i_orca.compiler import compile_isar, compile_lean4, compile_tex
from i_orca.metrics import ProofMetrics, compute_metrics
from i_orca.parser import ParseError, parse, parse_file
from i_orca.verifier import VerificationReport, verify, verify_document

__version__ = "0.1.0"

__all__ = [
    # AST
    "Document",
    "Theorem",
    "Proof",
    "Step",
    "Block",
    "ContextFact",
    "Goal",
    # Parser
    "parse",
    "parse_file",
    "ParseError",
    # Verifier
    "verify",
    "verify_document",
    "VerificationReport",
    # Compilers
    "compile_isar",
    "compile_tex",
    "compile_lean4",
    # Metrics
    "compute_metrics",
    "ProofMetrics",
]
