"""Decidable structural verifier for i-orca (SPEC §5).

Runs with **zero Isabelle**. Catches the structural-nonsense LLMs produce
(circular/forward dependencies, out-of-scope hypotheses, half-proved iffs,
missing induction arms, dangling lemma names) in stable, LLM-actionable codes —
a latency accelerator for the refine loop, *not* a proof checker (SPEC §2).
"""
from i_orca.verifier.verifier import (
    FrontierHole,
    VerificationError,
    VerificationReport,
    verify,
    verify_document,
)

__all__ = [
    "verify",
    "verify_document",
    "VerificationReport",
    "VerificationError",
    "FrontierHole",
]
