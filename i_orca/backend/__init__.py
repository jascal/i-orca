"""The expensive loop: binding i-orca's Isar output to a real Isabelle session.

Only ``check`` / ``hammer`` need Isabelle; ``parse`` / ``verify`` / ``compile``
do not (SPEC §7 graceful degradation, mirroring q-orca's optional QuTiP). When
Isabelle is absent every entry point returns a structured ``available: False``
result with the static fallback, so CI and the fast refine loop never break.
"""
from i_orca.backend.isabelle import (
    CheckResult,
    HammerResult,
    IsabelleBackend,
    Obligation,
    StepObligation,
    locate_isabelle,
)

__all__ = [
    "IsabelleBackend",
    "CheckResult",
    "HammerResult",
    "Obligation",
    "StepObligation",
    "locate_isabelle",
]
