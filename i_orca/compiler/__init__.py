"""The three i-orca backends (SPEC §6), asymmetric by design.

* :func:`compile_isar` — PRIMARY, checkable: lowers to a real ``.thy``; holes →
  ``sorry``. Isabelle elaborates and kernel-checks.
* :func:`compile_tex` — secondary, always emits LaTeX even for an incomplete
  proof.
* :func:`compile_lean4` — secondary, best-effort *skeleton* transfer (structure
  only; methods become ``sorry``).
"""
from i_orca.compiler.isar import compile_isar
from i_orca.compiler.lean4 import compile_lean4
from i_orca.compiler.tex import compile_tex

__all__ = ["compile_isar", "compile_tex", "compile_lean4"]
