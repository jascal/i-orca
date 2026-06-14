"""Scope visibility (SPEC §5, class *Scope*).

Codes: ``HYP_OUT_OF_SCOPE`` (decidable — reusing a block-local step or induction
hypothesis from outside its block) and ``VAR_UNBOUND`` (advisory — a variable
``fix``'d inside one block surfacing in another scope; only flagged when the
binder is *declared*, per SPEC §5's degrade-to-advisory rule).
"""
from __future__ import annotations

import re

from i_orca.ast import Theorem
from i_orca.verifier.resolution import Resolution


def _all_ih_names(res: Resolution) -> dict[str, str]:
    """ih-name → its block key, across the whole proof."""
    out: dict[str, str] = {}
    for b in res.blocks:
        if b.ih_name:
            out[b.ih_name] = res.block_key(b)
    return out


def check(theorem: Theorem, res: Resolution, report) -> bool:
    ok = True
    ih_names = _all_ih_names(res)

    for loc in res.located:
        visible = res.visible_ids(loc)
        for dep in loc.step.using:
            if dep in visible:
                continue
            tgt = res.by_id.get(dep)
            if tgt is not None:
                if tgt.index > loc.index or dep == loc.step.id:
                    continue  # forward ref / self-loop → structural check
                report.add_error(
                    "HYP_OUT_OF_SCOPE",
                    f"step {loc.step.id!r} cites {dep!r}, which lives in a "
                    f"different scope ({tgt.scope or 'global'}) and is not visible here",
                    "only cite global steps or steps in the same case/induction block",
                    step=loc.step.id,
                )
                ok = False
            elif dep in ih_names and ih_names[dep] != loc.scope:
                report.add_error(
                    "HYP_OUT_OF_SCOPE",
                    f"step {loc.step.id!r} cites induction hypothesis {dep!r} "
                    f"from outside its `## step` block",
                    "the induction hypothesis is only in scope inside its step block",
                    step=loc.step.id,
                )
                ok = False

    _check_var_unbound(theorem, res, report)
    return ok


def _check_var_unbound(theorem: Theorem, res: Resolution, report) -> None:
    """Advisory: a variable ``fix``'d in one block appearing in another scope."""
    # Map fixed variable → the block scope that binds it.
    bound: dict[str, str] = {}
    for b in res.blocks:
        for v in b.fixes:
            bound.setdefault(v, res.block_key(b))

    if not bound:
        return

    for loc in res.located:
        for var, owner in bound.items():
            if loc.scope == owner:
                continue
            if loc.scope != "" and _word_in(var, loc.step.claim):
                report.add_advisory(
                    "VAR_UNBOUND",
                    f"step {loc.step.id!r} uses variable {var!r}, which is "
                    f"`fix`'d in a different block ({owner})",
                    f"`fix {var}` in this scope or hoist it to the proof goal",
                    step=loc.step.id,
                )


def _word_in(word: str, text: str) -> bool:
    return re.search(rf"(?<![\w']){re.escape(word)}(?![\w'])", text) is not None
