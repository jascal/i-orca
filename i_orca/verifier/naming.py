"""Name resolution of ``Using`` references (SPEC §5, class *Naming*).

Code: ``UNKNOWN_LEMMA_REFERENCE`` — a ``Using`` id that resolves to neither a
prior step, a ``## context`` fact, nor an in-scope induction hypothesis.

We deliberately check only the ``Using`` column (the DAG / relevance-hint
channel), not lemma names *inside* method bodies like ``(metis foo)``: those
resolve against Isabelle's session, which the static layer does not model. This
keeps the check decidable and honest (SPEC §5: catches nothing Isabelle can't).
Forward references and out-of-scope citations are handled by their own checks;
here we only flag names that exist *nowhere*.
"""
from __future__ import annotations

from i_orca.ast import Theorem
from i_orca.verifier.resolution import Resolution


def check(theorem: Theorem, res: Resolution, report) -> bool:
    ok = True
    step_ids = res.all_step_ids()
    context = res.context_names
    implicit = res.implicit_facts

    for loc in res.located:
        ih = res.ih_names_in_scope(loc.scope)
        for dep in loc.step.using:
            if dep in step_ids or dep in context or dep in ih or dep in implicit:
                continue  # resolves somewhere (scope/forward checks judge *where*)
            report.add_error(
                "UNKNOWN_LEMMA_REFERENCE",
                f"step {loc.step.id!r} cites {dep!r}, which is not a step, a "
                f"`## context` fact, or an induction hypothesis",
                f"add {dep!r} to `## context`, or fix the reference",
                step=loc.step.id,
            )
            ok = False
    return ok
