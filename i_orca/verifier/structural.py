"""DAG well-formedness (SPEC §5, class *DAG*).

Codes: ``DUPLICATE_STEP_ID``, ``CIRCULAR_DEPENDENCY``, ``FORWARD_REFERENCE``,
``ORPHAN_STEP``. Catches the proof that assumes its conclusion and the
``by s7`` where ``s7`` comes later.
"""
from __future__ import annotations

from i_orca.ast import Theorem
from i_orca.verifier.resolution import Resolution


def check(theorem: Theorem, res: Resolution, report) -> bool:
    ok = True

    # Duplicate step ids — break uniqueness within the document.
    for dup in sorted(set(res.duplicate_ids)):
        report.add_error(
            "DUPLICATE_STEP_ID",
            f"step id {dup!r} is declared more than once",
            "each step Id must be unique within the theorem",
            step=dup,
        )
        ok = False

    step_ids = res.all_step_ids()

    # Cycle detection over the using-graph restricted to step ids (includes
    # self-loops). Any cycle → CIRCULAR_DEPENDENCY.
    cycle = _find_cycle(res, step_ids)
    if cycle:
        report.add_error(
            "CIRCULAR_DEPENDENCY",
            "circular dependency among steps: " + " → ".join(cycle),
            "a step may only cite steps proved before it",
            step=cycle[0],
        )
        ok = False

    # Forward references: citing a step declared later in document order. (Self
    # references are reported as cycles above, so skip them here.)
    for loc in res.located:
        for dep in loc.step.using:
            tgt = res.by_id.get(dep)
            if tgt is None or dep == loc.step.id:
                continue
            if tgt.index > loc.index:
                report.add_error(
                    "FORWARD_REFERENCE",
                    f"step {loc.step.id!r} cites {dep!r}, which is proved later",
                    "reorder so every cited step precedes its use",
                    step=loc.step.id,
                )
                ok = False

    # Orphan steps: a non-final step nothing depends on. A *warning*, not an
    # error — dead weight, not ill-formed.
    cited: set[str] = set()
    for loc in res.located:
        cited.update(loc.step.using)
    final_ids = _final_step_ids(theorem, res)
    for loc in res.located:
        if loc.step.id in cited or loc.step.id in final_ids:
            continue
        report.add_warning(
            "ORPHAN_STEP",
            f"step {loc.step.id!r} is never used and is not a concluding step",
            "remove it, or cite it where it is needed",
            step=loc.step.id,
        )

    return ok


def _find_cycle(res: Resolution, step_ids: set[str]) -> list[str] | None:
    """Return a cycle (as a node list) in the step using-graph, or ``None``."""
    adj: dict[str, list[str]] = {}
    for loc in res.located:
        adj.setdefault(loc.step.id, [])
        for dep in loc.step.using:
            if dep in step_ids:
                adj[loc.step.id].append(dep)

    WHITE, GREY, BLACK = 0, 1, 2
    color = dict.fromkeys(adj, WHITE)
    stack: list[str] = []

    def dfs(u: str) -> list[str] | None:
        color[u] = GREY
        stack.append(u)
        for v in adj.get(u, ()):
            if color.get(v, BLACK) == GREY:
                # Found a back edge: extract the cycle from the stack.
                i = stack.index(v)
                return stack[i:] + [v]
            if color.get(v, BLACK) == WHITE:
                found = dfs(v)
                if found:
                    return found
        stack.pop()
        color[u] = BLACK
        return None

    for node in adj:
        if color[node] == WHITE:
            found = dfs(node)
            if found:
                return found
    return None


def _final_step_ids(theorem: Theorem, res: Resolution) -> set[str]:
    """Ids that conclude the proof or one of its blocks (exempt from orphan)."""
    finals: set[str] = set()
    elements = theorem.proof.elements
    # Last top-level step.
    top_steps = [el for el in elements if not hasattr(el, "elements")]
    if top_steps:
        finals.add(top_steps[-1].id)
    # Last step of each block.
    for el in elements:
        if hasattr(el, "elements"):
            block_steps = el.steps()
            if block_steps:
                finals.add(block_steps[-1].id)
    return finals
