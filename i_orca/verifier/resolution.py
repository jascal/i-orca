"""Shared name/scope resolution used by every check (computed once per theorem).

This is the decidable core: it flattens the proof into document order, records
which scope each step lives in, and answers "what fact ids are visible to this
step?" — the single source of truth the DAG, scope, and naming checks all read.

Scope model (one level of nesting, SPEC §4): the ``## proof`` body holds
*global* steps and *blocks* (``base`` / ``step`` / ``case``). A step in block
``B`` sees global steps declared before it plus steps in ``B`` declared before
it; a global step sees only earlier global steps. Blocks do not see each other.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from i_orca.ast import Block, Step, Theorem

GLOBAL = ""  # scope key for top-level proof steps


@dataclass
class Located:
    """A step plus where it sits: document index, scope key, owning block."""

    step: Step
    index: int
    scope: str                     # GLOBAL or a block key
    block: Block | None = None


@dataclass
class Resolution:
    theorem: Theorem
    located: list[Located] = field(default_factory=list)
    by_id: dict[str, Located] = field(default_factory=dict)
    duplicate_ids: list[str] = field(default_factory=list)
    blocks: list[Block] = field(default_factory=list)

    @property
    def context_names(self) -> set[str]:
        return self.theorem.context_names

    @property
    def implicit_facts(self) -> set[str]:
        """Facts in scope without an explicit declaration.

        ``neg`` is the negated goal a contradiction proof (``rule ccontr`` /
        ``rule classical`` / ``rule notI``) introduces; ``thesis`` / ``?thesis``
        are Isar's standing references to the current goal.
        """
        facts = {"thesis", "?thesis"}
        outer = (self.theorem.proof.outer_method or "").lower()
        if any(rule in outer for rule in ("ccontr", "classical", "noti")):
            facts.add("neg")
        return facts

    def block_key(self, block: Block) -> str:
        if block.kind == "case":
            return f"case:{block.name}"
        return block.kind  # "base" / "step"

    def ih_names_in_scope(self, scope: str) -> set[str]:
        for b in self.blocks:
            if self.block_key(b) == scope and b.ih_name:
                return {b.ih_name}
        return set()

    def assume_count(self, scope: str) -> int:
        for b in self.blocks:
            if self.block_key(b) == scope:
                return len(b.assumes)
        return 0

    def visible_ids(self, loc: Located) -> set[str]:
        """Fact ids the step at ``loc`` may legitimately cite in ``Using``."""
        vis: set[str] = set(self.context_names)
        vis |= self.implicit_facts
        vis |= self.ih_names_in_scope(loc.scope)
        for other in self.located:
            if other.index >= loc.index:
                continue
            # Visible iff declared in GLOBAL (ancestor of every scope) or in the
            # same block scope.
            if other.scope == GLOBAL or other.scope == loc.scope:
                vis.add(other.step.id)
        return vis

    def all_step_ids(self) -> set[str]:
        return {loc.step.id for loc in self.located}

    def scope_of(self, step_id: str) -> str | None:
        loc = self.by_id.get(step_id)
        return loc.scope if loc else None


def build_resolution(theorem: Theorem) -> Resolution:
    res = Resolution(theorem=theorem)
    counter = 0
    seen: dict[str, int] = {}

    def add(step: Step, scope: str, block: Block | None) -> None:
        nonlocal counter
        loc = Located(step=step, index=counter, scope=scope, block=block)
        counter += 1
        res.located.append(loc)
        seen[step.id] = seen.get(step.id, 0) + 1
        # First declaration wins for resolution; duplicates are flagged.
        res.by_id.setdefault(step.id, loc)

    for el in theorem.proof.elements:
        if isinstance(el, Step):
            add(el, GLOBAL, None)
        else:  # Block
            res.blocks.append(el)
            key = res.block_key(el)
            for inner in el.elements:
                if isinstance(inner, Step):
                    add(inner, key, el)
                else:
                    # Deeper nesting is uncommon; flatten under the same key.
                    nested_key = res.block_key(inner)
                    res.blocks.append(inner)
                    for s in inner.elements:
                        if isinstance(s, Step):
                            add(s, nested_key, inner)

    res.duplicate_ids = [sid for sid, n in seen.items() if n > 1]
    return res
