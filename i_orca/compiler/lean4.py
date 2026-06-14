"""Secondary backend: i-orca → Lean 4 skeleton (SPEC §6, §11.4).

**Structure only, full stop.** Methods do not transfer (Isar ``metis``/``smt``
have no Lean analog) and HOL surface syntax does not parse as Lean, so the
export carries the *dependency DAG and the propositions* as structured comments
inside a compiling shell. This is cross-prover skeleton portability for
exploration — never proof transfer. We do not dress it up as more than that.
"""
from __future__ import annotations

from i_orca.ast import Block, Step, Theorem


def compile_lean4(theorem: Theorem) -> str:
    name = _lean_name(theorem.name)
    lines: list[str] = []
    lines.append("/-")
    lines.append("  Lean 4 skeleton — STRUCTURE ONLY (SPEC §6.Lean, §11.4).")
    lines.append("  Propositions are carried verbatim from i-orca in HOL syntax; they do not")
    lines.append("  parse as Lean and every method is a hole. This transfers the proof SHAPE,")
    lines.append("  not the proof. Re-state each claim in Lean/Mathlib syntax to make it real.")
    lines.append("-/")
    if theorem.imports:
        lines.append("-- isabelle imports: " + ", ".join(theorem.imports))
    lines.append("")
    if theorem.context:
        lines.append("-- context (assumed facts):")
        for c in theorem.context:
            lines.append(f"--   {c.name} : {c.statement}")
    goal = theorem.goal.statement if theorem.goal else "True"
    lines.append(f"-- goal: {goal}")
    if theorem.proof.outer_method:
        lines.append(f"-- proof method: {theorem.proof.outer_method}")
    lines.append("-- proof DAG (id  [status]  using → claim):")
    for el in theorem.proof.elements:
        lines.extend(_emit_element(el, indent="--   "))
    lines.append("")
    lines.append(f"theorem {name} : True := by")
    lines.append("  trivial")
    lines.append("")
    return "\n".join(lines) + "\n"


def _emit_element(el, indent: str) -> list[str]:
    if isinstance(el, Step):
        return [_emit_step(el, indent)]
    if isinstance(el, Block):
        head = {
            "base": "base case",
            "step": "inductive step"
            + (f" (ih: {el.ih_name})" if el.ih_name else ""),
            "case": f"case {el.name}",
        }.get(el.kind, el.kind)
        out = [f"{indent}{head}:"]
        for inner in el.elements:
            out.extend(_emit_element(inner, indent + "  "))
        return out
    return []


def _emit_step(step: Step, indent: str) -> str:
    using = ("using " + ",".join(step.using)) if step.using else "·"
    return f"{indent}{step.id}  [{step.static_status}]  {using} → {step.claim}"


def _lean_name(name: str) -> str:
    import re

    snake = re.sub(r"[^0-9A-Za-z]+", "_", name).strip("_")
    if not snake or not snake[0].isalpha():
        snake = "thm_" + snake
    return snake[0].lower() + snake[1:]
