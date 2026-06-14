"""Primary backend: i-orca → Isabelle/Isar ``.thy`` (SPEC §4, §6).

The lowering is transliteration, not translation (SPEC §1): a proof-step row
*is* an Isar ``have``. ``## context`` facts become named theorem assumptions, so
the emitted theory is **self-contained and checkable relative to its declared
context**; holes (``hammer``/``sorry``/no method) lower to ``sorry`` with a TODO
marker for the prove loop to fill.

Row → Isar (SPEC §4):

==================================  =========================================
i-orca                              Isar
==================================  =========================================
``## proof`` heading                ``proof - … qed`` (or the declared rule)
``Id / Claim / Using / Method``     ``have Id: "Claim" using Using by Method``
``Method`` = hole                   ``sorry`` (+ TODO marker)
existential ``Claim`` + witnesses   ``obtain <vars> where Id: "Claim" …``
final step targeting the goal       ``show "<goal>" using … by …``
==================================  =========================================
"""
from __future__ import annotations

import re

from i_orca.ast import Block, Proof, Step, Theorem

_CONTRADICTION_RULES = ("ccontr", "classical", "notI")

# Isabelle's batch lexer reads propositions in terms of its own symbol table, so
# term/prop content must use the canonical ``\<name>`` escapes, not raw Unicode
# (document text in ``text \<open>…\<close>`` cartouches is exempt — it passes
# through). We translate the operators/binders/Greek an i-orca claim may use.
_TERM_SYMBOLS = {
    "⋀": r"\<And>", "⟹": r"\<Longrightarrow>", "⟶": r"\<longrightarrow>",
    "⟷": r"\<longleftrightarrow>", "⇒": r"\<Rightarrow>", "⇔": r"\<Leftrightarrow>",
    "→": r"\<rightarrow>", "←": r"\<leftarrow>", "↔": r"\<longleftrightarrow>",
    "∑": r"\<Sum>", "∏": r"\<Prod>", "∫": r"\<integral>",
    "∈": r"\<in>", "∉": r"\<notin>", "⊆": r"\<subseteq>", "⊂": r"\<subset>",
    "∩": r"\<inter>", "∪": r"\<union>", "∅": r"\<emptyset>",
    "≤": r"\<le>", "≥": r"\<ge>", "≠": r"\<noteq>", "≡": r"\<equiv>",
    "≈": r"\<approx>", "∝": r"\<propto>",
    "∧": r"\<and>", "∨": r"\<or>", "¬": r"\<not>",
    "∀": r"\<forall>", "∃": r"\<exists>", "λ": r"\<lambda>",
    "‖": r"\<parallel>", "√": r"\<surd>", "·": r"\<cdot>", "×": r"\<times>",
    "⊗": r"\<otimes>", "⊕": r"\<oplus>", "∞": r"\<infinity>", "⊥": r"\<bottom>",
    "⟨": r"\<langle>", "⟩": r"\<rangle>", "∂": r"\<partial>",
    "α": r"\<alpha>", "β": r"\<beta>", "γ": r"\<gamma>", "δ": r"\<delta>",
    "ε": r"\<epsilon>", "θ": r"\<theta>", "λ ": r"\<lambda> ", "μ": r"\<mu>",
    "ρ": r"\<rho>", "σ": r"\<sigma>", "τ": r"\<tau>", "φ": r"\<phi>",
    "Δ": r"\<Delta>", "Σ": r"\<Sigma>", "Π": r"\<Pi>", "Φ": r"\<Phi>",
}


def isar_term(s: str) -> str:
    """Rewrite a proposition's Unicode operators to Isabelle ``\\<name>`` escapes."""
    for uni, esc in _TERM_SYMBOLS.items():
        s = s.replace(uni, esc)
    return s


def _fmt_import(name: str) -> str:
    """Quote a session-qualified import (``HOL-Analysis.Inner_Product``) — the
    ``-`` and ``.`` otherwise split the token. Plain identifiers stay bare."""
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        return name
    return f'"{name}"'


def _fmt_imports(imports: list[str]) -> str:
    return " ".join(_fmt_import(i) for i in imports)


def compile_isar(theorem: Theorem) -> str:
    name = _theory_name(theorem.name)
    imports = theorem.imports or ["Main"]
    lines: list[str] = []
    lines.append(f"theory {name}")
    lines.append("  imports " + _fmt_imports(imports))
    lines.append("begin")
    lines.append("")
    lines.extend(_emit_theorem(theorem))
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def compile_isar_document(theorems: list[Theorem], *, theory_name: str = "Fieldrun") -> str:
    """Emit one self-contained ``.thy`` holding every theorem as a lemma.

    Imports are unioned (order-preserving) across the theorems; each theorem
    keeps its own ``assumes`` context, so the lemmas stay independent and the
    single theory kernel-checks as a unit.
    """
    name = _theory_name(theory_name)
    imports: list[str] = []
    for t in theorems:
        for imp in (t.imports or ["Main"]):
            if imp not in imports:
                imports.append(imp)
    if not imports:
        imports = ["Main"]

    lines: list[str] = [f"theory {name}", "  imports " + _fmt_imports(imports), "begin", ""]
    for t in theorems:
        lines.extend(_emit_theorem(t))
        lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def _emit_theorem(theorem: Theorem) -> list[str]:
    out: list[str] = []
    thm_name = _lemma_name(theorem.name)
    if theorem.description:
        out.append(rf"text \<open>{theorem.description}\<close>")
    out.append(f"theorem {thm_name}:")
    # `## context` rows → named assumptions (self-contained, checkable).
    if theorem.context:
        assume_lines = [f'    {c.name}: "{isar_term(c.statement)}"' for c in theorem.context]
        out.append("  assumes")
        out.append("\n    and\n".join(assume_lines))
    goal = isar_term(theorem.goal.statement) if theorem.goal else "True"
    out.append(f'  shows "{goal}"')

    proof = theorem.proof
    outer = proof.outer_method
    out.append(f"proof {_proof_opener(outer)}")

    # Contradiction proofs name the negated goal as an assumption.
    if outer and any(r in outer for r in _CONTRADICTION_RULES):
        out.append(rf'  assume neg: "\<not> ({goal})"')

    body = _emit_elements(proof.elements, proof, goal, indent="  ")
    out.extend(body)
    out.append("qed")
    return out


def _proof_opener(outer: str | None) -> str:
    if not outer:
        return "-"
    return f"({outer})"


def _emit_elements(
    elements: list, proof: Proof, goal: str, indent: str
) -> list[str]:
    out: list[str] = []
    top_steps = [el for el in elements if isinstance(el, Step)]
    last_top = top_steps[-1] if top_steps else None
    has_blocks = any(isinstance(el, Block) for el in elements)

    for el in elements:
        if isinstance(el, Step):
            concluding = el is last_top and not has_blocks
            out.extend(_emit_step(el, goal, indent, concluding))
        else:
            out.extend(_emit_block(el, proof, goal, indent))
    return out


def _emit_step(step: Step, goal: str, indent: str, concluding: bool) -> list[str]:
    using = _using_clause(step.using)
    if step.is_hole:
        tail = "sorry"
        using_note = f"; using: {', '.join(step.using)}" if step.using else ""
        comment = f"  (* {step.static_status}{using_note} *)"
    else:
        tail = f"by {_method(step.method)}"
        comment = ""

    claim = isar_term(step.claim)
    if step.witnesses:
        binder = " ".join(step.witnesses)
        head = f'{indent}obtain {binder} where {step.id}: "{claim}"'
    elif concluding:
        # The final step discharges the goal.
        head = f'{indent}show "{claim}"'
    else:
        head = f'{indent}have {step.id}: "{claim}"'

    if step.is_hole:
        line = f"{head} {tail}{comment}"
    elif using:
        line = f"{head} {using} {tail}"
    else:
        line = f"{head} {tail}"
    return [line]


def _emit_block(block: Block, proof: Proof, goal: str, indent: str) -> list[str]:
    """Best-effort lowering of an induction/case sub-block.

    Linear proofs (the common LLM register) need none of this; full Isar
    ``case … next`` reconstruction depends on the datatype's constructors, so we
    emit a clearly-marked scaffold and defer the exact case label to the author.
    """
    out: list[str] = []
    label = {
        "base": "base case",
        "step": "inductive step"
        + (f" (ih: {block.ih_name})" if block.ih_name else ""),
        "case": f"case {block.name}",
    }.get(block.kind, block.kind)
    out.append(f"{indent}(* {label} *)")
    if block.kind == "case" and block.name:
        out.append(f"{indent}case {block.name}")
    elif block.kind == "base":
        out.append(f"{indent}case base")
    elif block.kind == "step":
        out.append(f"{indent}case step")
    inner_steps = [el for el in block.elements if isinstance(el, Step)]
    last = inner_steps[-1] if inner_steps else None
    for el in block.elements:
        if isinstance(el, Step):
            out.extend(_emit_step(el, goal, indent + "  ", concluding=(el is last)))
    out.append(f"{indent}next" if block.kind in ("base", "step", "case") else "")
    # Drop a trailing empty / dangling ``next`` — the author closes with ``qed``.
    if out and out[-1] == "":
        out.pop()
    return out


def _using_clause(using: list[str]) -> str:
    refs = [u for u in using if u]
    return f"using {' '.join(refs)}" if refs else ""


def _method(method: str | None) -> str:
    if not method:
        return "simp"
    return method.strip()


def _theory_name(name: str) -> str:
    """A valid Isabelle theory name (letters/digits/underscore, letter-initial)."""
    cleaned = re.sub(r"[^0-9A-Za-z_]", "_", name)
    if not cleaned or not cleaned[0].isalpha():
        cleaned = "Thy_" + cleaned
    return cleaned


def _lemma_name(name: str) -> str:
    snake = re.sub(r"[^0-9A-Za-z]+", "_", name).strip("_").lower()
    if not snake or not snake[0].isalpha():
        snake = "thm_" + snake
    return snake
