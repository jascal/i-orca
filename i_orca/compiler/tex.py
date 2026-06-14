"""Secondary backend: i-orca → LaTeX (SPEC §6).

Always emits, even for an *incomplete* proof (the early / human path). Once the
``.thy`` checks, prefer Isabelle's own document preparation over this — the
human-readable artifact is then the machine-verified one. The translation of
math syntax is best-effort: i-orca claims are written in Isabelle/HOL surface
syntax, which we lightly rewrite into LaTeX and otherwise pass through.
"""
from __future__ import annotations

from i_orca.ast import Block, Step, Theorem

# Best-effort Isabelle/Unicode → LaTeX rewrites for the common operators.
_REWRITES = [
    ("⟷", r"\leftrightarrow"), ("⟹", r"\Longrightarrow"), ("⟶", r"\longrightarrow"),
    ("⇒", r"\Rightarrow"), ("←", r"\leftarrow"), ("→", r"\to"), ("↔", r"\leftrightarrow"),
    ("∀", r"\forall "), ("∃", r"\exists "), ("¬", r"\neg "), ("∧", r"\wedge "),
    ("∨", r"\vee "), ("∈", r"\in "), ("∉", r"\notin "), ("⊆", r"\subseteq "),
    ("∩", r"\cap "), ("∪", r"\cup "), ("∑", r"\sum"), ("∏", r"\prod"),
    ("⟨", r"\langle "), ("⟩", r"\rangle "), ("‖", r"\|"), ("√", r"\sqrt"),
    ("≤", r"\le "), ("≥", r"\ge "), ("≠", r"\neq "), ("≡", r"\equiv "),
    ("·", r"\cdot "), ("×", r"\times "), ("⊗", r"\otimes "), ("⊕", r"\oplus "),
    ("∞", r"\infty "), ("→", r"\to "), ("ρ", r"\rho "), ("Δ", r"\Delta "),
    ("δ", r"\delta "), ("μ", r"\mu "), ("θ", r"\theta "), ("σ", r"\sigma "),
    ("Σ", r"\Sigma "), ("Π", r"\Pi "), ("λ", r"\lambda "), ("⊥", r"\bot "),
]


def tex_math(s: str) -> str:
    out = s
    for src, dst in _REWRITES:
        out = out.replace(src, dst)
    # Subscripts written like ``U_v`` / ``c_j^v`` survive as-is in math mode.
    return out


def tex_preamble() -> str:
    return (
        "\\documentclass{article}\n"
        "\\usepackage{amsmath,amssymb,amsthm}\n"
        "\\newtheorem{theorem}{Theorem}\n"
        "\\newtheorem{proposition}{Proposition}\n"
        "\\begin{document}\n"
    )


def compile_tex(theorem: Theorem, *, standalone: bool = True) -> str:
    body = _emit_theorem(theorem)
    if not standalone:
        return body
    return tex_preamble() + body + "\n\\end{document}\n"


def compile_tex_document(theorems: list[Theorem]) -> str:
    parts = [tex_preamble()]
    for t in theorems:
        parts.append(_emit_theorem(t))
        parts.append("")
    parts.append("\\end{document}\n")
    return "\n".join(parts)


def _emit_theorem(theorem: Theorem) -> str:
    env = "proposition" if "prop" in theorem.name.lower() else "theorem"
    lines: list[str] = []
    label = theorem.name
    goal = theorem.goal.statement if theorem.goal else "True"
    lines.append(f"\\begin{{{env}}}[{_escape(label)}]")
    if theorem.description:
        lines.append(f"{_escape(theorem.description)}\\\\")
    if theorem.context:
        ctx = "; ".join(
            f"\\texttt{{{_escape(c.name)}}}: ${tex_math(c.statement)}$" for c in theorem.context
        )
        lines.append(f"\\emph{{Given}} {ctx}.\\\\")
    lines.append(f"${tex_math(goal)}$")
    lines.append(f"\\end{{{env}}}")
    lines.append("")
    lines.append("\\begin{proof}")
    lines.append(_emit_proof(theorem))
    lines.append("\\end{proof}")
    return "\n".join(lines)


def _emit_proof(theorem: Theorem) -> str:
    outer = theorem.proof.outer_method
    rows: list[str] = []
    if outer:
        rows.append(f"\\emph{{By {_escape(outer)}.}}")
    rows.append("\\begin{align}")
    for el in theorem.proof.elements:
        if isinstance(el, Step):
            rows.append(_emit_step(el))
        elif isinstance(el, Block):
            rows.append(_emit_block(el))
    rows.append("\\end{align}")
    return "\n".join(rows)


def _emit_step(step: Step) -> str:
    claim = tex_math(step.claim)
    note = []
    if step.by:
        note.append(_escape(step.by))
    if step.using:
        note.append("using " + ", ".join(step.using))
    if step.is_hole:
        note.append(f"\\textbf{{[{step.static_status}]}}")
    elif step.method:
        note.append(f"\\texttt{{{_escape(step.method)}}}")
    annotation = (" && \\text{(" + "; ".join(note) + ")}") if note else ""
    return f"&\\textbf{{{_escape(step.id)}}}\\quad {claim}{annotation} \\\\"


def _emit_block(block: Block) -> str:
    head = {
        "base": "\\text{Base case:}",
        "step": "\\text{Inductive step"
        + (f" (ih: {block.ih_name})" if block.ih_name else "") + ":}",
        "case": f"\\text{{Case {_escape(block.name)}:}}",
    }.get(block.kind, "")
    lines = [f"&{head} \\\\"]
    for el in block.elements:
        if isinstance(el, Step):
            lines.append(_emit_step(el))
    return "\n".join(lines)


def _escape(s: str) -> str:
    for ch, rep in (("\\", r"\textbackslash{}"), ("_", r"\_"), ("&", r"\&"),
                    ("%", r"\%"), ("#", r"\#"), ("$", r"\$")):
        s = s.replace(ch, rep)
    return s
