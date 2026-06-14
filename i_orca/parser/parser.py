"""Markdown parser for i-orca proof documents.

Parses ``.i.orca.md`` source into one or more :class:`~i_orca.ast.Theorem`
objects wrapped in a :class:`~i_orca.ast.Document`. Like its n-orca/q-orca
siblings the grammar is small and line-oriented: we tokenise ``#``/``##``
headings and Markdown tables directly rather than pulling in a general
Markdown library, because the surface is exactly tables + blockquotes.

Document shape (SPEC §4)::

    # theorem Name
    > informal one-line description
    ## imports         | Theory |
    ## context         | Name | Statement |
    ## goal            | Statement |
    ## proof (method)  | Id | Claim | By | Using | Method | Status |
    ## base            (proof sub-block: induction base)
    ## step (ih: …)    (proof sub-block: induction step, binds ih)
    ## case <name>     (proof sub-block: a case split arm)

Everything from ``## proof`` to the next ``# theorem`` (or EOF) belongs to one
:class:`~i_orca.ast.Proof`; ``## base`` / ``## step`` / ``## case`` headings in
that span open scoped :class:`~i_orca.ast.Block` sub-proofs.
"""
from __future__ import annotations

import re
from pathlib import Path

from i_orca.ast import (
    Block,
    ContextFact,
    Document,
    Goal,
    Proof,
    Step,
    Theorem,
)

_DASHES = {"", "-", "—", "–", "n/a", "none"}

_H1_THEOREM_RE = re.compile(r"^#\s+theorem\s+(\S+)\s*$", re.IGNORECASE)
_H1_ANY_RE = re.compile(r"^#\s+(?!#)(.+?)\s*$")
_H2_RE = re.compile(r"^##\s+(?!#)(.+?)\s*$")
_BLOCKQUOTE_RE = re.compile(r"^>\s?(.*)$")
_TABLE_ROW_RE = re.compile(r"^\s*\|(.+)\|\s*$")
_SEP_CELL_RE = re.compile(r"^:?-+:?$")
_OBTAIN_RE = re.compile(r"^obtain\s+(.+?)\s+where\s+(.+)$", re.IGNORECASE)
_IH_RE = re.compile(r"\bih\s*:\s*(.+)$", re.IGNORECASE)

_VALID_STATUS = {"sketched", "hammer", "method", "checked", "failed"}


class ParseError(Exception):
    def __init__(self, message: str, line: int | None = None):
        super().__init__(f"line {line}: {message}" if line else message)
        self.line = line
        self.message = message


def parse_file(path: str | Path) -> Document:
    """Parse an ``.i.orca.md`` file into a :class:`Document`."""
    text = Path(path).read_text(encoding="utf-8")
    return parse(text)


def parse(source: str) -> Document:
    """Parse ``source`` into a :class:`Document` of one or more theorems."""
    lines = source.splitlines()
    numbered = list(enumerate(lines, start=1))

    # Split into theorem spans on `# theorem` headings (any other H1 ends the
    # current theorem but does not start one).
    spans: list[list[tuple[int, str]]] = []
    current: list[tuple[int, str]] | None = None
    for lineno, raw in numbered:
        if _H1_THEOREM_RE.match(raw):
            current = [(lineno, raw)]
            spans.append(current)
        elif _H1_ANY_RE.match(raw):
            current = None  # a non-theorem H1 closes the current theorem span
        elif current is not None:
            current.append((lineno, raw))

    if not spans:
        raise ParseError("no `# theorem <Name>` heading found")

    return Document(theorems=[_parse_theorem(span) for span in spans])


def _parse_theorem(span: list[tuple[int, str]]) -> Theorem:
    h1_lineno, h1 = span[0]
    name = _H1_THEOREM_RE.match(h1).group(1)
    thm = Theorem(name=name, lineno=h1_lineno)

    # Optional blockquote description directly after the heading.
    body_start = 1
    for idx in range(1, len(span)):
        _, line = span[idx]
        if not line.strip():
            continue
        bq = _BLOCKQUOTE_RE.match(line)
        if bq and not _H2_RE.match(line):
            thm.description = (bq.group(1).strip() or None)
            body_start = idx + 1
        break

    # Carve the rest into `##` sections, preserving order.
    sections: list[tuple[str, str, int, list[tuple[int, str]]]] = []
    cur_head: str | None = None
    cur_arg = ""
    cur_lineno = h1_lineno
    cur_body: list[tuple[int, str]] = []

    def flush() -> None:
        nonlocal cur_head, cur_arg, cur_body, cur_lineno
        if cur_head is not None:
            sections.append((cur_head, cur_arg, cur_lineno, cur_body))
        cur_head, cur_arg, cur_body = None, "", []

    for lineno, line in span[body_start:]:
        h2 = _H2_RE.match(line)
        if h2:
            flush()
            kind, arg = _classify_heading(h2.group(1).strip())
            cur_head, cur_arg, cur_lineno, cur_body = kind, arg, lineno, []
        elif cur_head is not None:
            cur_body.append((lineno, line))
    flush()

    # Dispatch. `proof` and the block headings that follow it accumulate into a
    # single Proof.
    proof: Proof | None = None
    for kind, arg, lineno, body in sections:
        if kind == "imports":
            thm.imports.extend(_parse_single_col(body))
        elif kind == "context":
            thm.context.extend(_parse_context(body))
        elif kind == "goal":
            cols = _parse_single_col(body)
            if cols:
                thm.goal = Goal(statement=cols[0], lineno=lineno)
        elif kind == "proof":
            proof = Proof(outer_method=(arg or None), lineno=lineno)
            proof.elements.extend(_parse_steps(body))
            thm.proof = proof
        elif kind in ("base", "step", "case"):
            if proof is None:
                raise ParseError(
                    f"`## {kind}` block appears before any `## proof` section",
                    lineno,
                )
            proof.elements.append(_parse_block(kind, arg, lineno, body))
        # Unknown sections are ignored (the verifier can warn elsewhere).

    return thm


def _classify_heading(text: str) -> tuple[str, str]:
    """Map a raw ``##`` heading to ``(kind, argument)``.

    ``proof (rule ccontr)`` → ``("proof", "rule ccontr")``;
    ``case foo``            → ``("case", "foo")``;
    ``step (ih: P n)``      → ``("step", "ih: P n")``;
    ``base``                → ``("base", "")``.
    """
    low = text.lower()
    first = low.split()[0] if low.split() else low
    if first in ("imports", "context", "goal", "base"):
        return first, ""
    if first == "proof":
        return "proof", _strip_outer_parens(text[len("proof"):].strip())
    if first == "case":
        return "case", text[len("case"):].strip()
    if first == "step":
        return "step", _strip_outer_parens(text[len("step"):].strip())
    return first, text


def _strip_outer_parens(s: str) -> str:
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        return s[1:-1].strip()
    return s


def _parse_block(kind: str, arg: str, lineno: int, body: list[tuple[int, str]]) -> Block:
    block = Block(kind=kind, lineno=lineno)  # type: ignore[arg-type]
    if kind == "case":
        block.name = arg
    elif kind == "step":
        m = _IH_RE.search(arg)
        if m:
            block.ih_name = "ih"
            block.ih_statement = m.group(1).strip()
    # `> fix x y` / `> assume H` blockquote directives, then a step table.
    for _ln, line in body:
        bq = _BLOCKQUOTE_RE.match(line)
        if bq:
            directive = bq.group(1).strip()
            low = directive.lower()
            if low.startswith("fix "):
                block.fixes.extend(_split_names(directive[4:]))
            elif low.startswith("assume "):
                block.assumes.append(directive[7:].strip())
            continue
    block.elements.extend(_parse_steps(body))
    return block


# --------------------------------------------------------------------------- #
#  Tables
# --------------------------------------------------------------------------- #


def _table_rows(body: list[tuple[int, str]]) -> list[tuple[int, list[str]]]:
    """Yield ``(lineno, cells)`` for table data rows (header + separator dropped)."""
    rows: list[tuple[int, list[str]]] = []
    for lineno, line in body:
        m = _TABLE_ROW_RE.match(line)
        if not m:
            continue
        cells = [c.strip() for c in m.group(1).split("|")]
        if cells and all(_SEP_CELL_RE.match(c) for c in cells if c):
            continue
        rows.append((lineno, cells))
    return rows[1:] if rows else []  # drop the header row


def _parse_single_col(body: list[tuple[int, str]]) -> list[str]:
    out: list[str] = []
    for _, cells in _table_rows(body):
        if cells and cells[0] and cells[0].lower() not in _DASHES:
            out.append(cells[0])
    return out


def _parse_context(body: list[tuple[int, str]]) -> list[ContextFact]:
    out: list[ContextFact] = []
    for lineno, cells in _table_rows(body):
        if len(cells) < 2 or not cells[0]:
            continue
        out.append(ContextFact(name=cells[0], statement=cells[1], lineno=lineno))
    return out


def _parse_steps(body: list[tuple[int, str]]) -> list[Step]:
    out: list[Step] = []
    for lineno, cells in _table_rows(body):
        # Pad to six columns: Id | Claim | By | Using | Method | Status
        cells = (cells + [""] * 6)[:6]
        sid, claim, by, using, method, status = cells
        if not sid or sid.lower() in _DASHES:
            continue
        out.append(_make_step(sid, claim, by, using, method, status, lineno))
    return out


def _make_step(
    sid: str, claim: str, by: str, using: str, method: str, status: str, lineno: int
) -> Step:
    witnesses: list[str] = []
    m = _OBTAIN_RE.match(claim.strip())
    if m:
        witnesses = _split_names(m.group(1))
        claim = m.group(2).strip()

    using_ids = [
        u.strip()
        for u in re.split(r"[,;]", using)
        if u.strip() and u.strip().lower() not in _DASHES
    ]
    meth = None if method.strip().lower() in _DASHES else method.strip()
    by = "" if by.strip().lower() in _DASHES else by.strip()

    status_low = status.strip().lower()
    if status_low in _VALID_STATUS:
        resolved = status_low
    else:
        resolved = _infer_status(meth)

    return Step(
        id=sid,
        claim=claim.strip(),
        by=by.strip(),
        using=using_ids,
        method=meth,
        status=resolved,  # type: ignore[arg-type]
        witnesses=witnesses,
        lineno=lineno,
    )


def _infer_status(method: str | None) -> str:
    if method is None:
        return "sketched"
    m = method.strip().lower()
    if m in ("sledgehammer", "hammer"):
        return "hammer"
    if m == "sorry":
        return "sketched"
    return "method"


def _split_names(s: str) -> list[str]:
    # ``p q :: int`` / ``p, q`` / ``x y`` → ["p", "q"] (drop a type annotation)
    s = s.split("::")[0]
    return [tok for tok in re.split(r"[,\s]+", s.strip()) if tok]
