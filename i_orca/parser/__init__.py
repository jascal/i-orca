"""Markdown → AST front end for i-orca."""
from i_orca.parser.parser import ParseError, parse, parse_file

__all__ = ["parse", "parse_file", "ParseError"]
