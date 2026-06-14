"""Shared fixtures for the i-orca test suite."""
from __future__ import annotations

from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
FIELDRUN = REPO / "examples" / "fieldrun" / "fieldrun.i.orca.md"

VALID_SOURCE = """\
# theorem Trivial
> a trivial identity

## imports
| Theory |
|--------|
| Main   |

## context
| Name | Statement |
|------|-----------|
| zero | 0 = 0     |

## goal
| Statement |
|-----------|
| x = x     |

## proof
| Id | Claim | By      | Using | Method | Status |
|----|-------|---------|-------|--------|--------|
| s0 | y = y | reflexivity | — | simp | method |
| s1 | x = x | reflexivity | s0  | simp | method |
"""


@pytest.fixture
def valid_source() -> str:
    return VALID_SOURCE


@pytest.fixture
def fieldrun_path() -> Path:
    return FIELDRUN
