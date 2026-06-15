"""Backend graceful-degradation and metrics tests."""
from __future__ import annotations

import pytest

from i_orca.backend import IsabelleBackend, locate_isabelle
from i_orca.metrics import compute_metrics
from i_orca.parser import parse

SRC = """\
# theorem T
## context
| Name | Statement |
|------|-----------|
| ax | Q |
## goal
| Statement |
|-----------|
| P |
## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s0 | A | reason | ax | sledgehammer | hammer |
| s1 | B | reason | s0 | simp | method |
| s2 | P | reason | s1 | sorry | sketched |
"""


def _thm():
    return parse(SRC).theorems[0]


def test_metrics_counts():
    m = compute_metrics(_thm())
    assert m.n_steps == 3
    assert m.n_method == 1
    assert m.n_hammer == 1
    assert m.n_sketched == 1
    assert m.n_frontier == 2
    assert abs(m.formal_fraction_static - 1 / 3) < 1e-9
    assert m.formal_fraction_real is None  # no backend run


@pytest.fixture
def absent_backend(monkeypatch):
    """A backend that truly cannot find Isabelle, regardless of host.

    On a machine with Isabelle installed (and ISABELLE_HOME set) the
    ``isabelle_bin=None`` fallback would otherwise *locate* it, so we stub the
    locator and clear the env vars to exercise the graceful-degradation path.
    """
    import i_orca.backend.isabelle as iz

    for var in ("ISABELLE", "ISABELLE_BIN", "ISABELLE_HOME"):
        monkeypatch.delenv(var, raising=False)
    monkeypatch.setattr(iz, "locate_isabelle", lambda: None)
    return IsabelleBackend(isabelle_bin=None)


def test_backend_degrades_when_absent(absent_backend):
    backend = absent_backend
    assert backend.available is False
    res = backend.check_proof(_thm())
    assert res.available is False
    assert res.formal_fraction_real is None
    assert res.error and "Isabelle" in res.error
    # The static fallback still describes every step.
    assert set(res.steps) == {"s0", "s1", "s2"}
    # Open obligations carry the prompt-fragment shape (SPEC §7).
    ob = {o.step: o for o in res.open_obligations}
    assert "s0" in ob and ob["s0"].suggestion.startswith("hammer_step(s0)")
    assert ob["s0"].using == ["ax"]


def test_hammer_degrades_when_absent(absent_backend):
    res = absent_backend.hammer_step(_thm(), "s0")
    assert res.available is False
    assert res.success is False
    assert res.step == "s0"


def test_hammer_unknown_step(absent_backend):
    backend = absent_backend
    res = backend.hammer_step(_thm(), "does_not_exist")
    assert res.success is False


def test_locate_isabelle_returns_str_or_none():
    loc = locate_isabelle()
    assert loc is None or isinstance(loc, str)


# --- local-import resolution (check -d / --session parity) ------------------- #


def test_root_text_default_has_no_directories():
    b = IsabelleBackend(isabelle_bin="/fake/isabelle")
    txt = b._root_text("IOrca_T", "HOL", "T")
    assert 'session "IOrca_T" = "HOL" +' in txt
    assert "directories" not in txt
    assert "theories\n    T" in txt


def test_root_text_registers_extra_dirs(tmp_path):
    d1, d2 = tmp_path / "complexity", tmp_path / "separation"
    d1.mkdir()
    d2.mkdir()
    b = IsabelleBackend(isabelle_bin="/fake/isabelle", extra_dirs=[str(d1), str(d2)])
    # stored as resolved absolute paths
    assert b._extra_dirs == [str(d1.resolve()), str(d2.resolve())]
    txt = b._root_text("IOrca_T", "Complex_Main", "T")
    assert "  directories\n" in txt
    assert f'    "{d1.resolve()}"' in txt
    assert f'    "{d2.resolve()}"' in txt
    # directories precede the theories clause
    assert txt.index("directories") < txt.index("theories")
