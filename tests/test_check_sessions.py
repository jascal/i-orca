"""`i-orca check` project-local session resolution (no Isabelle needed).

Covers the backend that lets ``check <file>`` kernel-check theorems whose
``## imports`` name project-local theories: a sibling ``ROOT`` is declared as a
``sessions`` dependency and the project-local imports are rewritten to the
qualified ``Session.Theory`` form (bare cross-session imports do not resolve).
"""
from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

from i_orca.backend import IsabelleBackend
from i_orca.cli import _augment_session


def _project(tmp_path: Path) -> Path:
    d = tmp_path / "corpus"
    d.mkdir()
    (d / "ROOT").write_text('session "Foo" = "HOL" +\n  theories\n    Bar\n')
    (d / "Bar.thy").write_text("theory Bar\n  imports Main\nbegin\nend\n")
    (d / "corpus.i.orca.md").write_text("# theorem T\n")
    return d


def test_project_sessions_and_theory_map(tmp_path):
    d = _project(tmp_path)
    b = IsabelleBackend(extra_dirs=[str(d)])
    assert b._project_sessions() == [("Foo", str(d.resolve()))]
    assert b._theory_to_session() == {"Bar": "Foo"}


def test_qualify_imports_header_only(tmp_path):
    d = _project(tmp_path)
    b = IsabelleBackend(extra_dirs=[str(d)])
    src = (
        "theory DemandX\n  imports Bar Main\nbegin\n"
        "text \\<open>see Bar for details\\<close>\n"
        'theorem t: "Bar" by simp\nend\n'
    )
    out = b._qualify_imports(src)
    head, _, body = out.partition("\nbegin")
    assert '"Foo.Bar"' in head                 # project import is qualified
    assert "Main" in head and '"Foo.Main"' not in head  # library import untouched
    assert "see Bar for details" in body       # prose in the body untouched
    assert 'theorem t: "Bar"' in body          # body identifier untouched


def test_qualify_imports_noop_without_project_dirs():
    b = IsabelleBackend(extra_dirs=[])
    src = "theory X\n  imports Bar\nbegin\nend\n"
    assert b._qualify_imports(src) == src


def test_root_text_declares_sessions_and_qad(tmp_path):
    d = _project(tmp_path)
    b = IsabelleBackend(extra_dirs=[str(d)])
    root = b._root_text("IOrca_X", "HOL", "DemandX")
    assert "sessions\n    Foo" in root
    assert "quick_and_dirty" in root
    assert "directories" not in root  # a ROOT-bearing dir is a session, not a src dir


def test_augment_session_autoregisters_root_dir(tmp_path):
    d = _project(tmp_path)
    args = SimpleNamespace(dir=None, session=None, file=str(d / "corpus.i.orca.md"))
    extra, session = _augment_session(args)
    assert any(Path(e).resolve() == d.resolve() for e in extra)
    assert session is None  # the library parent stays inferred unless --session given


def test_augment_session_skips_dir_without_root(tmp_path):
    f = tmp_path / "loose.i.orca.md"
    f.write_text("# theorem T\n")
    args = SimpleNamespace(dir=None, session=None, file=str(f))
    extra, _ = _augment_session(args)
    assert extra == []
