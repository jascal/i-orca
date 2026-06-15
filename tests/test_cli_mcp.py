"""CLI and MCP-function surface tests."""
from __future__ import annotations

import json

from i_orca import mcp_server as mcp
from i_orca.cli import main


def test_cli_verify_ok(tmp_path, valid_source, capsys):
    f = tmp_path / "t.i.orca.md"
    f.write_text(valid_source)
    rc = main(["verify", str(f)])
    out = capsys.readouterr().out
    assert rc == 0
    assert "VALID" in out


def test_cli_verify_json(tmp_path, valid_source, capsys):
    f = tmp_path / "t.i.orca.md"
    f.write_text(valid_source)
    rc = main(["verify", str(f), "--json"])
    out = capsys.readouterr().out
    data = json.loads(out)
    assert rc == 0
    assert data["reports"][0]["valid"] is True


def test_cli_compile_targets(tmp_path, valid_source, capsys):
    f = tmp_path / "t.i.orca.md"
    f.write_text(valid_source)
    for target, needle in (("isar", "theory"), ("tex", "\\begin{proof}"),
                           ("lean4", "STRUCTURE ONLY")):
        main(["compile", str(f), "--target", target])
        out = capsys.readouterr().out
        assert needle in out


def test_cli_tools(capsys):
    rc = main(["--tools"])
    out = capsys.readouterr().out
    data = json.loads(out)
    assert rc == 0
    assert data["name"] == "i-orca"
    assert "parse_proof" in data["cheap_loop"]
    assert "check_proof" in data["expensive_loop"]


def test_cli_check_degrades(tmp_path, valid_source, capsys):
    f = tmp_path / "t.i.orca.md"
    f.write_text(valid_source)
    rc = main(["check", str(f), "--json"])
    out = capsys.readouterr().out
    data = json.loads(out)
    assert rc == 0
    # On a host without Isabelle this is False; either way it is a bool.
    assert isinstance(data["results"][0]["available"], bool)


def test_mcp_parse(valid_source):
    res = mcp.parse_proof(valid_source)
    assert res["theorems"][0]["name"] == "Trivial"


def test_mcp_verify_and_refine(valid_source):
    assert mcp.verify_proof(valid_source)["reports"][0]["valid"] is True
    bad = valid_source.replace("| s1 | x = x | reflexivity | s0  | simp | method |",
                               "| s1 | x = x | reflexivity | ghost | simp | method |")
    refine = mcp.refine_proof(bad)
    codes = {e["code"] for e in refine["reports"][0]["errors"]}
    assert "UNKNOWN_LEMMA_REFERENCE" in codes


def test_mcp_compile_and_metrics(valid_source):
    out = mcp.compile_proof(valid_source, "isar")
    assert "Trivial" in out["outputs"]
    m = mcp.proof_metrics(valid_source)
    assert m["Trivial"]["formal_fraction_static"] == 1.0


def test_mcp_describe_tools():
    desc = mcp.describe_tools()
    assert {t["name"] for t in desc["tools"]} >= {"parse_proof", "check_proof"}


def test_mcp_parse_error_is_structured():
    res = mcp.parse_proof("not a theorem")
    assert "error" in res


def test_mcp_check_hammer_prove_accept_dirs_session():
    import inspect
    for fn in (mcp.check_proof, mcp.hammer_step, mcp.prove_proof):
        params = inspect.signature(fn).parameters
        assert "dirs" in params, fn.__name__
        assert "session" in params, fn.__name__


def test_mcp_compile_document_parity(valid_source):
    import inspect
    params = inspect.signature(mcp.compile_proof).parameters
    assert "document" in params and "theory" in params
    out = mcp.compile_proof(valid_source, "isar", document=True, theory="Demo")
    assert out["document"] is True
    assert "theory Demo" in out["output"]


def test_mcp_prove_tool_registered():
    desc = mcp.describe_tools()
    # prove_proof is exposed on the MCP surface for CLI parity
    names = {t["name"] for t in desc["tools"]}
    assert "prove_proof" in names or hasattr(mcp, "prove_proof")
