# i-orca

**A Markdown-table DSL for mathematical proofs at the register LLMs naturally
produce** — more structured and machine-readable than prose, more informal than
Lean tactic mode — whose canonical backend is **Isabelle/Isar**, with **TeX** and
**Lean 4** as secondary exports.

```
i-orca : Isabelle  ::  n-orca : PyTorch  ::  orca-lang : XState
```

i-orca is a Pillar-1 sibling in the [Orca language family](../RESEARCH_MANIFESTO.md):
a Markdown spec layer over a powerful-but-verbose substrate, adding **cheap
static verification before you run the heavy backend**.

> ⚠️ **i-orca is a structural linter + scaffold compiler, NOT a proof checker.**
> A green `verify` means the proof *skeleton* is well-formed — a decidable,
> strictly-weaker property. It does **not** mean the proof is true. Only
> Isabelle's kernel (`i-orca check`, step status `checked`) certifies truth.

## Install

```bash
uv venv --python 3.12 .venv
uv pip install -e ".[dev]"      # add ",mcp" for the MCP server
.venv/bin/pytest                # 46 tests
```

The cheap loop (`parse`/`verify`/`compile`) needs zero Isabelle. The expensive
loop (`check`/`hammer`) needs an [Isabelle](https://isabelle.in.tum.de)
distribution (i-orca tracks **Isabelle2025-2**) — point i-orca at it with
`ISABELLE_HOME` (or put `isabelle` on `PATH`). Without it, `check`/`hammer`
degrade gracefully. See [`GETTING_STARTED.md`](GETTING_STARTED.md) for Linux/macOS
install steps, heap-image build, and the MCP-server environment gotcha.

## A proof in i-orca

```markdown
# theorem RecoveredProbability
> The normalised mass m(v)/Σ m is exactly the softmax.

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name  | Statement |
|-------|-----------|
| M0pos | M0 > 0    |

## goal
| Statement                                                                |
|--------------------------------------------------------------------------|
| (M0 * exp (L v)) / (∑w∈V. M0 * exp (L w)) = exp (L v) / (∑w∈V. exp (L w)) |

## proof
| Id | Claim                                          | By                | Using  | Method                                   | Status |
|----|------------------------------------------------|-------------------|--------|------------------------------------------|--------|
| s1 | (∑w∈V. M0 * exp (L w)) = M0 * (∑w∈V. exp (L w)) | pull base out     | —      | (simp add: sum_distrib_left)             | method |
| s2 | M0 ≠ 0                                          | base is positive  | M0pos  | (metis less_irrefl)                      | method |
| s3 | (M0 * exp (L v)) / (∑w∈V. M0 * exp (L w)) = exp (L v) / (∑w∈V. exp (L w)) | cancel → softmax | s1, s2 | (simp add: mult_divide_mult_cancel_left) | method |
```

`i-orca compile … --target isar` lowers each row to an Isar `have`, `## context`
rows to named assumptions, and holes to `sorry` — a self-contained `.thy` the
Isabelle kernel checks.

## Pipeline

```
generate .i.orca.md → verify (cheap, no Isabelle) → refine until valid
   → compile isar → check (warm Isabelle session)
   → for each open obligation: hammer → on fail, refine that step
   → repeat until formal_fraction_real → 1.0
   → exports: tex (always) | lean4 (best-effort skeleton)
```

Every leg is a structured MCP call with structured feedback (stable error
codes), so an agent can drive the whole loop. See [`docs/mcp.md`](docs/mcp.md).

## The three backends (asymmetric by design)

- **Isar — primary, checkable.** Lowers to a real `.thy`; holes → `sorry`;
  Isabelle elaborates and kernel-checks; Sledgehammer discharges holes.
- **TeX — secondary, always emits**, even for an incomplete proof.
- **Lean 4 — secondary, structure-only skeleton.** Carries the DAG and
  propositions; methods do not transfer. Never a Lean proof.

## Worked corpus: the fieldrun theorems

[`examples/fieldrun/fieldrun.i.orca.md`](examples/fieldrun/fieldrun.i.orca.md)
formalises all ten theorems/propositions of the paper *"What a Transformer
Retrieves and What It Computes"* (`../fieldrun/paper`). **All ten are fully
kernel-proved** with Isabelle2025-2: the combined `Fieldrun.thy` builds clean
(exit 0) with **zero `sorry`** — every step is a concrete method the kernel
accepts. Formalising the open half of Theorem 3 surfaced a definitional crux (μ_t=0
"no singleton" vs irreducibility "no sufficient sub-conjunction") with a
kernel-checked witness; see the research note and the companion
[`separation/Separation.thy`](examples/fieldrun/separation/Separation.thy).
Generated `.thy`/`.tex`/`.lean` artifacts and the kernel-check report are in
[`examples/fieldrun/artifacts/`](examples/fieldrun/artifacts/) — see
[`examples/fieldrun/RESULTS.md`](examples/fieldrun/RESULTS.md).

## Example corpora

The `examples/` tree holds ten kernel-checked corpora — four formalising this
workspace's own research, plus six in a **"canonical proofs from other authors"** track:

| Corpus | What it formalises | Kernel status |
|--------|--------------------|---------------|
| [`fieldrun/`](examples/fieldrun) | all ten theorems of the fieldrun paper *"What a Transformer Retrieves and What It Computes"* | 10/10, zero `sorry` |
| [`complexity/`](examples/complexity) | non-paper extensions (minimal deciders, decomposition, the per-input pipeline bridge) | zero `sorry` |
| [`provable_opt/`](examples/provable_opt) | fieldrun **PROVABLE_OPT** formal arm — PO-T1 (`T_P`-equivalence for the lossless demand/dead-stratum `lastpos` transform) **and** PO-T3 (margin-certified decode invariance + a **tight** boundary), the **kernel bridge** (rule-level Datalog: the syntactic demand-closure check fieldrun's tool runs ⟹ the semantic one), and a **verified executable decision procedure** (`echeck`, faithful + `eval`-run + `export_code`) shrinking the trusted base to just the parser | 18/18 surfaced + 4 compiled surfaces, zero `sorry` |
| [`provenance/`](examples/provenance) | the syntactic-vs-statistical attribution dichotomy + two-scenario explain analysis | 11/11, zero `sorry` |
| [`watermark/`](examples/watermark) | **canonical / other authors:** the math core of Aaronson's LLM watermark — distortion-free sampling + key-based detectability | 12/12, zero `sorry` |
| [`tropical/`](examples/tropical) | **canonical / other authors:** the tropical-geometry view of ReLU networks — Zhang–Naitzat–Lim (ICML 2018), with Pachter–Sturmfels and Maragos et al. | 20/20, zero `sorry` |
| [`superposition/`](examples/superposition) | **canonical / other authors:** the geometric core of Anthropic's "Toy Models of Superposition" — interference, orthogonal capacity, and the Welch bound | 10/10, zero `sorry` |
| [`jl/`](examples/jl) | **canonical / other authors:** the Johnson–Lindenstrauss random-projection lemma — unbiased projection, `O(log n/ε²)` dimension, probabilistic-method existence | 7/7, zero `sorry` |
| [`turboquant/`](examples/turboquant) | **canonical / other authors:** the distortion-rate structure of Google's TurboQuant (arXiv:2504.19874) — near-optimal `≈2.7×` ratio, geometric `1/4ᵇ` rate, unbiased inner products | 11/11, zero `sorry` |
| [`bitnet/`](examples/bitnet) | **canonical / other authors:** ternary-weight LLMs (BitNet b1.58, arXiv:2402.17764) — multiplication-free matmul, the `≈1.58`-bit width, and a *lossless* ternary realization by balanced-ternary expansion | 9/9, zero `sorry` |

Each corpus ships its own `PROPOSAL.md` / `README.md` / `RESULTS.md` and follows the
same substrate-`.thy` + thin-`.i.orca.md`-surface pattern.

## Docs

- [`SPEC.md`](SPEC.md) — full design + honest reckonings
- [`AGENTS.md`](AGENTS.md) — agent orientation
- [`docs/grammar.md`](docs/grammar.md) — surface syntax
- [`docs/mcp.md`](docs/mcp.md) — the MCP tool surface
- [`docs/verifier-backend-metrics.md`](docs/verifier-backend-metrics.md) — the
  static-vs-kernel metric

## License

Apache-2.0.
