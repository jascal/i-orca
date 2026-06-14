# The Verifier–Backend Gap: a cross-family coverage & agreement metric

> **Status:** design proposal, drafted 2026-06-04. Native to i-orca; retrofits onto
> `orca-lang`, `n-orca`, `q-orca-lang`. Captures the metric so the idea is not lost.

## Thesis

Every Orca dialect has the same shape: **a cheap static checker standing in front of an
expensive ground-truth backend.** i-orca's `formal_fraction` is not special to proofs — it is
one instance of a metric every dialect can carry. The gap between "statically verified" and
"actually realized/accepted by the backend" splits into **two distinct numbers**, and keeping
them distinct is the whole point.

- **(a) Coverage** — of the specs the static verifier passes, what fraction does the backend
  **faithfully realize** (vs stub, drop, or refuse)? Measures the expressiveness gap between
  DSL+verifier and backend. The direct `formal_fraction` analog.
- **(b) Agreement** — when the cheap static verdict says "valid," does the expensive backend's
  **ground truth agree**? Measures whether the static check is *sound* — i.e. whether
  verify-before-execute is real.

i-orca already names both halves: `formal_fraction_static` (coverage estimate, no Isabelle)
and `formal_fraction_real` (agreement-corrected, after `check_proof`).

---

## The one distinction that must not be flattened

For **proofs, the residue the static layer punts is fundamental** — proof validity is
undecidable, so the holes are a permanent epistemic frontier. For **orca/n-orca, the residue is
mostly incidental** — a `MISSING_OP` or an `any-final` parallel region is an unimplemented
lowering (a TODO), not an undecidable obligation. So a low i-orca `formal_fraction` is a real
limit being probed; a low n-orca coverage is just "we haven't written that op emitter yet."

But metric **(b)** restores the parallel, because even a "decidable" verifier is in practice an
**approximation** of backend semantics, and its value scales with how much it approximates:

| Dialect | Static check is… | So agreement (b) is… |
|---------|------------------|----------------------|
| orca structural (reachability/determinism) | near-exact vs the XState graph | trivially high — only catches verifier *bugs* |
| orca `properties.ts` (model checking) | over-approximates — treats every guarded transition as fireable because **action postconditions are opaque** | genuinely informative |
| n-orca shape inference | symbolic dims "opaque but consistent" | informative under *real* execution |
| q-orca Stage 4 (declared entanglement/unitarity) | trusts the Markdown declaration | **highly** informative |
| i-orca proof skeleton | undecidable residue | the entire story |

Rule of thumb: **coverage** dominates where the verifier is near-complete relative to the
backend; **agreement** dominates where the static check is a genuine approximation.

---

## Formal definitions

Fix a corpus `M` of specs (ideally LLM-generated, stratified by size — state count / layer
count / qubit count / proof step count).

### Coverage

For a spec `m` that the static verifier accepts, let `realizable(m)` = the fraction of `m`'s
constructs the backend lowers **faithfully** (not to a stub/placeholder/fallback).

```
coverage = mean over static-valid m in M of realizable(m)
```

Per-dialect `realizable` granularity: per construct (orca transition / parallel region),
per layer (n-orca), per machine-or-gate (q-orca), per proof step (i-orca).

### Agreement

Run each static-valid `m` through the backend oracle `O` (which returns accept/reject and,
where applicable, a semantic ground truth).

```
agreement      = P( O accepts m            | static verifier accepts m )   # 1 − false-negative rate
false_negative = P( O rejects/deadlocks m  | static verifier accepts m )
false_positive = P( O accepts m            | static verifier rejects m )   # verifier over-strictness
```

`agreement` is the operational form of the manifesto's unmeasured claim that verify-before-
execute lowers defect rate. `false_positive` measures whether the verifier is needlessly
rejecting runnable specs.

---

## Per-backend instantiation

### orca-lang → XState / Mermaid / runtimes

- **Coverage:** % of constructs lowerable to *native* XState vs standalone-runtime-only. Turns
  the prose "Known Limitations" (`any-final` sync has no XState equivalent; nested parallel
  disallowed; Mermaid parallel depends on renderer support) into a corpus number.
- **Agreement:** compile static-valid machines to XState, run XState's own validator + execute
  on random event traces; rate of `(static-valid ∧ backend-deadlock/reject)` = verifier
  false-negative rate. Most informative against `properties.ts`, which over-approximates because
  action postconditions are opaque.
- **Runtime parity:** % of `(machine, trace)` where all four runtimes (TS/Py/Go/Rust) produce
  identical state+context trajectories. Turns the `health-check` from pass/fail into a
  differential-agreement rate, and operationalizes the "feature parity across four runtimes"
  claim.

### n-orca → PyTorch

- **Coverage:** runnable fraction = layers with a real op / total = `1 − MISSING_OP rate`. The
  "compiles to an `nn.Module` placeholder" gap, made numeric.
- **Agreement:** compile → instantiate → run a forward pass on a dummy batch; does
  `SHAPE_MISMATCH`-clean static inference ⇒ the real forward actually succeed? Static shape
  algebra vs torch's real shapes — n-orca's exact analog of static-vs-dynamic.

### q-orca-lang → QASM / Qiskit / QuTiP / CUDA-Q

**Already implemented — just not aggregated.** Stage 4 (static: declared entanglement,
`ENTANGLEMENT_WITHOUT_GATE`) vs Stage 4b (dynamic: real QuTiP Schmidt rank / Von Neumann
entropy, `DYNAMIC_NO_ENTANGLEMENT`) **is** the agreement metric — the broken-bell example shows
both verdicts firing. Aggregate it as a declaration-vs-simulation agreement rate over a corpus.

- **QASM coverage:** % emitting real QASM vs falling back — HEA-encoded machines verify and
  produce an analytic Gram but are explicitly *out of scope for QASM emit*, so they are a
  countable coverage hole.
- **Cross-backend agreement:** QuTiP vs CUDA-Q vs cuQuantum Schmidt/entropy "within tolerance"
  is currently *asserted* in the README — measure it.
- **Sim-vs-hardware (aspirational):** QASM on a real device vs simulation — the ultimate
  ground-truth oracle, the q-orca analog of bio-sae being the only substrate on a real
  foundation model.

### i-orca → Isabelle

- **Coverage:** `formal_fraction_static` — fraction of steps with a concrete Isar method vs
  `hammer`/`sorry`/`sketched`.
- **Agreement:** `formal_fraction_real` — fraction of steps Isabelle's kernel accepts; plus
  `sledgehammer_success_rate`. The undecidable case, where agreement *is* the whole story.

---

## The experiment Success Criterion #4 is asking for

The manifesto ranks the language family **#3 — "compelling but unproven-at-its-own-root… the
substrate of trust is, at its root, currently asserted,"** and Success Criterion #4 explicitly
wants *"the orca verifier's value (lower defect rate at growing state count) actually measured,
not assumed."* The agreement metric is that instrument:

```
For each dialect, for N ∈ {small … large} state/layer/qubit/step counts:
  generate K specs with an LLM at size N, TWO arms:
    arm A: raw generation (no verify-refine loop)
    arm B: generate → verify → refine-until-valid → then backend
  measure backend-acceptance / defect rate vs N, for A and B.
Claim under test: (B − A) defect-rate reduction GROWS with N.
```

This is the same move the SAE substrates made for interpretability: replace "the verifier seems
to help" with a number against a ground truth, where the backend (XState's validator, torch's
executor, QuTiP's state vector, Isabelle's kernel) plays the oracle role the substrates' known
factorization plays. It is the measurement that moves **Pillar 1 from asserted to demonstrated.**

---

## Reckonings

1. **Where coverage is the only interesting number** (orca structural): if the verifier is
   correct and complete relative to the backend, agreement is ~100% and only measures verifier
   bugs. Don't dress a near-trivial agreement number as a deep result.
2. **Coverage can be gamed by scope.** "100% coverage" on a corpus that avoids the unsupported
   constructs (parallel regions, HEA, exotic ops) is meaningless. Report the corpus's construct
   distribution alongside the number — the analog of the manifesto's "no silent caps."
3. **Agreement needs an honest oracle.** XState/torch/QuTiP/Isabelle each have their own bugs and
   their own partiality (Sledgehammer timeouts ≠ "false"). A `hammer` timeout is *unknown*, not a
   failure — three-valued accounting (proved / refuted / unknown), not binary, or the i-orca
   numbers will lie the way small samples lied in manifesto Reckoning #6.
4. **The two arms in the §"experiment" must be genuinely matched** (same prompts, same model,
   same budget) or the (B − A) gap measures prompt luck, not the verifier.
