# BitNet b1.58 / ternary weights — i-orca corpus

A kernel-checked formalisation of the structural math of **ternary-weight LLMs (BitNet
b1.58)** (Ma et al., Microsoft Research, arXiv:2402.17764, 2024) — the sixth entry in
i-orca's **"canonical proofs from other authors"** track — built around the question
*can a finite-precision network be transformed into a ternary one losslessly?*

> ⚠️ As everywhere in i-orca, a green `i-orca verify` certifies only that the proof
> *skeleton* is well-formed. Truth is the kernel's: every theorem here is discharged by
> `(rule <lemma>)` against a hand-authored Isabelle lemma, and the whole `BitNet` session
> builds under Isabelle2025-2 with **zero `sorry`**.

## The idea in one line

Ternary weights `{−1,0,1}` (≈ `log₂3 ≈ 1.58` bits each) make the matmul a **signed sum**
(no multiplies); per-weight ternarization is **lossy**, but a finite-precision layer has an
**exact ternary realization by balanced-ternary expansion**. See [`PROPOSAL.md`](PROPOSAL.md)
for the full lossless-vs-Datalog discussion.

## Layout

| File | Role |
|------|------|
| [`Ternary.thy`](Ternary.thy) | the multiplication-free ternary matmul (a ternary dot product is a signed sum), and the absmean RoundClip quantizer (maps into `{−1,0,1}`; non-injective ⇒ per-weight ternarization is lossy) |
| [`BalancedTernary.thy`](BalancedTernary.thy) | every integer is a balanced-ternary combination `Σⱼ tⱼ·3ʲ`, `tⱼ ∈ {−1,0,1}` (the lossless-by-expansion crux, proved from scratch) |
| [`Lossless.thy`](Lossless.thy) | the lossless ternary realization: an integer-weight layer's exact output is a power-of-3 weighted sum of ternary matmuls |
| [`BitWidth.thy`](BitWidth.thy) | the "1.58 bits": `1.5 < log₂3 < 1.6`, and `3⁵ ≤ 2⁸` (five trits per byte) |
| [`ROOT`](ROOT) | Isabelle session `BitNet` (parent `HOL`) |
| [`bitnet.i.orca.md`](bitnet.i.orca.md) | the i-orca surface: 9 theorems, each `(rule <lemma>)` |
| [`PROPOSAL.md`](PROPOSAL.md) | the source, the lossless/Datalog question, the formal-vs-meta table, honest reckonings |
| [`RESULTS.md`](RESULTS.md) | verification status and commands |

## Verify

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/bitnet/bitnet.i.orca.md
#   -> all 9 theorems VALID, formal_fraction_static = 1.000

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/bitnet -o quick_and_dirty BitNet
#   -> Finished BitNet, exit 0, zero sorry
```

To also kernel-check the **surface**, compile it into the session and rebuild:

```bash
i-orca compile examples/bitnet/bitnet.i.orca.md --target isar \
  --document --theory BitNetSurface --out examples/bitnet/BitNetSurface.thy
# append "BitNetSurface" to ROOT, rebuild -> exit 0 (every (rule ...) non-vacuous)
# BitNetSurface.thy is a regenerable artifact; not committed.
```

The standalone `i-orca check` builds each theorem under a plain HOL parent and cannot load
this project-local session — an import-resolution limit, not a math failure (same caveat as
the other corpora).

## What it proves (and what it doesn't)

Nine kernel-checked cores: the multiplication-free ternary matmul, the absmean quantizer
(and its non-injectivity ⇒ per-weight ternarization is lossy), the balanced-ternary
expansion and the **lossless ternary realization** of a finite-precision layer, and the
≈1.58-bit width — see the table in [`PROPOSAL.md`](PROPOSAL.md). The theorems are honest
about scope: "lossless" means *behavioural exactness for finite-precision weights by
expansion* (not a same-size net, and not recovery of the original real weights — which is
impossible). The Datalog encoding itself is the meta narrative; what is kernel-checked is
the algebra it rests on.
