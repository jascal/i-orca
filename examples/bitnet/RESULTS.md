# BitNet corpus — verification results

Status of the `examples/bitnet/` corpus under **Isabelle2025-2**. Two layers (SPEC §2, §8):
the cheap structural skeleton (`i-orca verify`, no Isabelle) and the real kernel check
(`isabelle build`).

## Commands

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/bitnet/bitnet.i.orca.md
#   -> all 9 theorems VALID, formal_fraction_static = 1.000, 0 frontier holes

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/bitnet -o quick_and_dirty BitNet
#   -> Finished BitNet, exit 0, zero sorry

# Layer 2 — kernel check of the SURFACE (compile, add to ROOT, build in-session)
i-orca compile examples/bitnet/bitnet.i.orca.md --target isar \
  --document --theory BitNetSurface --out examples/bitnet/BitNetSurface.thy
#   append "BitNetSurface" to ROOT, rebuild  -> exit 0
#   (BitNetSurface.thy is a regenerable artifact; not committed)
```

## Outcome

| Layer | Tool | Result |
|-------|------|--------|
| Skeleton | `i-orca verify` | 9/9 VALID, `formal_fraction_static = 1.000` |
| Substrate | `isabelle build` (`BitNet` session) | exit 0, **zero `sorry`** |
| Surface | `isabelle build` (compiled `BitNetSurface` in-session) | exit 0 — every `(rule …)` non-vacuous |

No `sorry`, `oops`, or `sledgehammer` placeholders remain in the substrate — every step is a
concrete method the kernel accepts. The corpus needs no `HOL-Analysis` (the session parent
is plain `HOL`; everything is in `Complex_Main`).

## Theorems (surface → kernel-checked substrate lemma)

**Multiplication-free matmul** (`Ternary.thy`)
- `TernaryProductIsMultiplication` → `tprod_is_mult`
- `TernaryDotIsSignedSum` → `ternary_dot_signed_sum`

**Absmean quantizer** (`Ternary.thy`)
- `QuantizerIsTernary` → `roundclip_ternary`
- `QuantizerNotInjective` → `roundclip_not_injective` (per-weight ternarization is lossy)

**Lossless-by-expansion** (`BalancedTernary.thy`, `Lossless.thy`)
- `BalancedTernaryExists` → `balanced_ternary_exists`
- `LosslessRealization` → `lossless_realization`
- `LosslessWeight` → `lossless_weight`

**1.58 bits** (`BitWidth.thy`)
- `TernaryBitWidth` → `log2_3_approx` (`1.5 < log₂3 < 1.6`)
- `FiveTritsPerByte` → `five_trits_per_byte` (`3⁵ ≤ 2⁸`)

## Notes

- `balanced_ternary_exists` is proved from scratch by strong induction on `nat ¦n¦`, using
  `presburger` for the integer div/mod facts (the balanced residue and the termination
  measure `¦(n+1) div 3¦ < ¦n¦`).
- `log2_3_approx` (`1.5 < log₂3 < 1.6`) is a genuine numeric bound: it reduces via
  `less_log_iff` / `log_less_iff` and `powr_realpow` to `2³ < 3²` and `3⁵ < 2⁸`. The true
  value is ≈ 1.585; a tighter bracket would need much larger integer powers.
- Three surface goals (`BalancedTernaryExists`, `LosslessRealization`, `LosslessWeight`)
  carry an explicit `::int` annotation: they use only generic ring/sum operations with no
  int-typed constant to pin the type, so without it `(rule …)` would not unify with the
  `int`-fixed lemma (same gotcha as goals in the `watermark` and `jl` corpora). The other
  six are pinned by `tprod`, `roundclip`, `log`, or a `(3::nat)` literal.
- The standalone `i-orca check` cannot load this project-local session (it builds each
  theorem under a plain HOL parent), so the surface is kernel-checked via `isabelle build`
  rather than the batch backend — an import-resolution limit, not a math failure.
- Scope and the lossless-vs-Datalog discussion (lossless = behavioural exactness by
  expansion; the Datalog rewriting is the meta narrative; minimising the expansion is the
  hard optimisation) are recorded in [`PROPOSAL.md`](PROPOSAL.md).
