# KreinPIC — verification status

A thought experiment: PIC's frame/decode split under an indefinite (Krein) inner product, plus the
bottom-K (min-plus) dual and the frame-only "Scheme A" preconditioner. Companion spec:
`pic/spec/PIC_SPEC.md`. See [`PROPOSAL.md`](PROPOSAL.md) for the tag ledger.

## Layer 1 — structural skeleton (no Isabelle)

```
$ .venv/bin/i-orca verify examples/pic_krein/pic_krein.i.orca.md
```
All **39** surface theorems VALID, `formal_fraction_static = 1.000`, 0 frontier holes.

## Layer 2 — kernel check of the substrate (the load-bearing math)

```
$ isabelle build -d examples/pic_krein -o quick_and_dirty KreinPIC
Running KreinPIC ...
Finished KreinPIC (0:00:02 elapsed time)
```

`Finished KreinPIC`, exit 0, **zero `sorry`** across all seven theories
(`KreinDecode.thy`, `KreinWelch.thy`, `KreinBottomK.thy`, `KreinPrecond.thy`, `KreinTernary.thy`,
`PIC_Quant.thy`, `PIC_Prune.thy`; Isabelle2025-2, parent `HOL-Analysis`). The `.thy` files are the hand-authored, kernel-checked substrate; the `.i.orca.md` is
the thin i-orca surface, each theorem discharged by `(rule <lemma>)`.

## The seven theories

| theory | what it establishes |
|--------|---------------------|
| `KreinDecode` | decode side is metric-free (definitization); capacity survives in the majorant |
| `KreinWelch`  | frame side feels the signature: timelike units, null token, trace = signature, Welch driver vanishes, indefinite ball unbounded |
| `KreinBottomK`| the bottom-K (min-plus) head/tail certificate — dual of `tropical/HeadTail.thy` — and bottom-K = top-K of the negated frame |
| `KreinPrecond`| Scheme A: an indefinite frame-update preconditioner is no real reparametrization of SGD, and the flow `U̇ = −J∇L` is *not* a descent flow (genuinely new, saddle-seeking dynamics). Recipes in [`SCHEME_A.md`](SCHEME_A.md); learned `J` in [`LEARNED_J.md`](LEARNED_J.md) |
| `KreinTernary`| bridge to the `bitnet` corpus: a ternary signature is a tripotent degenerate fundamental symmetry (`Js³=Js`), and the provable value-system differences (integer/ternary robustness floor vs float; finite `3^d` frame space). See [`TERNARY.md`](TERNARY.md) |
| `PIC_Quant`   | within-tolerance lossless compression for **any** value system (float/int/ternary) and **any** metric: the margin certificate + a Cauchy–Schwarz quantization bound ⇒ quantize the frame to `ε`-cells with `2ρε < margin` and the decode is preserved exactly. See [`QUANT.md`](QUANT.md) |
| `PIC_Prune`   | the source-side **pruning** certificate: dropping sources whose summed incidence stays under half the margin preserves the decode, with a `β`-budget form the greedy/knapsack algorithms gate on. See [`PRUNE.md`](PRUNE.md) |

## What is proved vs. what is open

**Proved (kernel, 40 theorems):** decode definitization, form symmetry, majorant escape hatch,
capacity-survives-in-majorant; the signature phenomena (timelike split, null token, trace = signature,
Welch-driver vanishing, indefinite-ball unboundedness); the full bottom-K dual certificate (partition,
co-head certifies, argmin-in-co-head, tail residue), the negation duality (`bottomk = −(top-k over −U)`);
and Scheme A's non-triviality (Gram forms are PSD ⇒ an indefinite preconditioner is no reparametrized SGD),
its dynamical companion (a PSD preconditioner descends, but an indefinite one has a strict ascent
direction — the J-flow is not a descent flow), the **isotropic instability** (the Scheme-A update
multiplies a timelike axis by `1+η` — geometric divergence — and `−J` has eigenvalue `+1` on the whole
timelike eigenspace), the **learned-J dichotomy** (descends-for-all ⟺ PSD), and the **signature
parametrization** (a rigid signature is an involution). See [`SCHEME_A.md`](SCHEME_A.md) and
[`LEARNED_J.md`](LEARNED_J.md). The general SPD-Hessian eigenvalue count (`q` positive eigenvalues of
`−JH` by Sylvester) reduces to the isotropic core and is stated, not formalized (needs spectral theory).
The **ternary / bitnet bridge** adds the tripotent law (`s³=s ⟹ Js³=Js`), `Js² = `support-projection,
and the **value-system differences**: the discrete robustness floor (integer/ternary strict win survives
any `δ<½`; float has no floor), the finite ternary frame space (`3^d`), the **lossless conversion by
adding dimensions** (`⟨w,x⟩ = Σ_k 3^k ⟨t_{·k},x⟩` — int/fp → ternary at a `K`-fold width blow-up,
`ternary_widen_lossless`), and the **lossless storage compression** (5 trits/byte, `3^5 ≤ 2^8`,
`ternary_byte_packing`). See [`TERNARY.md`](TERNARY.md). Finally **within-tolerance lossless
compression** (`PIC_Quant.thy`, value-system- and metric-agnostic): the self-contained margin
certificate (`margin_certified`), the Cauchy–Schwarz quantization bound (`frame_quant_logit_bound`,
logit drift ≤ `ρε`), and their composition (`quant_decode_preserved`) — quantize the frame to `ε`-cells
on any grid and the decode is preserved exactly when `2ρε < margin`; the `ε`-covering number sets the
bit rate. See [`QUANT.md`](QUANT.md). And the source-side **pruning certificate** (`PIC_Prune.thy`):
pruning perturbs each logit by the dropped incidence (`prune_logit_delta`), bounded by a per-source
`β`-budget (`prune_dropped_le_budget`, monotone — `prune_budget_mono`), so dropping `P` with
`2·Σ_{j∈P}β_j < margin` preserves the decode (`prune_decode_preserved` / `prune_budget_decode_preserved`)
— the certificate the greedy / knapsack / iterative pruning algorithms gate on, with quantization + prune
+ rewrite mixable under one triangle-budget. See [`PRUNE.md`](PRUNE.md). (Kernel count 40 = 39 surfaced + `card_ternary_frame`, proved in
`KreinTernary.thy` but not surfaced — i-orca verify mis-tokenizes its `Pi⇩E` goal, a surface-parser
limit, not a math gap.)

**Open / not claimed:** achievability of sub-Welch coherence with `n>d` indefinite units; an
indefinite-ball capacity bound; that an indefinite preconditioner *helps* (pil §6.1: no frame knob yet
beats plain SGD); any transformer measurement (QK signature; negative-subspace dimension); the
architecture/decoding/loss designs and the quantum-informational analogy (structural conjecture, no
"Krein quantum-information" literature claimed — it may not exist).

## Note for the spec

The takeaway for `pic/spec/PIC_SPEC.md` is independent of Krein: **positive-definiteness is a silent,
load-bearing hypothesis** in §5.1 (compact ball) and §5.3 (PSD Gram). Annotating each §5 theorem
*metric-free vs metric-dependent* — the third axis this corpus surfaces alongside frame/decode (§4) and
monomial/variable (§5.0) — would sharpen the spec whether or not the Krein variant is pursued.
