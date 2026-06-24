# KreinPIC — verification status

A thought experiment: PIC's frame/decode split under an indefinite (Krein) inner product, plus the
bottom-K (min-plus) dual and the frame-only "Scheme A" preconditioner. Companion spec:
`pic/spec/PIC_SPEC.md`. See [`PROPOSAL.md`](PROPOSAL.md) for the tag ledger.

## Layer 1 — structural skeleton (no Isabelle)

```
$ .venv/bin/i-orca verify examples/pic_krein/pic_krein.i.orca.md
```
All **23** surface theorems VALID, `formal_fraction_static = 1.000`, 0 frontier holes.

## Layer 2 — kernel check of the substrate (the load-bearing math)

```
$ isabelle build -d examples/pic_krein -o quick_and_dirty KreinPIC
Running KreinPIC ...
Finished KreinPIC (0:00:02 elapsed time)
```

`Finished KreinPIC`, exit 0, **zero `sorry`** across all four theories
(`KreinDecode.thy`, `KreinWelch.thy`, `KreinBottomK.thy`, `KreinPrecond.thy`; Isabelle2025-2, parent
`HOL-Analysis`). The `.thy` files are the hand-authored, kernel-checked substrate; the `.i.orca.md` is
the thin i-orca surface, each theorem discharged by `(rule <lemma>)`.

## The four theories

| theory | what it establishes |
|--------|---------------------|
| `KreinDecode` | decode side is metric-free (definitization); capacity survives in the majorant |
| `KreinWelch`  | frame side feels the signature: timelike units, null token, trace = signature, Welch driver vanishes, indefinite ball unbounded |
| `KreinBottomK`| the bottom-K (min-plus) head/tail certificate — dual of `tropical/HeadTail.thy` — and bottom-K = top-K of the negated frame |
| `KreinPrecond`| Scheme A: an indefinite frame-update preconditioner is no real reparametrization of SGD, and the flow `U̇ = −J∇L` is *not* a descent flow (genuinely new, saddle-seeking dynamics). Training recipe in [`SCHEME_A.md`](SCHEME_A.md) |

## What is proved vs. what is open

**Proved (kernel, 23 theorems):** decode definitization, form symmetry, majorant escape hatch,
capacity-survives-in-majorant; the signature phenomena (timelike split, null token, trace = signature,
Welch-driver vanishing, indefinite-ball unboundedness); the full bottom-K dual certificate (partition,
co-head certifies, argmin-in-co-head, tail residue), the negation duality (`bottomk = −(top-k over −U)`);
and Scheme A's non-triviality (Gram forms are PSD ⇒ an indefinite preconditioner is no reparametrized SGD)
plus its dynamical companion (a PSD preconditioner descends, but an indefinite one has a strict ascent
direction — the J-flow is not a descent flow; see [`SCHEME_A.md`](SCHEME_A.md) for the saddle-seeking
analysis and the min–max / annealing recipe that make it usable).

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
