# Toy Models of Superposition — proposal

The third entry in i-orca's **"canonical proofs from other authors"** track (after
[`../watermark`](../watermark), Aaronson's LLM watermark, and
[`../tropical`](../tropical), the tropical geometry of ReLU networks): a kernel-checked
formalisation of the geometric core of Anthropic's **"Toy Models of Superposition"**.

**Source.** Elhage, Hume, Olsson, Schiefer, Henighan, Kravec, Hatfield-Dodds, Lasenby,
Drain, Chen, Grosse, McCandlish, Kaplan, Amodei, Wattenberg & Olah, *"Toy Models of
Superposition"*, Transformer Circuits Thread / Anthropic, 2022.

## The idea

A model embeds `n` features into `m` dimensions via a matrix `W` whose columns `W_i` are
the feature directions, and reconstructs an input by `x' = W^T W x`. The Gram matrix
`W^T W` carries the feature norms on its diagonal and the pairwise **interference**
`⟨W_i, W_j⟩` off it. **Superposition** — representing `n > m` features — is the regime
where features must share directions, so they interfere; the paper studies when a model
chooses to do so (when features are sparse) and the geometry it settles into. The
mathematical backbone is a packing fact: you cannot fit many near-orthogonal directions
into few dimensions, and the residual interference is bounded below by the **Welch
bound**.

## What is formalised (and the formal-vs-meta split)

The Isabelle theorems are **honest, narrow, kernel-checked cores** — the linear-algebra
geometry of interference, proved from scratch over a finite coordinate set (no matrix or
inner-product-space library). Three theories, ten surfaced theorems:

| # | i-orca theorem | Isabelle lemma | Proves (formal) | Supports (meta) |
|---|----------------|----------------|------------------|------------------|
| 1 | InnerProductSymmetric | `ip_commute` | `⟨x,y⟩ = ⟨y,x⟩` | the Gram matrix is symmetric |
| 2 | ReconstructionErrorIsInterference | `recon_error_eq_interference` | a unit feature's reconstruction error `= Σ_{l≠i} ⟨W_l,W_i⟩²` | geometry **is** the loss the model minimises |
| 3 | OrthogonalPerfectRecovery | `orthogonal_perfect_recovery'` | orthogonal features reconstruct with zero error | the dense, no-superposition regime is lossless |
| 4 | WelchSumOfSquares | `welch_sos` | `Σ_{i,j} ⟨v_i,v_j⟩² ≥ (Σ_i ‖v_i‖²)² / m` | **the jewel** — the source of every bound below |
| 5 | OrthogonalCapacity | `orth_capacity'` | orthonormal features number `≤ m` | without superposition only `m` features fit |
| 6 | SuperpositionForcesInterference | `superposition_forces_interference'` | `n > m` ⇒ some `⟨v_i,v_j⟩ ≠ 0` | representing `> m` features **requires** interference |
| 7 | WelchBound | `welch_offdiag'` | total interference `≥ n(n−m)/m` | the quantitative cost of overpacking |
| 8 | AntipodalInterference | `antipodal_interference` | `⟨v_0,v_1⟩ = −1` for the antipodal pair | the simplest superposition geometry |
| 9 | AntipodalIsSuperposition | `antipodal_is_superposition` | two features in one dimension interfere | a concrete witness of theorem 6 |
| 10 | AntipodalAchievesWelch | `antipodal_achieves_welch` | the antipodal pair meets the Welch bound `= 2` with equality | the **optimal** packing of two features into one dimension |

The **meta** column is deliberately not claimed as proven. E.g. theorem 4 is the exact
Welch sum-of-squares inequality; it does not, by itself, model a trained network's
weight matrix or its loss landscape.

## Honest reckonings

- **The Welch bound is genuine and from scratch.** `welch_sos` is proved directly —
  expand each inner product over the coordinate set, swap the feature and coordinate
  sums to recognise the Gram matrix `M b b' = Σ_i v_i[b] v_i[b']`, drop the non-negative
  off-diagonal Gram entries, and apply Cauchy–Schwarz to the diagonal. No matrix,
  eigenvalue, or inner-product-space library is used; vectors are functions over a
  finite coordinate set `K` with `m = card K`.
- **Linear reconstruction model (thm 2, 3).** The reconstruction map is the *linear*
  `x ↦ W^T W x`. The paper's model has a ReLU and a bias (`x' = ReLU(W^T W x + b)`); the
  ReLU is what lets sparse features tolerate interference. Formalising the ReLU model
  and the sparsity-weighted expected loss is the stated lift, not done here.
- **Phase transitions and specific geometries not attempted.** The paper's headline
  empirical findings — the sparsity-driven *phase transitions* in how many features get
  represented, and the specific polytope geometries (antipodal pairs, triangles,
  pentagons, tetrahedra) features organise into — are optimisation phenomena of trained
  toy models. We prove the *static* capacity/interference bounds that explain *why*
  those geometries are forced; we kernel-check only the antipodal pair (thm 8–10).
- **Feature dimensionality.** The paper's fractional "feature dimensionality"
  `D_i = ‖W_i‖² / Σ_j ⟨Ŵ_i, W_j⟩²` and its budget are not formalised here.

## Milestones / open targets

1. **(done)** The ten-theorem development above — all kernel-checked under
   Isabelle2025-2 (`isabelle build -D examples/superposition Superposition`, exit 0,
   zero `sorry`). See [`RESULTS.md`](RESULTS.md).
2. The ReLU reconstruction model with a bias, and the sparsity-weighted expected loss,
   so "sparse features tolerate interference" becomes a theorem.
3. The Welch bound in its standard max-coherence form
   `max_{i≠j} ⟨v_i,v_j⟩² ≥ (n−m)/(m(n−1))` (the off-diagonal-sum form is theorem 7).
4. More superposition geometries (the regular simplex / equiangular tight frames that
   achieve the Welch bound at larger `n`).
5. Connect the feature directions `W_i` to the SAE dictionary geometry modelled in
   `polygram`, so "superposition" here is the same object that stack measures.
