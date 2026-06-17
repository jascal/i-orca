<!--
  i-orca surface for ANTHROPIC'S "TOY MODELS OF SUPERPOSITION" -- the third entry in
  i-orca's "canonical proofs from other authors" track (after ../watermark/, Aaronson's
  LLM watermark, and ../tropical/, the tropical geometry of ReLU networks).

  Source: Elhage, Hume, Olsson, ... Olah, "Toy Models of Superposition", Transformer
  Circuits Thread / Anthropic, 2022. A model embeds n features into m dimensions via a
  matrix W whose columns are the feature directions; it reconstructs by x' = W^T W x.
  Off-diagonal Gram entries <W_i, W_j> are INTERFERENCE. Superposition -- representing
  n > m features -- is the regime where features must share directions and interfere.

  We formalise the geometric core: the reconstruction loss of a single active feature
  IS its total interference; orthogonal features (the dense, no-superposition regime)
  cost nothing but cap the feature count at m; and packing n > m features forces
  interference bounded below by the WELCH BOUND -- proved from scratch via an elementary
  sum-of-squares inequality.

  As in ../watermark/, ../tropical/ and ../provenance/, the heavy content lives in the
  kernel-checked Isabelle theories here (Superposition.thy, Welch.thy, Examples.thy);
  each theorem below is STATED in i-orca form and discharged by `(rule <lemma>)`. We do
  NOT list the cited lemma in `## context` (the compiler lowers context rows to local
  `assumes`, which would make the cite a vacuous P => P).

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID, fraction 1.000.
    - Kernel check: built INSIDE the `Superposition` session (this directory's ROOT):
          ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/superposition \
            -o quick_and_dirty Superposition
      The standalone `i-orca check` builds each theorem under a plain HOL parent and
      cannot load this project-local session (same caveat as the other corpora).

  Map to the paper:
    INTERFERENCE = LOSS    -> InnerProductSymmetric, ReconstructionErrorIsInterference,
                             OrthogonalPerfectRecovery
    THE WELCH BOUND        -> WelchSumOfSquares, OrthogonalCapacity,
      (cost of packing)       SuperpositionForcesInterference, WelchBound
    WORKED EXAMPLE         -> AntipodalInterference, AntipodalIsSuperposition,
      (antipodal pair)        AntipodalAchievesWelch
-->

# theorem InnerProductSymmetric
> The inner product over the coordinate set is symmetric: `<x,y> = <y,x>`. The Gram matrix W^T W is symmetric, so interference is mutual. Cites `ip_commute`.

## imports
| Theory        |
|---------------|
| Superposition |

## goal
| Statement |
|-----------|
| ip K x y = ip K y x |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ip K x y = ip K y x | multiplication of coordinates commutes | — | (rule ip_commute) | method |


# theorem ReconstructionErrorIsInterference
> Geometry becomes loss. Reconstructing the one-hot input for a single UNIT feature i under x ↦ W^T W x incurs squared error exactly equal to its total squared interference with the other features. Cites `recon_error_eq_interference`.

## imports
| Theory        |
|---------------|
| Superposition |

## goal
| Statement |
|-----------|
| finite I ⟹ i ∈ I ⟹ ip K (W i) (W i) = 1 ⟹ recon_error K W I i = (∑l∈I - {i}. (ip K (W l) (W i))\<^sup>2) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ i ∈ I ⟹ ip K (W i) (W i) = 1 ⟹ recon_error K W I i = (∑l∈I - {i}. (ip K (W l) (W i))\<^sup>2) | the diagonal target is met exactly; the residual is the interference with the rest | — | (rule recon_error_eq_interference) | method |


# theorem OrthogonalPerfectRecovery
> The dense, no-superposition regime: orthogonal features have zero interference, so a single active feature reconstructs with zero error. Cites `orthogonal_perfect_recovery'`.

## imports
| Theory        |
|---------------|
| Superposition |

## goal
| Statement |
|-----------|
| finite I ⟹ i ∈ I ⟹ ip K (W i) (W i) = 1 ⟹ (∀l∈I. l ≠ i ⟶ ip K (W l) (W i) = 0) ⟹ recon_error K W I i = 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ i ∈ I ⟹ ip K (W i) (W i) = 1 ⟹ (∀l∈I. l ≠ i ⟶ ip K (W l) (W i) = 0) ⟹ recon_error K W I i = 0 | every interference term is zero, so the error sum is zero | — | (rule orthogonal_perfect_recovery') | method |


# theorem WelchSumOfSquares
> The mathematical jewel, proved from scratch (Cauchy–Schwarz on the Gram diagonal, no matrix library). The sum of squared inner products is bounded below by the squared total norm over the embedding dimension `m = card K`. Everything about the cost of superposition flows from this one inequality. Cites `welch_sos`.

## imports
| Theory |
|--------|
| Welch  |

## goal
| Statement |
|-----------|
| finite I ⟹ finite K ⟹ (∑i∈I. ∑j∈I. (ip K (v i) (v j))\<^sup>2) ≥ (∑i∈I. ip K (v i) (v i))\<^sup>2 / real (card K) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ finite K ⟹ (∑i∈I. ∑j∈I. (ip K (v i) (v j))\<^sup>2) ≥ (∑i∈I. ip K (v i) (v i))\<^sup>2 / real (card K) | recognise the Gram matrix, drop the non-negative off-diagonal, Cauchy–Schwarz the diagonal | — | (rule welch_sos) | method |


# theorem OrthogonalCapacity
> Without superposition you fit only `m` features. Pairwise-orthogonal unit features number at most the embedding dimension `card K` — the dense-regime capacity. Cites `orth_capacity'`.

## imports
| Theory |
|--------|
| Welch  |

## goal
| Statement |
|-----------|
| finite I ⟹ finite K ⟹ (∀i∈I. ip K (v i) (v i) = 1) ⟹ (∀i∈I. ∀j∈I. i ≠ j ⟶ ip K (v i) (v j) = 0) ⟹ card I ≤ card K |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ finite K ⟹ (∀i∈I. ip K (v i) (v i) = 1) ⟹ (∀i∈I. ∀j∈I. i ≠ j ⟶ ip K (v i) (v j) = 0) ⟹ card I ≤ card K | orthogonal unit vectors make the Welch inequality read n ≥ n²/m, forcing n ≤ m | — | (rule orth_capacity') | method |


# theorem SuperpositionForcesInterference
> The defining fact of superposition: representing more features than dimensions is impossible without interference. If `card K < card I` (n > m) then some pair of features has non-zero inner product. Cites `superposition_forces_interference'`.

## imports
| Theory |
|--------|
| Welch  |

## goal
| Statement |
|-----------|
| finite I ⟹ finite K ⟹ (∀i∈I. ip K (v i) (v i) = 1) ⟹ card K < card I ⟹ (∃i∈I. ∃j∈I. i ≠ j ∧ ip K (v i) (v j) ≠ 0) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ finite K ⟹ (∀i∈I. ip K (v i) (v i) = 1) ⟹ card K < card I ⟹ (∃i∈I. ∃j∈I. i ≠ j ∧ ip K (v i) (v j) ≠ 0) | if all features were orthogonal the capacity bound n ≤ m would fail | — | (rule superposition_forces_interference') | method |


# theorem WelchBound
> The Welch bound: total off-diagonal interference is at least `n(n−m)/m`, strictly positive exactly when `n > m`. This quantifies the unavoidable cost of overpacking — interference that grows as more features are crammed into the same dimensions. Cites `welch_offdiag'`.

## imports
| Theory |
|--------|
| Welch  |

## goal
| Statement |
|-----------|
| finite I ⟹ finite K ⟹ 0 < card K ⟹ (∀i∈I. ip K (v i) (v i) = 1) ⟹ (∑i∈I. ∑j∈I - {i}. (ip K (v i) (v j))\<^sup>2) ≥ real (card I) * (real (card I) - real (card K)) / real (card K) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ finite K ⟹ 0 < card K ⟹ (∀i∈I. ip K (v i) (v i) = 1) ⟹ (∑i∈I. ∑j∈I - {i}. (ip K (v i) (v j))\<^sup>2) ≥ real (card I) * (real (card I) - real (card K)) / real (card K) | split the diagonal off the Welch sum-of-squares bound | — | (rule welch_offdiag') | method |


# theorem AntipodalInterference
> Worked example. Two features packed into one dimension as the antipodal unit vectors +1 and −1 interfere maximally: `<v₀, v₁> = −1`. Cites `antipodal_interference`.

## imports
| Theory   |
|----------|
| Examples |

## goal
| Statement |
|-----------|
| ip {0::nat} (antipodal 0) (antipodal 1) = - 1 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ip {0::nat} (antipodal 0) (antipodal 1) = - 1 | the two antipodal directions have inner product minus one | — | (rule antipodal_interference) | method |


# theorem AntipodalIsSuperposition
> The antipodal pair is genuine superposition: two features in one dimension, with non-zero interference — a concrete instance of the forcing theorem. Cites `antipodal_is_superposition`.

## imports
| Theory   |
|----------|
| Examples |

## goal
| Statement |
|-----------|
| ∃i∈{0,1::nat}. ∃j∈{0,1}. i ≠ j ∧ ip {0::nat} (antipodal i) (antipodal j) ≠ 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∃i∈{0,1::nat}. ∃j∈{0,1}. i ≠ j ∧ ip {0::nat} (antipodal i) (antipodal j) ≠ 0 | the two antipodal features interfere, witnessing superposition in one dimension | — | (rule antipodal_is_superposition) | method |


# theorem AntipodalAchievesWelch
> The antipodal pair is OPTIMAL: it achieves the Welch off-diagonal bound `n(n−m)/m = 2` with equality — the best possible packing of two features into one dimension, exactly the configuration the paper finds for sparse antipodal pairs. Cites `antipodal_achieves_welch`.

## imports
| Theory   |
|----------|
| Examples |

## goal
| Statement |
|-----------|
| (∑i∈{0,1::nat}. ∑j∈{0,1} - {i}. (ip {0::nat} (antipodal i) (antipodal j))\<^sup>2) = real (card {0,1::nat}) * (real (card {0,1::nat}) - real (card {0::nat})) / real (card {0::nat}) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (∑i∈{0,1::nat}. ∑j∈{0,1} - {i}. (ip {0::nat} (antipodal i) (antipodal j))\<^sup>2) = real (card {0,1::nat}) * (real (card {0,1::nat}) - real (card {0::nat})) / real (card {0::nat}) | the two interference terms sum to the Welch bound exactly | — | (rule antipodal_achieves_welch) | method |
