<!--
  i-orca surface for examples/pic_binding/PROPOSAL.md (PIC x tensor-product binding).

  The proofs live in the kernel-checked substrate examples/pic_core/PIC_Binding.thy (session PIC_Core,
  quick_and_dirty = false, 0 sorry). Each theorem below is STATED in i-orca form and discharged by
  `(rule <lemma>)`, the sibling-corpus pattern.

  Verification:
    - substrate:  isabelle build -d examples/pic_core PIC_Core
    - surface:    isabelle build -b -d examples/pic_core PIC_Core   (store the heap once)
                  i-orca check examples/pic_binding/pic_binding.i.orca.md -d examples/pic_core --session PIC_Core
      All 15 theorems kernel-checked, formal_fraction_real = 1.000 each (2026-10-03, ~80 s).
      Without --session, i-orca infers parent HOL and reloads PIC_Core + HOL-Analysis from source per theorem
      (~8 min and heavy memory each) -- same verdict, much slower.

  Scope: T1 (absolute + SIGNED), T1', T2 (diagonal-inclusive convention), T3 (one factor of 2), T5(a).
  OPEN: T2 claim 4 (frame-operator tightness), T4, T5(b)/(c), T6, the pairwise substitution certificate, and the
  pre-norm Lipschitz step. No theorem here says any model is TPR-shaped.
-->

# theorem InnerTprod
> T0/T1 substrate: the concrete tensor product satisfies ⟨f⊗r, g⊗s⟩ = ⟨f,g⟩⟨r,s⟩ -- a lemma, not an assumption. Cites `inner_tprod`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| inner (tprod f r) (tprod g s) = inner f g * inner r s |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | inner (tprod f r) (tprod g s) = inner f g * inner r s | discharged by the kernel-checked substrate lemma | — | (rule inner_tprod) | method |

# theorem TensorCoherence
> T1 (absolute): binding does not raise coherence; for |A|,|S| ≥ 2 and unit frames, μ(F⊗R) = max μ_F μ_R. Cites `tensor_coherence`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite A ⟹ finite S ⟹ 2 ≤ card A ⟹ 2 ≤ card S ⟹ ∀a∈A. norm ((f::'a ⇒ real^'n) a) = 1 ⟹ ∀s∈S. norm ((r::'s ⇒ real^'m) s) = 1 ⟹ coh (bound f r) (A × S) = max (coh f A) (coh r S) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ finite S ⟹ 2 ≤ card A ⟹ 2 ≤ card S ⟹ ∀a∈A. norm ((f::'a ⇒ real^'n) a) = 1 ⟹ ∀s∈S. norm ((r::'s ⇒ real^'m) s) = 1 ⟹ coh (bound f r) (A × S) = max (coh f A) (coh r S) | discharged by the kernel-checked substrate lemma | — | (rule tensor_coherence) | method |

# theorem TensorSignedCoherence
> T1 (signed form, the one to encode): a bound pair's signed coherence is the max of the filler's, the role's, and the both-differ products -- which can be positive when both signed coherences are negative. Cites `tensor_signed_coherence`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite A ⟹ finite S ⟹ 2 ≤ card A ⟹ 2 ≤ card S ⟹ a ∈ A ⟹ s ∈ S ⟹ norm ((f::'a ⇒ real^'n) a) = 1 ⟹ norm ((r::'s ⇒ real^'m) s) = 1 ⟹ scoh (bound f r) (A × S) (a, s) = Max {scoh f A a, scoh r S s, Max ((λ(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) × (S - {s})))} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ finite S ⟹ 2 ≤ card A ⟹ 2 ≤ card S ⟹ a ∈ A ⟹ s ∈ S ⟹ norm ((f::'a ⇒ real^'n) a) = 1 ⟹ norm ((r::'s ⇒ real^'m) s) = 1 ⟹ scoh (bound f r) (A × S) (a, s) = Max {scoh f A a, scoh r S s, Max ((λ(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) × (S - {s})))} | discharged by the kernel-checked substrate lemma | — | (rule tensor_signed_coherence) | method |

# theorem TensorOptimalMargin
> T1′: via optimal_margin_coherence_sandwich, a bound pair's optimal decode margin is at least 1 minus its signed coherence. Cites `tensor_optimal_margin`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite A ⟹ finite S ⟹ 2 ≤ card A ⟹ 2 ≤ card S ⟹ a ∈ A ⟹ s ∈ S ⟹ ∀b∈A. norm ((f::'a ⇒ real^'n) b) = 1 ⟹ ∀t∈S. norm ((r::'s ⇒ real^'m) t) = 1 ⟹ 1 - scoh (bound f r) (A × S) (a, s) ≤ optmargin (bound f r) (a, s) (A × S - {(a, s)}) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ finite S ⟹ 2 ≤ card A ⟹ 2 ≤ card S ⟹ a ∈ A ⟹ s ∈ S ⟹ ∀b∈A. norm ((f::'a ⇒ real^'n) b) = 1 ⟹ ∀t∈S. norm ((r::'s ⇒ real^'m) t) = 1 ⟹ 1 - scoh (bound f r) (A × S) (a, s) ≤ optmargin (bound f r) (a, s) (A × S - {(a, s)}) | discharged by the kernel-checked substrate lemma | — | (rule tensor_optimal_margin) | method |

# theorem TensorFramePotential
> T2: the DIAGONAL-INCLUSIVE frame potential Σ_ij ⟨x_i,x_j⟩² is multiplicative under binding. (pil's off-diagonal normalised fp/welch is a different quantity and does not factor.) Cites `tensor_frame_potential`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| FP (bound (f::'a ⇒ real^'n) (r::'s ⇒ real^'m)) (A × S) = FP f A * FP r S |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | FP (bound (f::'a ⇒ real^'n) (r::'s ⇒ real^'m)) (A × S) = FP f A * FP r S | discharged by the kernel-checked substrate lemma | — | (rule tensor_frame_potential) | method |

# theorem TensorWelchValue
> T2: the Welch value card²/dim is multiplicative. Cites `tensor_welch_value`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| welch_value (A × S) (dF * dR) = welch_value A dF * welch_value S dR |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | welch_value (A × S) (dF * dR) = welch_value A dF * welch_value S dR | discharged by the kernel-checked substrate lemma | — | (rule tensor_welch_value) | method |

# theorem TensorFpWelchRatio
> T2: hence the diagonal-inclusive FP/Welch ratio is multiplicative. Cites `tensor_fp_welch_ratio`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| FP (bound (f::'a ⇒ real^'n) (r::'s ⇒ real^'m)) (A × S) / welch_value (A × S) (dF * dR) = (FP f A / welch_value A dF) * (FP r S / welch_value S dR) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | FP (bound (f::'a ⇒ real^'n) (r::'s ⇒ real^'m)) (A × S) / welch_value (A × S) (dF * dR) = (FP f A / welch_value A dF) * (FP r S / welch_value S dR) | discharged by the kernel-checked substrate lemma | — | (rule tensor_fp_welch_ratio) | method |

# theorem UnbindCertified
> T3: matched-filter unbinding decodes the filler of role s0 whenever 1 - ⟨f(σ s0), f b⟩ > 2 (k-1) μ_R for every rival b. The factor 2 enters once (decode_margin_certified); δ = (k-1) μ_R is the per-score crosstalk bound. Cites `unbind_certified`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite D ⟹ s0 ∈ D ⟹ card D = k ⟹ norm ((r::'s ⇒ real^'m) s0) = 1 ⟹ ∀b∈Fs ∪ σ ` D. norm ((f::'b ⇒ real^'n) b) = 1 ⟹ ∀t∈D - {s0}. ¦inner (r t) (r s0)¦ ≤ μ ⟹ σ s0 ∈ Fs ⟹ ∀b∈Fs. b ≠ σ s0 ⟶ 1 - inner (f (σ s0)) (f b) > 2 * ((real k - 1) * μ) ⟹ decodes_to (λb. inner (unbind (structure_tpr f r σ D) (r s0)) (f b)) Fs (σ s0) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite D ⟹ s0 ∈ D ⟹ card D = k ⟹ norm ((r::'s ⇒ real^'m) s0) = 1 ⟹ ∀b∈Fs ∪ σ ` D. norm ((f::'b ⇒ real^'n) b) = 1 ⟹ ∀t∈D - {s0}. ¦inner (r t) (r s0)¦ ≤ μ ⟹ σ s0 ∈ Fs ⟹ ∀b∈Fs. b ≠ σ s0 ⟶ 1 - inner (f (σ s0)) (f b) > 2 * ((real k - 1) * μ) ⟹ decodes_to (λb. inner (unbind (structure_tpr f r σ D) (r s0)) (f b)) Fs (σ s0) | discharged by the kernel-checked substrate lemma | — | (rule unbind_certified) | method |

# theorem SubstitutionCertified
> T5(a): replacing the decode input r by r̂ preserves the argmax t whenever every margin exceeds 2δ, with δ bounding |⟨r - r̂, U v⟩| on V. Cites `substitution_certified`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ ∀v∈V. ¦inner (r - rhat) ((U::'v ⇒ 'a::real_inner) v)¦ ≤ δ ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * δ ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ ∀v∈V. ¦inner (r - rhat) ((U::'v ⇒ 'a::real_inner) v)¦ ≤ δ ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * δ ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule substitution_certified) | method |

# theorem SubstitutionCertifiedMax
> T5(a), the stated form: margin > 2·max_v |⟨r - r̂, U_v⟩| over a finite V certifies the substitution. Cites `substitution_certified_max`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite V ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ (inner r ((U::'v ⇒ 'a::real_inner) t) + bias t) - (inner r (U v) + bias v) > 2 * Max ((λv. ¦inner (r - rhat) (U v)¦) ` V) ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite V ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ (inner r ((U::'v ⇒ 'a::real_inner) t) + bias t) - (inner r (U v) + bias v) > 2 * Max ((λv. ¦inner (r - rhat) (U v)¦) ` V) ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule substitution_certified_max) | method |

# theorem SubstitutionCertifiedNorm
> T5(a), Cauchy-Schwarz form: δ = |r - r̂| · u_max. Cites `substitution_certified_norm`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * (norm (r - rhat) * u) ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * (norm (r - rhat) * u) ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule substitution_certified_norm) | method |

# theorem SubstitutionPairwiseIff
> T5(a), pairwise and EXACT: the substituted decode keeps t iff, for every rival v, the original margin over v exceeds ⟨r - r̂, U t - U v⟩. Cites `substitution_pairwise_iff`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ decodes_to (λv. inner rhat ((U::'v ⇒ 'a::real_inner) v) + bias v) V t = (∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ decodes_to (λv. inner rhat ((U::'v ⇒ 'a::real_inner) v) + bias v) V t = (∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)) | discharged by the kernel-checked substrate lemma | — | (rule substitution_pairwise_iff) | method |

# theorem SubstitutionCertifiedPairwise
> T5(a), pairwise certificate (the sufficiency half of the iff). Cites `substitution_certified_pairwise`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ (inner r ((U::'v ⇒ 'a::real_inner) t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v) ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ (inner r ((U::'v ⇒ 'a::real_inner) t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v) ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule substitution_certified_pairwise) | method |

# theorem UniformImpliesPairwise
> The pairwise certificate is at least as strong as the uniform one: the uniform T5(a) hypothesis implies the pairwise condition. Cites `uniform_implies_pairwise`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ ∀v∈V. ¦inner (r - rhat) ((U::'v ⇒ 'a::real_inner) v)¦ ≤ δ ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * δ ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ ∀v∈V. ¦inner (r - rhat) ((U::'v ⇒ 'a::real_inner) v)¦ ≤ δ ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * δ ⟹ ∀v∈V. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v) | discharged by the kernel-checked substrate lemma | — | (rule uniform_implies_pairwise) | method |

# theorem SubstitutionCertifiedHybrid
> Hybrid certificate: pairwise on a rival set K, and outside K the norm tail bound |⟨r - r̂, U t⟩| + |r - r̂|·u_max. Cites `substitution_certified_hybrid`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ ∀v∈K. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v) ⟹ ∀v∈V - K. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > ¦inner (r - rhat) (U t)¦ + norm (r - rhat) * u ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ ∀v∈K. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v) ⟹ ∀v∈V - K. v ≠ t ⟶ (inner r (U t) + bias t) - (inner r (U v) + bias v) > ¦inner (r - rhat) (U t)¦ + norm (r - rhat) * u ⟹ decodes_to (λv. inner rhat (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule substitution_certified_hybrid) | method |
