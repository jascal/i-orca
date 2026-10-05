<!--
  i-orca surface for examples/pic_binding/PROPOSAL.md (PIC x tensor-product binding).

  The proofs live in the kernel-checked substrate examples/pic_core/PIC_Binding.thy (session PIC_Core,
  quick_and_dirty = false, 0 sorry). Each theorem below is STATED in i-orca form and discharged by
  `(rule <lemma>)`, the sibling-corpus pattern.

  Verification:
    - substrate:  isabelle build -d examples/pic_core PIC_Core
    - surface:    isabelle build -b -d examples/pic_core PIC_Core   (store the heap once)
                  i-orca check examples/pic_binding/pic_binding.i.orca.md -d examples/pic_core --session PIC_Core
      All 46 theorems kernel-checked, formal_fraction_real = 1.000 each (2026-10-04).
      Without --session, i-orca infers parent HOL and reloads PIC_Core + HOL-Analysis from source per theorem
      (~8 min and heavy memory each) -- same verdict, much slower.

  Scope: T1 (absolute + SIGNED), T1', T2 (diagonal-inclusive convention), T3 (one factor of 2), T5(a) (uniform,
  pairwise-exact, hybrid), T5(b) (domain, given an error bound on the whole domain), T5(c) (hull ceiling; bias-free, and biased via a lift).
  T6(b) clean-up constants (PIC_Cleanup.thy). T6(a) iff (PIC_Cleanup.thy). OPEN: T2 claim 4 (frame-operator tightness), T4, bounding the fit error off the evaluated contexts, and the
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

# theorem SubstitutionDomainNorm
> T5(b): one fit-error bound ε on a whole domain D, with every margin > 2·ε·u_max, certifies every context in D (evaluated or not). Cites `substitution_domain_norm`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| ∀x∈D. t x ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ ∀x∈D. norm (r x - rhat x) ≤ ε ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > 2 * (ε * u) ⟹ ∀x∈D. decodes_to (λv. inner (rhat x) (U v) + bias v) V (t x) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀x∈D. t x ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ ∀x∈D. norm (r x - rhat x) ≤ ε ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > 2 * (ε * u) ⟹ ∀x∈D. decodes_to (λv. inner (rhat x) (U v) + bias v) V (t x) | discharged by the kernel-checked substrate lemma | — | (rule substitution_domain_norm) | method |

# theorem SubstitutionDomainPairwise
> T5(b), per-rival: with ‖r − r̂‖ ≤ ε on D, margin over each rival v > ε·‖U_t − U_v‖ certifies every context in D. Cites `substitution_domain_pairwise`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| ∀x∈D. t x ∈ V ⟹ ∀x∈D. norm (r x - rhat x) ≤ ε ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > ε * norm ((U::'v ⇒ 'a::real_inner) (t x) - U v) ⟹ ∀x∈D. decodes_to (λv. inner (rhat x) (U v) + bias v) V (t x) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀x∈D. t x ∈ V ⟹ ∀x∈D. norm (r x - rhat x) ≤ ε ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > ε * norm ((U::'v ⇒ 'a::real_inner) (t x) - U v) ⟹ ∀x∈D. decodes_to (λv. inner (rhat x) (U v) + bias v) V (t x) | discharged by the kernel-checked substrate lemma | — | (rule substitution_domain_pairwise) | method |

# theorem DomainNormImpliesPairwise
> T5(b): the per-rival domain threshold never exceeds the norm one, so the per-rival form is at least as strong. Cites `domain_norm_implies_pairwise`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ v ∈ V ⟹ ∀w∈V. norm ((U::'v ⇒ 'a::real_inner) w) ≤ u ⟹ 0 ≤ ε ⟹ ε * norm (U t - U v) ≤ 2 * (ε * u) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ v ∈ V ⟹ ∀w∈V. norm ((U::'v ⇒ 'a::real_inner) w) ≤ u ⟹ 0 ≤ ε ⟹ ε * norm (U t - U v) ≤ 2 * (ε * u) | discharged by the kernel-checked substrate lemma | — | (rule domain_norm_implies_pairwise) | method |

# theorem HullMarginUpperScaled
> T5(c) substrate: for any residual r (not only unit), some rival's margin is at most ‖r‖ times the hull distance. Cites `hull_margin_upper_scaled`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite C ⟹ C ≠ {} ⟹ ∃v∈C. inner r ((U::'v ⇒ 'a::euclidean_space) t - U v) ≤ norm r * infdist (U t) (convex hull (U ` C)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite C ⟹ C ≠ {} ⟹ ∃v∈C. inner r ((U::'v ⇒ 'a::euclidean_space) t - U v) ≤ norm r * infdist (U t) (convex hull (U ` C)) | discharged by the kernel-checked substrate lemma | — | (rule hull_margin_upper_scaled) | method |

# theorem CertificateHullCeiling
> T5(c): bias-free; a certificate needing every margin > m can fire only if m < ‖r‖·hdist(t). The ceiling is set by the frame and ‖r‖, independent of the substitute. Cites `certificate_hull_ceiling`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite C ⟹ C ≠ {} ⟹ ∀v∈C. inner r ((U::'v ⇒ 'a::euclidean_space) t) - inner r (U v) > m ⟹ m < norm r * infdist (U t) (convex hull (U ` C)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite C ⟹ C ≠ {} ⟹ ∀v∈C. inner r ((U::'v ⇒ 'a::euclidean_space) t) - inner r (U v) > m ⟹ m < norm r * infdist (U t) (convex hull (U ` C)) | discharged by the kernel-checked substrate lemma | — | (rule certificate_hull_ceiling) | method |

# theorem SubstitutionHullCeiling
> T5(c), bias-free uniform threshold instance: a bias-free margin ⟨r, U_t⟩ − ⟨r, U_v⟩ > 2δ for every rival is possible only if 2δ < ‖r‖·hdist(t). A biased margin is bounded by `certificate_hull_ceiling_biased`, not by this. Cites `substitution_hull_ceiling`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite V ⟹ V - {t} ≠ {} ⟹ ∀v∈V. v ≠ t ⟶ inner r ((U::'v ⇒ 'a::euclidean_space) t) - inner r (U v) > 2 * δ ⟹ 2 * δ < norm r * infdist (U t) (convex hull (U ` (V - {t}))) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite V ⟹ V - {t} ≠ {} ⟹ ∀v∈V. v ≠ t ⟶ inner r ((U::'v ⇒ 'a::euclidean_space) t) - inner r (U v) > 2 * δ ⟹ 2 * δ < norm r * infdist (U t) (convex hull (U ` (V - {t}))) | discharged by the kernel-checked substrate lemma | — | (rule substitution_hull_ceiling) | method |

# theorem CertificateHullCeilingBiased
> T5(c), biased decode by lifting: with a per-token bias b, a certificate needing every margin > m fires only if m < ‖(w, s)‖ · infdist((U_t, b_t/s), conv{(U_v, b_v/s)}), for every s > 0. An upper bound only. Cites `certificate_hull_ceiling_biased`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| finite C ⟹ C ≠ {} ⟹ 0 < s ⟹ ∀v∈C. (inner w ((U::'v ⇒ 'a::euclidean_space) t) + (b::'v ⇒ real) t) - (inner w (U v) + b v) > m ⟹ m < norm (w, s) * infdist (U t, b t / s) (convex hull ((λv. (U v, b v / s)) ` C)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite C ⟹ C ≠ {} ⟹ 0 < s ⟹ ∀v∈C. (inner w ((U::'v ⇒ 'a::euclidean_space) t) + (b::'v ⇒ real) t) - (inner w (U v) + b v) > m ⟹ m < norm (w, s) * infdist (U t, b t / s) (convex hull ((λv. (U v, b v / s)) ` C)) | discharged by the kernel-checked substrate lemma | — | (rule certificate_hull_ceiling_biased) | method |

# theorem DomainNormPremiseImpliesPairwise
> T5(b): the norm-form domain premises (with ε ≥ 0) imply the per-rival domain premises, so `substitution_domain_pairwise` certifies everything `substitution_domain_norm` does. Cites `domain_norm_premise_implies_pairwise`.

## imports
| Theory      |
|-------------|
| PIC_Binding |

## goal
| Statement |
|-----------|
| ∀x∈D. t x ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ 0 ≤ ε ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > 2 * (ε * u) ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > ε * norm (U (t x) - U v) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀x∈D. t x ∈ V ⟹ ∀v∈V. norm ((U::'v ⇒ 'a::real_inner) v) ≤ u ⟹ 0 ≤ ε ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > 2 * (ε * u) ⟹ ∀x∈D. ∀v∈V. v ≠ t x ⟶ (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > ε * norm (U (t x) - U v) | discharged by the kernel-checked substrate lemma | — | (rule domain_norm_premise_implies_pairwise) | method |

# theorem NearestPointCleanup
> T6(b): a γ-separated code and a query within γ/2 of a code point: that point is the unique nearest. Cites `nearest_point_cleanup`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| ∀a∈A. ∀a'∈A. a ≠ a' ⟶ γ ≤ dist ((c::'a ⇒ 'x::metric_space) a) (c a') ⟹ a ∈ A ⟹ dist g (c a) < γ / 2 ⟹ ∀a'∈A. a' ≠ a ⟶ dist g (c a) < dist g (c a') |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀a∈A. ∀a'∈A. a ≠ a' ⟶ γ ≤ dist ((c::'a ⇒ 'x::metric_space) a) (c a') ⟹ a ∈ A ⟹ dist g (c a) < γ / 2 ⟹ ∀a'∈A. a' ≠ a ⟶ dist g (c a) < dist g (c a') | discharged by the kernel-checked substrate lemma | — | (rule nearest_point_cleanup) | method |

# theorem NearestPointRadiusTight
> T6(b): γ/2 cannot be enlarged; the midpoint of two code points γ apart is equidistant. Cites `nearest_point_radius_tight`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| dist ((γ::real) / 2) 0 = ¦γ¦ / 2 ∧ dist (γ / 2) γ = ¦γ¦ / 2 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | dist ((γ::real) / 2) 0 = ¦γ¦ / 2 ∧ dist (γ / 2) γ = ¦γ¦ / 2 | discharged by the kernel-checked substrate lemma | — | (rule nearest_point_radius_tight) | method |

# theorem UnbindNormLe
> T6(b): unbinding is bounded, ‖unbind e w‖ ≤ ‖e‖‖w‖ (Frobenius). Cites `unbind_norm_le`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| norm (unbind (e::real^'m^'n) w) ≤ norm e * norm w |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | norm (unbind (e::real^'m^'n) w) ≤ norm e * norm w | discharged by the kernel-checked substrate lemma | — | (rule unbind_norm_le) | method |

# theorem RoleCleanup
> T6(b): with ⟨r_s, w⟩ = 1, if crosstalk + ‖e‖‖w‖ < γ/2 then the nearest filler to the role-s readout is σ(s). Cites `role_cleanup`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| finite D ⟹ s ∈ D ⟹ inner (r s) w = 1 ⟹ ∀a∈F. ∀a'∈F. a ≠ a' ⟶ γ ≤ dist ((f::'b ⇒ real^'n) a) (f a') ⟹ σ s ∈ F ⟹ norm (∑t∈D - {s}. scaleR (inner (r t) w) (f (σ t))) + norm e * norm w < γ / 2 ⟹ ah ∈ F ⟹ ∀a'∈F. dist (unbind (structure_tpr f r σ D + e) w) (f ah) ≤ dist (unbind (structure_tpr f r σ D + e) w) (f a') ⟹ ah = σ s |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite D ⟹ s ∈ D ⟹ inner (r s) w = 1 ⟹ ∀a∈F. ∀a'∈F. a ≠ a' ⟶ γ ≤ dist ((f::'b ⇒ real^'n) a) (f a') ⟹ σ s ∈ F ⟹ norm (∑t∈D - {s}. scaleR (inner (r t) w) (f (σ t))) + norm e * norm w < γ / 2 ⟹ ah ∈ F ⟹ ∀a'∈F. dist (unbind (structure_tpr f r σ D + e) w) (f ah) ≤ dist (unbind (structure_tpr f r σ D + e) w) (f a') ⟹ ah = σ s | discharged by the kernel-checked substrate lemma | — | (rule role_cleanup) | method |

# theorem LeftInverseNoise
> T6(b): through a linear left inverse P of W with ‖P y‖ ≤ K‖y‖, tensor noise is at most K times residual noise. Cites `left_inverse_noise`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| linear (P::'d::real_normed_vector ⇒ 'e::real_normed_vector) ⟹ ∀T. P (W T) = T ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ norm (P (u - b0) - T) ≤ K * norm (u - (W T + b0)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | linear (P::'d::real_normed_vector ⇒ 'e::real_normed_vector) ⟹ ∀T. P (W T) = T ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ norm (P (u - b0) - T) ≤ K * norm (u - (W T + b0)) | discharged by the kernel-checked substrate lemma | — | (rule left_inverse_noise) | method |

# theorem AgreementBall
> T6(b): if ‖n‖·‖U_t − U_v‖ < the code point's margin over every rival v, the host x + n decides t. The radius min_v m_v/‖U_t − U_v‖ is the distance to t's cell boundary. Cites `agreement_ball`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm n * norm ((U::'v ⇒ 'a::real_inner) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ decodes_to (λv. inner (x + n) (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm n * norm ((U::'v ⇒ 'a::real_inner) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ decodes_to (λv. inner (x + n) (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule agreement_ball) | method |

# theorem CleanupCertifiedExact
> T6(b) certificate, part 1: within the clean-up radius ρ, clean-up returns the code point x(σ) exactly. Cites `cleanup_certified(1)`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. ∀a∈F s. ∀a'∈F s. a ≠ a' ⟶ γ s ≤ dist ((f::'b ⇒ real^'n) a) (f a') ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. norm (∑t∈D - {s}. scaleR (inner (r t) (w s)) (f (σ t))) + K * norm (u - x) * norm (w s) < γ s / 2 ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ W (structure_tpr f r σh D) + b0 = x |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. ∀a∈F s. ∀a'∈F s. a ≠ a' ⟶ γ s ≤ dist ((f::'b ⇒ real^'n) a) (f a') ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. norm (∑t∈D - {s}. scaleR (inner (r t) (w s)) (f (σ t))) + K * norm (u - x) * norm (w s) < γ s / 2 ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ W (structure_tpr f r σh D) + b0 = x | discharged by the kernel-checked substrate lemma | — | (rule cleanup_certified(1)) | method |

# theorem CleanupCertifiedDecision
> T6(b) certificate, part 2: within the agreement radius β, the host decides the code point's decision t. Cites `cleanup_certified(2)`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. ∀a∈F s. ∀a'∈F s. a ≠ a' ⟶ γ s ≤ dist ((f::'b ⇒ real^'n) a) (f a') ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. norm (∑t∈D - {s}. scaleR (inner (r t) (w s)) (f (σ t))) + K * norm (u - x) * norm (w s) < γ s / 2 ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ decodes_to (λv. inner u (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. ∀a∈F s. ∀a'∈F s. a ≠ a' ⟶ γ s ≤ dist ((f::'b ⇒ real^'n) a) (f a') ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. norm (∑t∈D - {s}. scaleR (inner (r t) (w s)) (f (σ t))) + K * norm (u - x) * norm (w s) < γ s / 2 ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ decodes_to (λv. inner u (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule cleanup_certified(2)) | method |

# theorem NearestIffHalfspace
> Directional clean-up: the readout fs + z is strictly nearer fs than fa iff ⟨z, fa − fs⟩ < ‖fa − fs‖²/2 (the bisector half-space). Cites `nearest_iff_halfspace`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| dist ((fs::'a::real_inner) + z) fs < dist (fs + z) fa ⟷ inner z (fa - fs) < (norm (fa - fs))⇧2 / 2 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | dist ((fs::'a::real_inner) + z) fs < dist (fs + z) fa ⟷ inner z (fa - fs) < (norm (fa - fs))⇧2 / 2 | discharged by the kernel-checked substrate lemma | — | (rule nearest_iff_halfspace) | method |

# theorem DirectionalSnap
> Directional clean-up: if the readout offset is c + m with ⟨m, d⟩ = ⟨n, q⟩, then ‖n‖‖q‖ < ‖d‖²/2 − ⟨c, d⟩ keeps fs strictly nearer than fa. Cites `directional_snap`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| inner (m::'a::real_inner) (fa - fs) = inner (n::'d::real_inner) q ⟹ norm n * norm q < (norm (fa - fs))⇧2 / 2 - inner c (fa - fs) ⟹ dist (fs + (c + m)) fs < dist (fs + (c + m)) fa |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | inner (m::'a::real_inner) (fa - fs) = inner (n::'d::real_inner) q ⟹ norm n * norm q < (norm (fa - fs))⇧2 / 2 - inner c (fa - fs) ⟹ dist (fs + (c + m)) fs < dist (fs + (c + m)) fa | discharged by the kernel-checked substrate lemma | — | (rule directional_snap) | method |

# theorem DirectionalRadiusTight
> Directional clean-up: the radius (‖d‖²/2 − ⟨c, d⟩)/‖q‖ is exact; noise of that size along q reaches the bisector. Cites `directional_radius_tight`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| ∀y. inner ((M::'d::real_inner ⇒ 'a::real_inner) y) d = inner y q ⟹ q ≠ 0 ⟹ (norm d)⇧2 / 2 - inner c d ≤ t * norm q ⟹ ¬ dist (fs + (c + M ((t / norm q) *⇩R q))) fs < dist (fs + (c + M ((t / norm q) *⇩R q))) (fs + d) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀y. inner ((M::'d::real_inner ⇒ 'a::real_inner) y) d = inner y q ⟹ q ≠ 0 ⟹ (norm d)⇧2 / 2 - inner c d ≤ t * norm q ⟹ ¬ dist (fs + (c + M ((t / norm q) *⇩R q))) fs < dist (fs + (c + M ((t / norm q) *⇩R q))) (fs + d) | discharged by the kernel-checked substrate lemma | — | (rule directional_radius_tight) | method |

# theorem DirectionalQBound
> Directional clean-up: ‖q‖ ≤ K‖w‖‖d‖, so the directional radius never falls below the worst-case one. Cites `directional_q_bound`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| ∀y. inner (unbind ((P::'d::real_inner ⇒ real^'m^'n) y) w) d = inner y q ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ 0 ≤ K ⟹ norm q ≤ K * norm w * norm d |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀y. inner (unbind ((P::'d::real_inner ⇒ real^'m^'n) y) w) d = inner y q ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ 0 ≤ K ⟹ norm q ≤ K * norm w * norm d | discharged by the kernel-checked substrate lemma | — | (rule directional_q_bound) | method |

# theorem WorstCaseImpliesDirectional
> Directional clean-up: the worst-case condition ‖n‖·K‖w‖ < γ/2 (γ ≤ ‖d‖) implies the directional one. Cites `worst_case_implies_directional`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| ∀y. inner (unbind ((P::'d::real_inner ⇒ real^'m^'n) y) w) d = inner y q ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ 0 ≤ K ⟹ norm (n::'d) * (K * norm w) < γ / 2 ⟹ γ ≤ norm d ⟹ d ≠ 0 ⟹ norm n * norm q < (norm d)⇧2 / 2 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀y. inner (unbind ((P::'d::real_inner ⇒ real^'m^'n) y) w) d = inner y q ⟹ ∀y. norm (P y) ≤ K * norm y ⟹ 0 ≤ K ⟹ norm (n::'d) * (K * norm w) < γ / 2 ⟹ γ ≤ norm d ⟹ d ≠ 0 ⟹ norm n * norm q < (norm d)⇧2 / 2 | discharged by the kernel-checked substrate lemma | — | (rule worst_case_implies_directional) | method |

# theorem RoleCleanupDirectional
> Directional clean-up, per role: the half-space condition for every rival filler forces the nearest filler to be σ(s). Cites `role_cleanup_directional`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| finite D ⟹ s ∈ D ⟹ inner (r s) w = 1 ⟹ σ s ∈ (F::'b set) ⟹ ah ∈ F ⟹ ∀a∈F. inner (unbind e w) ((f::'b ⇒ real^'n) a - f (σ s)) = inner (n::'d::real_inner) (q a) ⟹ ∀a∈F. a ≠ σ s ⟶ norm n * norm (q a) < (norm (f a - f (σ s)))⇧2 / 2 - inner (∑t∈D - {s}. inner (r t) w *⇩R f (σ t)) (f a - f (σ s)) ⟹ ∀a'∈F. dist (unbind (structure_tpr f r σ D + e) w) (f ah) ≤ dist (unbind (structure_tpr f r σ D + e) w) (f a') ⟹ ah = σ s |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite D ⟹ s ∈ D ⟹ inner (r s) w = 1 ⟹ σ s ∈ (F::'b set) ⟹ ah ∈ F ⟹ ∀a∈F. inner (unbind e w) ((f::'b ⇒ real^'n) a - f (σ s)) = inner (n::'d::real_inner) (q a) ⟹ ∀a∈F. a ≠ σ s ⟶ norm n * norm (q a) < (norm (f a - f (σ s)))⇧2 / 2 - inner (∑t∈D - {s}. inner (r t) w *⇩R f (σ t)) (f a - f (σ s)) ⟹ ∀a'∈F. dist (unbind (structure_tpr f r σ D + e) w) (f ah) ≤ dist (unbind (structure_tpr f r σ D + e) w) (f a') ⟹ ah = σ s | discharged by the kernel-checked substrate lemma | — | (rule role_cleanup_directional) | method |

# theorem CleanupCertifiedDirectionalExact
> Directional T6(b) certificate, part 1: clean-up returns x(σ) exactly within ρ_dir. Cites `cleanup_certified_directional`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. ∀a∈F s. ∀y. inner (unbind (P y) (w s)) ((f::'b ⇒ real^'n) a - f (σ s)) = inner y (q s a) ⟹ ∀s∈D. ∀a∈F s. a ≠ σ s ⟶ norm (u - x) * norm (q s a) < (norm (f a - f (σ s)))⇧2 / 2 - inner (∑t∈D - {s}. inner (r t) (w s) *⇩R f (σ t)) (f a - f (σ s)) ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ W (structure_tpr f r σh D) + b0 = x |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. ∀a∈F s. ∀y. inner (unbind (P y) (w s)) ((f::'b ⇒ real^'n) a - f (σ s)) = inner y (q s a) ⟹ ∀s∈D. ∀a∈F s. a ≠ σ s ⟶ norm (u - x) * norm (q s a) < (norm (f a - f (σ s)))⇧2 / 2 - inner (∑t∈D - {s}. inner (r t) (w s) *⇩R f (σ t)) (f a - f (σ s)) ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ W (structure_tpr f r σh D) + b0 = x | discharged by the kernel-checked substrate lemma | — | (rule cleanup_certified_directional(1)) | method |

# theorem CleanupCertifiedDirectionalDecision
> Directional T6(b) certificate, part 2: the host decides the code point's t within β. Cites `cleanup_certified_directional`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. ∀a∈F s. ∀y. inner (unbind (P y) (w s)) ((f::'b ⇒ real^'n) a - f (σ s)) = inner y (q s a) ⟹ ∀s∈D. ∀a∈F s. a ≠ σ s ⟶ norm (u - x) * norm (q s a) < (norm (f a - f (σ s)))⇧2 / 2 - inner (∑t∈D - {s}. inner (r t) (w s) *⇩R f (σ t)) (f a - f (σ s)) ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ decodes_to (λv. inner u (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite D ⟹ linear (P::'d::real_inner ⇒ real^'m^'n) ⟹ ∀T. P ((W::real^'m^'n ⇒ 'd) T) = T ⟹ ∀s∈D. inner (r s) (w s) = 1 ⟹ ∀s∈D. σ s ∈ F s ⟹ ∀s∈D. ∀a∈F s. ∀y. inner (unbind (P y) (w s)) ((f::'b ⇒ real^'n) a - f (σ s)) = inner y (q s a) ⟹ ∀s∈D. ∀a∈F s. a ≠ σ s ⟶ norm (u - x) * norm (q s a) < (norm (f a - f (σ s)))⇧2 / 2 - inner (∑t∈D - {s}. inner (r t) (w s) *⇩R f (σ t)) (f a - f (σ s)) ⟹ x = W (structure_tpr f r σ D) + b0 ⟹ ∀s∈D. σh s ∈ F s ⟹ ∀s∈D. ∀a'∈F s. dist (unbind (P (u - b0)) (w s)) (f (σh s)) ≤ dist (unbind (P (u - b0)) (w s)) (f a') ⟹ t ∈ V ⟹ ∀v∈V. v ≠ t ⟶ norm (u - x) * norm ((U::'v ⇒ 'd) t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v) ⟹ decodes_to (λv. inner u (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule cleanup_certified_directional(2)) | method |

# theorem ProjectionPreservesDifferences
> T6(a): a self-adjoint P that fixes d leaves ⟨r, d⟩ unchanged: ⟨P r, d⟩ = ⟨r, d⟩. Cites `projection_preserves_differences`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| ∀x y. inner ((P::'a::real_inner ⇒ 'a) x) y = inner x (P y) ⟹ P d = d ⟹ inner (P r) d = inner r d |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀x y. inner ((P::'a::real_inner ⇒ 'a) x) y = inner x (P y) ⟹ P d = d ⟹ inner (P r) d = inner r d | discharged by the kernel-checked substrate lemma | — | (rule projection_preserves_differences) | method |

# theorem ProjectionPreservesMargins
> T6(a): if P fixes U_t − U_v, the margin of t over v is the same for P r as for r. Cites `projection_preserves_margins`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| ∀x y. inner ((P::'a::real_inner ⇒ 'a) x) y = inner x (P y) ⟹ P ((U::'v ⇒ 'a) t - U v) = U t - U v ⟹ (inner (P r) (U t) + bias t) - (inner (P r) (U v) + bias v) = (inner r (U t) + bias t) - (inner r (U v) + bias v) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀x y. inner ((P::'a::real_inner ⇒ 'a) x) y = inner x (P y) ⟹ P ((U::'v ⇒ 'a) t - U v) = U t - U v ⟹ (inner (P r) (U t) + bias t) - (inner (P r) (U v) + bias v) = (inner r (U t) + bias t) - (inner r (U v) + bias v) | discharged by the kernel-checked substrate lemma | — | (rule projection_preserves_margins) | method |

# theorem ProjectionPreservesDecision
> T6(a): if P fixes every U_t − U_v, P r and r decode to t alike. Cites `projection_preserves_decision`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| ∀x y. inner ((P::'a::real_inner ⇒ 'a) x) y = inner x (P y) ⟹ ∀v∈V. P ((U::'v ⇒ 'a) t - U v) = U t - U v ⟹ decodes_to (λv. inner (P r) (U v) + bias v) V t ⟷ decodes_to (λv. inner r (U v) + bias v) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∀x y. inner ((P::'a::real_inner ⇒ 'a) x) y = inner x (P y) ⟹ ∀v∈V. P ((U::'v ⇒ 'a) t - U v) = U t - U v ⟹ decodes_to (λv. inner (P r) (U v) + bias v) V t ⟷ decodes_to (λv. inner r (U v) + bias v) V t | discharged by the kernel-checked substrate lemma | — | (rule projection_preserves_decision) | method |

# theorem ProjectionMarginChanges1
> T6(a), converse: if an orthogonal projection moves a difference d, the residual d − P d changes the margin along d by ‖d − P d‖² > 0 (the projected residual scores 0 along d). Cites `projection_margin_changes`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ P d ≠ d ⟹ inner (P (d - P d)) d = 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ P d ≠ d ⟹ inner (P (d - P d)) d = 0 | discharged by the kernel-checked substrate lemma | — | (rule projection_margin_changes(1)) | method |

# theorem ProjectionMarginChanges2
> T6(a), converse: if an orthogonal projection moves a difference d, the residual d − P d changes the margin along d by ‖d − P d‖² > 0 (the original scores ‖d − P d‖²). Cites `projection_margin_changes`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ P d ≠ d ⟹ inner (d - P d) d = (norm (d - P d))⇧2 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ P d ≠ d ⟹ inner (d - P d) d = (norm (d - P d))⇧2 | discharged by the kernel-checked substrate lemma | — | (rule projection_margin_changes(2)) | method |

# theorem ProjectionMarginChanges3
> T6(a), converse: if an orthogonal projection moves a difference d, the residual d − P d changes the margin along d by ‖d − P d‖² > 0 (and that change is positive). Cites `projection_margin_changes`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ P d ≠ d ⟹ (norm (d - P d))⇧2 > 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ P d ≠ d ⟹ (norm (d - P d))⇧2 > 0 | discharged by the kernel-checked substrate lemma | — | (rule projection_margin_changes(3)) | method |

# theorem ProjectionPreservesMarginsIff
> T6(a): an orthogonal projection preserves every margin of every residual IFF it fixes every readout difference. Cites `projection_preserves_margins_iff`.

## imports
| Theory      |
|-------------|
| PIC_Cleanup |

## goal
| Statement |
|-----------|
| linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ (∀r. ∀v∈V. ∀w∈V. inner (P r) ((U::'v ⇒ 'a) v - U w) = inner r (U v - U w)) ⟷ (∀v∈V. ∀w∈V. P (U v - U w) = U v - U w) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | linear (P::'a::real_inner ⇒ 'a) ⟹ ∀x. P (P x) = P x ⟹ ∀x y. inner (P x) y = inner x (P y) ⟹ (∀r. ∀v∈V. ∀w∈V. inner (P r) ((U::'v ⇒ 'a) v - U w) = inner r (U v - U w)) ⟷ (∀v∈V. ∀w∈V. P (U v - U w) = U v - U w) | discharged by the kernel-checked substrate lemma | — | (rule projection_preserves_margins_iff) | method |
