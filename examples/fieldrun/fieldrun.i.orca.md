<!--
  i-orca proofs of the theorems in ../fieldrun/paper/fieldrun_paper_draft.pdf
  ("What a Transformer Retrieves and What It Computes", J. Allan Scott).

  Each `# theorem` below formalises the *checkable core* of one paper result and
  lowers to Isabelle/Isar (the canonical backend). Honest reckonings (SPEC §2,
  §11.5): the static verifier checks the proof *skeleton*; a green `verify` is
  NOT a kernel proof. `formal_fraction_static` reports method coverage; the real
  status needs an Isabelle distribution (`i-orca check`). Steps the paper itself
  leaves open (general Horn separation; the cited Maslov limit; the asymptotic
  localisation bound) are marked as frontier holes — incompleteness is first-class.

  Paper map:  Thm 1 → CardinalityInertness          Thm 4 → RecoveredProbability
              Thm 2 → NonTruthFunctionalityBudget    Thm 5 → Diffuseness (+Asymptotic)
              Thm 3 → WeightedThresholdExpressivity   Thm 6 → TwoTemperatureSoundness
                      (+GeneralSeparation, open)      Prop 1 → PropPowerDiagram
                                                      Prop 2 → PropMarginDistance
-->

# theorem CardinalityInertness
> Theorem 1. Under the projective pairing the decision depends only on the totals (hence on {Δ, D_j}) and is invariant to the readout multiplicity μ_t: two source tensors c, c′ with equal column sums induce the same argmax even when their per-source argmax counts μ_t differ.

## imports
| Theory |
|--------|
| Main   |

## context
| Name  | Statement                                            |
|-------|------------------------------------------------------|
| eqtot | ⋀v. (∑j∈J. c j v) = (∑j∈J. c' j v)                    |

## goal
| Statement                                                                                              |
|--------------------------------------------------------------------------------------------------------|
| (∀w∈V. (∑j∈J. c j w) ≤ (∑j∈J. c j t)) = (∀w∈V. (∑j∈J. c' j w) ≤ (∑j∈J. c' j t)) |

## proof
| Id     | Claim                                                                                                  | By                              | Using  | Method            | Status |
|--------|--------------------------------------------------------------------------------------------------------|---------------------------------|--------|-------------------|--------|
| s_tot  | ⋀w. (∑j∈J. c j w) = (∑j∈J. c' j w)                                                                      | totals coincide; μ_t never enters L | eqtot  | (simp add: eqtot) | method |
| s_dec  | (∀w∈V. (∑j∈J. c j w) ≤ (∑j∈J. c j t)) = (∀w∈V. (∑j∈J. c' j w) ≤ (∑j∈J. c' j t)) | decision is a function of totals only | s_tot  | (simp add: s_tot) | method |

# theorem NonTruthFunctionalityBudget
> Theorem 2. Competition hardness is carried by the frame Gram: for unit directions ‖U_t − U_v‖² = 2(1 − ρ_tv), so the differential incidence becomes common-mode and collapses as ρ_tv → 1; and when G is diagonal (ρ_tv = 0, mutually exclusive outcomes) it reduces to the classical disjoint-outcome distance ‖U_t − U_v‖² = 2.

## imports
| Theory                     |
|----------------------------|
| HOL-Analysis.Inner_Product |

## context
| Name | Statement         |
|------|-------------------|
| ut   | norm (U t) = 1    |
| uv   | norm (U v) = 1    |

## goal
| Statement                                                                                                          |
|--------------------------------------------------------------------------------------------------------------------|
| (norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v)) ∧ (inner (U t) (U v) = 0 ⟶ (norm (U t - U v)) ^ 2 = 2) |

## proof
| Id   | Claim                                                                                       | By                          | Using   | Method                                                                                 | Status |
|------|---------------------------------------------------------------------------------------------|-----------------------------|---------|----------------------------------------------------------------------------------------|--------|
| s1   | (norm (U t - U v)) ^ 2 = (norm (U t)) ^ 2 - 2 * inner (U t) (U v) + (norm (U v)) ^ 2         | polarisation of the norm    | —       | (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute) | method |
| s2   | (norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v))                                         | substitute the unit norms   | s1      | (simp add: ut uv algebra_simps)                                                        | method |
| s3   | (norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v)) ∧ (inner (U t) (U v) = 0 ⟶ (norm (U t - U v)) ^ 2 = 2) | diagonal G is the ρ = 0 limit | s2 | (simp add: s2) | method |

# theorem WeightedThresholdExpressivity
> Theorem 3 (realisability half). A COMPOSED token (μ_t = 0) is the argmax of the weighted sum Σ_j c_j though no single source's argmax selects it: an explicit two-source, three-outcome witness where the sum prefers outcome 0 while source 1 prefers 1 and source 2 prefers 2 — realised by a weighted-threshold connective but by no singleton sufficient sub-conjunction.

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name   | Statement                                                            |
|--------|----------------------------------------------------------------------|
| c1_def | c1 = (λx::nat. if x = 0 then (2::real) else if x = 1 then 3 else 0)   |
| c2_def | c2 = (λx::nat. if x = 0 then (2::real) else if x = 1 then 0 else 3)   |
| L_def  | L = (λx. c1 x + c2 x)                                                 |

## goal
| Statement                                            |
|------------------------------------------------------|
| L 0 > L 1 ∧ L 0 > L 2 ∧ c1 1 > c1 0 ∧ c2 2 > c2 0    |

## proof
| Id  | Claim                                          | By                                       | Using   | Method                       | Status |
|-----|------------------------------------------------|------------------------------------------|---------|------------------------------|--------|
| s1  | L 0 = 4 ∧ L 1 = 3 ∧ L 2 = 3                     | the summed vote prefers outcome 0        | —       | (simp add: L_def c1_def c2_def) | method |
| s2  | c1 1 > c1 0 ∧ c2 2 > c2 0                       | each source's own argmax avoids outcome 0 (μ_0 = 0) | — | (simp add: c1_def c2_def)    | method |
| s3  | L 0 > L 1 ∧ L 0 > L 2 ∧ c1 1 > c1 0 ∧ c2 2 > c2 0 | composed token: realised by the sum, by no singleton | s1, s2 | simp | method |

# theorem MuZeroNotIrreducible
> Theorem 3 (general half) — restated faithfully and PROVEN. The earlier i-orca hole `horn_expressible t ⟶ mu_t t ≠ 0` used *uninterpreted* predicates, so it was vacuously refutable — never a faithful encoding. With explicit definitions (a source set S *decides* t when t is the strict argmax of the S-sum over outcomes V; μ_t = 0 means no *singleton* decides t; t is Horn/sub-conjunction-expressible when some *proper non-empty subset* already decides it), the substantive content is sharp: **μ_t = 0 does NOT imply not-Horn-expressible.** Witnessed here, kernel-checked: a 3-source token with μ_0 = 0 whose proper subset {1,2} already decides outcome 0. The dual positive result — genuinely *irreducible* composed tokens (no proper subset suffices) exist at every n (incl. an n = 3 case where every source is necessary, tying to §4.4 fragility) — is proven in the companion [`separation/Separation.thy`](separation/Separation.thy). The full expressivity *characterisation* over formula classes is the remaining genuine open frontier.

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name   | Statement |
|--------|-----------|
| c3_def | ⋀j v. c3 (j::nat) (v::nat) = (if j = 1 then (if v = 0 then (2::real) else if v = 1 then 3 else 0) else if j = 2 then (if v = 0 then 2 else if v = 1 then 0 else 3) else (if v = 0 then 0 else 1/2)) |

## goal
| Statement |
|-----------|
| (∀j∈{1,2,3}. ¬ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{j}. c3 i v) < (∑i∈{j}. c3 i 0))) ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{1,2,3}. c3 i v) < (∑i∈{1,2,3}. c3 i 0)) ∧ (∃P. P ≠ {} ∧ P ⊂ {1,2,3} ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈P. c3 i v) < (∑i∈P. c3 i 0))) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_mu0  | ∀j∈{1,2,3}. ¬ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{j}. c3 i v) < (∑i∈{j}. c3 i 0)) | μ_0 = 0: no singleton source decides outcome 0 | — | (simp add: c3_def) | method |
| s_dec  | ∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{1,2,3}. c3 i v) < (∑i∈{1,2,3}. c3 i 0) | the full triple decides outcome 0 | — | (simp add: c3_def) | method |
| s_suff | ∃P. P ≠ {} ∧ P ⊂ {1,2,3} ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈P. c3 i v) < (∑i∈P. c3 i 0)) | yet the proper subset {1,2} already decides outcome 0 | — | (rule exI[of _ "{1,2::nat}"]) (auto simp: c3_def) | method |
| s_show | (∀j∈{1,2,3}. ¬ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{j}. c3 i v) < (∑i∈{j}. c3 i 0))) ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{1,2,3}. c3 i v) < (∑i∈{1,2,3}. c3 i 0)) ∧ (∃P. P ≠ {} ∧ P ⊂ {1,2,3} ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈P. c3 i v) < (∑i∈P. c3 i 0))) | μ_0 = 0 yet Horn-expressible: the naive separation fails | s_mu0, s_dec, s_suff | blast | method |

# theorem RecoveredProbability
> Theorem 4. With a uniform base measure M_0 reweighted by exp(c_j^v) per source, the normalised mass m(v)/Σ_w m(w) = exp(L_v)/Z is exactly the softmax — the Gibbs measure recovered as a PIC incidence frequency, parameter-free.

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name   | Statement      |
|--------|----------------|
| M0pos  | (M0::real) > 0 |

## goal
| Statement                                                                          |
|------------------------------------------------------------------------------------|
| (M0 * exp (L v)) / (∑w∈V. M0 * exp (L w)) = exp (L v) / (∑w∈V. exp (L w))           |

## proof
| Id  | Claim                                                              | By                          | Using    | Method                                      | Status |
|-----|-------------------------------------------------------------------|-----------------------------|----------|---------------------------------------------|--------|
| s1  | (∑w∈V. M0 * exp (L w)) = M0 * (∑w∈V. exp (L w))                    | pull the common base out    | —        | (simp add: sum_distrib_left)                | method |
| s2  | M0 ≠ 0                                                             | the base is positive        | M0pos    | (metis less_irrefl)                         | method |
| s3  | (M0 * exp (L v)) / (∑w∈V. M0 * exp (L w)) = exp (L v) / (∑w∈V. exp (L w)) | cancel the base → softmax | s1, s2 | (simp add: mult_divide_mult_cancel_left) | method |

# theorem Diffuseness
> Theorem 5 (ratio core). Under equitable contributions e_m = E/PR, single-source relative influence is e_m/E = 1/PR and a k-source body captures only |A|/PR of E — so no bounded-size formula localises the quantity (the asymptotic O(1/PR) consequence is DiffusenessAsymptotic).

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name  | Statement                                |
|-------|------------------------------------------|
| Epos  | E ≠ 0                                     |
| equit | ⋀m. m ∈ {1..PR} ⟹ e m = E / real PR      |
| Asub  | A ⊆ {1..PR}                              |

## goal
| Statement                                                                                              |
|--------------------------------------------------------------------------------------------------------|
| (∀m∈{1..PR}. e m / E = 1 / real PR) ∧ (∑m∈A. e m) / E = real (card A) / real PR  |

## proof
| Id  | Claim                                                                            | By                                   | Using  | Method                            | Status |
|-----|----------------------------------------------------------------------------------|--------------------------------------|--------|-----------------------------------|--------|
| s1  | ∀m∈{1..PR}. e m / E = 1 / real PR                                                 | one module is 1/PR of the whole      | Epos   | (simp add: equit field_simps)     | method |
| s2a | (∑m∈A. e m) = (∑m∈A. E / real PR)                                                 | each term equal on the arbitrary k-body A ⊆ {1..PR} | — | (rule sum.cong) (use Asub equit in auto) | method |
| s2b | (∑m∈A. e m) = real (card A) * (E / real PR)                                       | sum of a constant over A             | s2a    | simp                              | method |
| s2  | (∑m∈A. e m) / E = real (card A) / real PR                                         | a k-body captures only k/PR          | s2b, Epos | simp                           | method |
| s3  | (∀m∈{1..PR}. e m / E = 1 / real PR) ∧ (∑m∈A. e m) / E = real (card A) / real PR | single-source and k-source bounds together | s1, s2 | blast | method |

# theorem DiffusenessAsymptotic
> Theorem 5 (asymptotic consequence). As PR → ∞ the k-source captured fraction k/PR → 0: no bounded-size PIC formula localises a diffuse causal property, and P⟨single-module intervention alters E⟩ = O(1/PR). Discharged: the constant numerator over a diverging denominator tends to 0.

## imports
| Theory       |
|--------------|
| Complex_Main |

## goal
| Statement                                          |
|----------------------------------------------------|
| (λn. real k / real n) \<longlonglongrightarrow> 0      |

## proof
| Id  | Claim                                          | By                                | Using | Method       | Status |
|-----|------------------------------------------------|-----------------------------------|-------|--------------|--------|
| s0  | (λn. real k / real n) \<longlonglongrightarrow> 0  | const / (real n → ∞) → 0          | —     | (rule tendsto_divide_0[OF tendsto_const filterlim_at_top_imp_at_infinity[OF filterlim_real_sequentially]]) | method |

# theorem TwoTemperatureSoundness
> Theorem 6. Read Π as a semiring FAQ. Under the tropical semiring (T=0) the aggregate is the attained max with witness argmax (greedy decode); the Maslov sandwich Max(L) ≤ T·ln Σ exp(L/T) ≤ Max(L) + T·ln|V| brings it to the log-semiring softmax aggregate (T=1) — one program, two temperatures. Both bounds are now discharged: the max term is one summand of the sum (lower), and every term is at most the max term (upper).

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name | Statement   |
|------|-------------|
| Tpos | T > 0       |
| finV | finite V    |
| neV  | V ≠ {}      |

## goal
| Statement                                                                                                                                                          |
|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| (∃u∈V. L u = Max (L ` V)) ∧ Max (L ` V) ≤ T * ln (∑v∈V. exp (L v / T)) ∧ T * ln (∑v∈V. exp (L v / T)) ≤ Max (L ` V) + T * ln (real (card V)) |

## proof
| Id         | Claim                                                                                                                                                               | By                                               | Using                      | Method                                                       | Status |
|------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------|--------------------------------------------------|----------------------------|--------------------------------------------------------------|--------|
| s_mem      | Max (L ` V) ∈ L ` V                                                  | the max is attained on the image                  | finV, neV        | (intro Max_in) auto                              | method |
| s_attained | ∃u∈V. L u = Max (L ` V)                                              | tropical aggregate = attained max (greedy decode) | s_mem            | auto                                             | method |
| s_obt      | obtain u where u ∈ V ∧ L u = Max (L ` V)                             | name the maximiser u                              | s_attained       | blast                                            | method |
| s_uV       | u ∈ V                                                                | the maximiser lies in V                           | s_obt            | simp                                             | method |
| s_Lu       | L u = Max (L ` V)                                                    | its value is the max                              | s_obt            | simp                                             | method |
| s_memle    | exp (L u / T) ≤ (∑v∈V. exp (L v / T))                                | one summand bounds the sum                        | s_uV, finV       | (intro member_le_sum) auto                       | method |
| s_lestar   | exp (Max (L ` V) / T) ≤ (∑v∈V. exp (L v / T))                        | rewrite via the max value                         | s_memle, s_Lu    | simp                                             | method |
| s_pos      | 0 < (∑v∈V. exp (L v / T))                                            | positive sum of exponentials                      | finV, neV        | (simp add: sum_pos)                              | method |
| s_key      | Max (L ` V) / T ≤ ln (∑v∈V. exp (L v / T))                           | take logs (lower)                                 | s_lestar, s_pos  | (simp add: ln_ge_iff)                            | method |
| s_lower    | Max (L ` V) ≤ T * ln (∑v∈V. exp (L v / T))                           | multiply through by T > 0                          | s_key, Tpos      | (simp add: pos_divide_le_eq mult.commute)        | method |
| s_ucard    | 0 < real (card V)                                                   | V is finite and nonempty                          | finV, neV        | (simp add: card_gt_0_iff)                        | method |
| s_ub       | ⋀v. v ∈ V ⟹ exp (L v / T) ≤ exp (Max (L ` V) / T)                   | every term is at most the max term                | finV, Tpos       | (simp add: Max_ge divide_right_mono)             | method |
| s_bound    | (∑v∈V. exp (L v / T)) ≤ real (card V) * exp (Max (L ` V) / T)        | bound the sum by card · max-term                  | s_ub             | (simp add: sum_bounded_above)                    | method |
| s_lnbound  | ln (∑v∈V. exp (L v / T)) ≤ ln (real (card V) * exp (Max (L ` V) / T)) | ln is monotone on the positives                  | s_bound, s_pos   | simp                                             | method |
| s_lnsplit  | ln (real (card V) * exp (Max (L ` V) / T)) = ln (real (card V)) + Max (L ` V) / T | split the log of a product            | s_ucard          | (simp add: ln_mult)                              | method |
| s_key2     | ln (∑v∈V. exp (L v / T)) ≤ ln (real (card V)) + Max (L ` V) / T      | combine (upper, pre-multiply)                     | s_lnbound, s_lnsplit | simp                                         | method |
| s_tmul     | T * ln (∑v∈V. exp (L v / T)) ≤ T * (ln (real (card V)) + Max (L ` V) / T) | multiply through by T > 0                     | s_key2, Tpos     | (simp add: mult_left_mono)                       | method |
| s_tsimp    | T * (ln (real (card V)) + Max (L ` V) / T) = Max (L ` V) + T * ln (real (card V)) | clear the T/T cancellation               | Tpos             | (simp add: field_simps)                          | method |
| s_upper    | T * ln (∑v∈V. exp (L v / T)) ≤ Max (L ` V) + T * ln (real (card V))  | upper Maslov bound                                | s_tmul, s_tsimp  | simp                                             | method |
| s_show     | (∃u∈V. L u = Max (L ` V)) ∧ Max (L ` V) ≤ T * ln (∑v∈V. exp (L v / T)) ∧ T * ln (∑v∈V. exp (L v / T)) ≤ Max (L ` V) + T * ln (real (card V)) | Maslov dequantization joins both temperatures    | s_attained, s_lower, s_upper | blast | method |

# theorem PropPowerDiagram
> Proposition 1. The linear regions of the max-logit M(r) are the Laguerre power diagram of {U_v} with weights (b_v, ‖U_v‖²): the power-distance difference between two sites equals −2× the score difference ⟨r,U_v⟩+b_v, so the cell of minimum power distance is exactly the argmax (predicted) token.

## imports
| Theory                     |
|----------------------------|
| HOL-Analysis.Inner_Product |

## goal
| Statement                                                                                                                                                              |
|------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| ((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w)) |

## proof
| Id  | Claim                                                                                | By                       | Using    | Method                                                                                       | Status |
|-----|-------------------------------------------------------------------------------------|--------------------------|----------|----------------------------------------------------------------------------------------------|--------|
| s1v | (norm (r - U v)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U v) + (norm (U v)) ^ 2           | polarisation at site v   | —        | (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute) | method |
| s1w | (norm (r - U w)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U w) + (norm (U w)) ^ 2           | polarisation at site w   | —        | (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute) | method |
| s2  | ((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w)) | weight ω_v = ‖U_v‖² + 2 b_v makes argmin-power = argmax-score | s1v, s1w | (simp add: algebra_simps) | method |

# theorem PropMarginDistance
> Proposition 2. The normalised margin (L_t − L_{v*})/‖U_t − U_{v*}‖ is the exact signed Euclidean distance from r to the t–v* facet of the tropical hypersurface: the numerator ⟨r, U_t − U_{v*}⟩ + (b_t − b_{v*}) equals L_t − L_{v*} = Δ, and dividing by ‖U_t − U_{v*}‖ gives the point-to-bisector distance.

## imports
| Theory                     |
|----------------------------|
| HOL-Analysis.Inner_Product |

## goal
| Statement                                                                                                                                                       |
|-----------------------------------------------------------------------------------------------------------------------------------------------------------------|
| (inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar)              |

## proof
| Id  | Claim                                                              | By                              | Using | Method                       | Status |
|-----|-------------------------------------------------------------------|---------------------------------|-------|------------------------------|--------|
| s1  | inner r (U t - U vstar) = inner r (U t) - inner r (U vstar)        | linearity of the inner product  | —     | (simp add: inner_diff_right) | method |
| s2  | (inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar) | the facet numerator is Δ; divide by ‖U_t − U_{v*}‖ | s1 | (simp add: algebra_simps) | method |
