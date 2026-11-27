# Student formal: definitions and lemmas for a sparse, discretised, clamped model (kernel-checked)

Statements about the mathematical definitions behind a sparse discretised "student" of a host model.
The proofs live in the three Isabelle theories next to this file and were accepted by the Isabelle
kernel (Isabelle2025-2, no `sorry`, no `quick_and_dirty`). This file is the readable surface.

**What this is not.** Nothing here says a training run finds the right structure, and nothing here
certifies that a trained student computes its host's function. Those stay `empirical`. The clamp
constants are taken from the host, so the clamp results are about the structure of the model, not
about whether a particular mask is the right one.

# theorem LevelStable
> A latent value that is at least δ away from every level threshold keeps its level under any perturbation smaller than δ.

## imports
| Theory         |
|----------------|
| Quantiser_Levels |

## goal
| Statement |
|-----------|
| (∀t∈set th. δ ≤ ¦c - t¦) ⟹ ¦c' - c¦ < δ ⟹ level th c' = level th c |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | (∀t∈set th. δ ≤ ¦c - t¦) ⟹ ¦c' - c¦ < δ ⟹ level th c' = level th c | a latent at least delta from every threshold keeps its level | — | (auto intro: level_stable) | method |

# theorem MarginPreventsLevelChange
> If the margin penalty of a code is zero (it is at least w·sp from every threshold), no perturbation smaller than w·sp changes its level.

## imports
| Theory         |
|----------------|
| Quantiser_Levels |

## goal
| Statement |
|-----------|
| th ≠ [] ⟹ 0 < sp ⟹ margin_pen w sp th c = 0 ⟹ ¦c' - c¦ < w * sp ⟹ level th c' = level th c |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | th ≠ [] ⟹ 0 < sp ⟹ margin_pen w sp th c = 0 ⟹ ¦c' - c¦ < w * sp ⟹ level th c' = level th c | zero margin penalty means distance at least w*sp from every threshold | — | (rule margin_prevents_level_change) | method |

# theorem ArbitrarilySmallFlip
> A code exactly on a threshold changes level under an arbitrarily small step, which is why proximity to a threshold matters and why the margin cannot stop large jumps.

## imports
| Theory         |
|----------------|
| Quantiser_Levels |

## goal
| Statement |
|-----------|
| t ∈ set th ⟹ 0 < ε ⟹ ∃c'. ¦c' - t¦ < ε ∧ level th c' ≠ level th t |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | t ∈ set th ⟹ 0 < ε ⟹ ∃c'. ¦c' - t¦ < ε ∧ level th c' ≠ level th t | on a threshold, any positive step flips the level | — | (rule arbitrarily_small_flip) | method |

# theorem QuantInValues
> The quantiser has finitely many output values: one per level, taken from the list of level values.

## imports
| Theory         |
|----------------|
| Quantiser_Levels |

## goal
| Statement |
|-----------|
| length vb = Suc (length th) ⟹ quant vb th c ∈ set vb |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | length vb = Suc (length th) ⟹ quant vb th c ∈ set vb | level index is below the number of values | — | (rule quant_in_values) | method |

# theorem TopkCodeSparse
> A code that keeps a top-k index set has at most k nonzero entries.

## imports
| Theory         |
|----------------|
| Sparse_TopK |

## goal
| Statement |
|-----------|
| is_topk k z S ⟹ finite {i. keep_code S z i ≠ 0} ∧ card {i. keep_code S z i ≠ 0} ≤ k |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | is_topk k z S ⟹ finite {i. keep_code S z i ≠ 0} ∧ card {i. keep_code S z i ≠ 0} ≤ k | support is inside the kept set of at most k entries | — | (auto intro: topk_code_sparse) | method |

# theorem ClampedNodesIrrelevant
> C1. With a set C of nodes clamped to constants, the model's output does not depend on the internal computation of any clamped node.

## imports
| Theory         |
|----------------|
| Node_Mask_Clamp |

## goal
| Statement |
|-----------|
| (∀n∈set order. n ∉ C ⟶ mech1 n = mech2 n) ⟹ eval mech1 order rd d x (clamp_ov C μ ov0) = eval mech2 order rd d x (clamp_ov C μ ov0) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | (∀n∈set order. n ∉ C ⟶ mech1 n = mech2 n) ⟹ eval mech1 order rd d x (clamp_ov C μ ov0) = eval mech2 order rd d x (clamp_ov C μ ov0) | overridden nodes never read their own mechanism | — | (auto intro: clamped_nodes_irrelevant) | method |

# theorem ClampedSwapNoop
> C2. Swapping clamped nodes is a no-op, so a clamped node's interchange score is null by construction.

## imports
| Theory         |
|----------------|
| Node_Mask_Clamp |

## goal
| Statement |
|-----------|
| S ⊆ C ⟹ S ⊆ set order ⟹ eval mech order rd d a (swap_ov mech order d S b (clamp_ov C μ ov0)) = eval mech order rd d a (clamp_ov C μ ov0) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | S ⊆ C ⟹ S ⊆ set order ⟹ eval mech order rd d a (swap_ov mech order d S b (clamp_ov C μ ov0)) = eval mech order rd d a (clamp_ov C μ ov0) | a clamped node already holds the constant a swap would write | — | (rule clamped_swap_noop) | method |

# theorem ClampCostBound
> C3. If the student agrees with the clamped host on a set of inputs and the clamped host differs from the host on at most e inputs, the student agrees with the host on at least that many minus e. With e = 0 the clamp is lossless.

## imports
| Theory         |
|----------------|
| Node_Mask_Clamp |

## goal
| Statement |
|-----------|
| finite D ⟹ card {x∈D. f x = g x} - card {x∈D. g x ≠ h x} ≤ card {x∈D. f x = h x} |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | finite D ⟹ card {x∈D. f x = g x} - card {x∈D. g x ≠ h x} ≤ card {x∈D. f x = h x} | agreement is transitive up to the count of disagreements | — | (rule clamp_cost_bound) | method |

# theorem SingleInertJointNot
> C4. Two duplicate nodes: ablating either one alone changes nothing, ablating both changes the output. A single-node inertness screen can therefore clamp both members of a redundant pair.

## imports
| Theory         |
|----------------|
| Node_Mask_Clamp |

## goal
| Statement |
|-----------|
| (∀x. dup_eval x (ablate {False}) = dup_eval x (λ_. None)) ∧ (∀x. dup_eval x (ablate {True}) = dup_eval x (λ_. None)) ∧ ¬ (∀x. dup_eval x (ablate {False, True}) = dup_eval x (λ_. None)) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | (∀x. dup_eval x (ablate {False}) = dup_eval x (λ_. None)) ∧ (∀x. dup_eval x (ablate {True}) = dup_eval x (λ_. None)) ∧ ¬ (∀x. dup_eval x (ablate {False, True}) = dup_eval x (λ_. None)) | duplicate nodes: each alone is redundant, both together are not | — | (auto simp: single_inert_joint_not) | method |

# theorem SingleSwapsNotEnough
> P1. A student can match the host on the plain output and on every single-node swap and still differ on a swap of two nodes (four duplicated copies; host true when at least two are true, student when at least three).

## imports
| Theory |
|--------|
| Swap_Probe_Identifiability |

## goal
| Statement |
|-----------|
| (∀x. out4 rd_host x (λ_. None) = out4 rd_stud x (λ_. None)) ∧ (∀n a b. swap4 rd_host {n} a b = swap4 rd_stud {n} a b) ∧ (∃a b. swap4 rd_host {N0, N1} a b ≠ swap4 rd_stud {N0, N1} a b) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | (∀x. out4 rd_host x (λ_. None) = out4 rd_stud x (λ_. None)) ∧ (∀n a b. swap4 rd_host {n} a b = swap4 rd_stud {n} a b) ∧ (∃a b. swap4 rd_host {N0, N1} a b ≠ swap4 rd_stud {N0, N1} a b) | single-swap agreement does not control a pair swap | — | (intro conjI single_swaps_not_enough(1) single_swaps_not_enough(2) single_swaps_not_enough(3)) | method |

# theorem ValidMasksNotUnique
> P2. On a host with a redundant pair of nodes, each member alone is a maximal valid clamp set, so valid masks are not unique and the set of all single-node-inert nodes is not itself inert.

## imports
| Theory |
|--------|
| Swap_Probe_Identifiability |

## goal
| Statement |
|-----------|
| inert_dup {False} ∧ inert_dup {True} ∧ ¬ inert_dup {False, True} ∧ (∀C. {False} ⊂ C ⟶ ¬ inert_dup C) ∧ (∀C. {True} ⊂ C ⟶ ¬ inert_dup C) ∧ {False} ≠ {True} |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | inert_dup {False} ∧ inert_dup {True} ∧ ¬ inert_dup {False, True} ∧ (∀C. {False} ⊂ C ⟶ ¬ inert_dup C) ∧ (∀C. {True} ⊂ C ⟶ ¬ inert_dup C) ∧ {False} ≠ {True} | each member of the pair is a maximal inert clamp; the two are different | — | (auto simp: valid_masks_not_unique) | method |

# theorem SingleScreenMaskNotInert
> P2 corollary. The mask chosen by a single-node ablation screen on the redundant host contains both members and is not inert.

## imports
| Theory |
|--------|
| Swap_Probe_Identifiability |

## goal
| Statement |
|-----------|
| {n. inert_dup {n}} = {False, True} ∧ ¬ inert_dup {n. inert_dup {n}} |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | {n. inert_dup {n}} = {False, True} ∧ ¬ inert_dup {n. inert_dup {n}} | the screen selects both nodes and that set is not inert | — | (intro conjI single_screen_mask_not_inert(1) single_screen_mask_not_inert(2)) | method |

# theorem ClampBreaksSwapEquivalence
> P3. On the redundant host, a student built from the host mechanisms by clamping a set C to constants that matches the plain output and the single-node swaps of every free node must have C empty. The swap criterion forces both redundant copies to stay.

## imports
| Theory |
|--------|
| Swap_Probe_Identifiability |

## goal
| Statement |
|-----------|
| (∀x. dup_eval x (clamp_ov C μ (λ_. None)) = dup_eval x (λ_. None)) ⟹ (∀n. n ∉ C ⟶ (∀a b. dup_swap {n} a b (clamp_ov C μ (λ_. None)) = dup_swap {n} a b (λ_. None))) ⟹ C = {} |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | (∀x. dup_eval x (clamp_ov C μ (λ_. None)) = dup_eval x (λ_. None)) ⟹ (∀n. n ∉ C ⟶ (∀a b. dup_swap {n} a b (clamp_ov C μ (λ_. None)) = dup_swap {n} a b (λ_. None))) ⟹ C = {} | any clamp breaks plain or swap equivalence on this host | — | (rule clamp_breaks_swap_equivalence) | method |

# theorem SwapBehavioursLeNodeValues
> Cap1. If a student matches a host under every single-node swap of node n over a finite domain, the student node must take at least as many distinct values as the host node has distinct swap behaviours.

## imports
| Theory |
|--------|
| Capacity_Counting |

## goal
| Statement |
|-----------|
| finite D ⟹ (⋀b. b ∈ D ⟹ swap_row mech1 order1 rd1 d1 n ov1 b = swap_row mech2 order2 rd2 d2 n ov2 b) ⟹ card (swap_row mech1 order1 rd1 d1 n ov1 ` D) ≤ card ((λb. nodeval mech2 order2 d2 b ov2 n) ` D) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | finite D ⟹ (⋀b. b ∈ D ⟹ swap_row mech1 order1 rd1 d1 n ov1 b = swap_row mech2 order2 rd2 d2 n ov2 b) ⟹ card (swap_row mech1 order1 rd1 d1 n ov1 ` D) ≤ card ((λb. nodeval mech2 order2 d2 b ov2 n) ` D) | node values bound swap behaviours | — | (rule swap_behaviours_le_node_values) | method |

# theorem CardSparseCodesGe
> Cap2a. A sparse discrete site with dictionary size D, k active latents and L levels has at least (D choose k) * L^k codes.

## imports
| Theory |
|--------|
| Capacity_Counting |

## goal
| Statement |
|-----------|
| (D choose k) * L ^ k ≤ card (sparse_codes D k L) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | (D choose k) * L ^ k ≤ card (sparse_codes D k L) | count codes with exactly k active latents | — | (rule card_sparse_codes_ge) | method |

# theorem CardSparseCodesLe
> Cap2b. It has at most (number of supports of size at most k) * L^k codes.

## imports
| Theory |
|--------|
| Capacity_Counting |

## goal
| Statement |
|-----------|
| 0 < L ⟹ card (sparse_codes D k L) ≤ card (sparse_supports D k) * L ^ k |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | 0 < L ⟹ card (sparse_codes D k L) ≤ card (sparse_supports D k) * L ^ k | each support carries at most L^k level choices | — | (rule card_sparse_codes_le) | method |

# theorem CapacityNecessary
> Cap3. Necessary condition: exact single-node swap equivalence forces the number of host swap behaviours to be at most the number of codes of the student site.

## imports
| Theory |
|--------|
| Capacity_Counting |

## goal
| Statement |
|-----------|
| finite D ⟹ (⋀b. b ∈ D ⟹ swap_row mech1 order1 rd1 d1 n ov1 b = swap_row mech2 order2 rd2 d2 n ov2 b) ⟹ (⋀b. b ∈ D ⟹ enc b ∈ sparse_codes Dsz k L) ⟹ (⋀b. b ∈ D ⟹ nodeval mech2 order2 d2 b ov2 n = dec (enc b)) ⟹ card (swap_row mech1 order1 rd1 d1 n ov1 ` D) ≤ card (sparse_codes Dsz k L) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | finite D ⟹ (⋀b. b ∈ D ⟹ swap_row mech1 order1 rd1 d1 n ov1 b = swap_row mech2 order2 rd2 d2 n ov2 b) ⟹ (⋀b. b ∈ D ⟹ enc b ∈ sparse_codes Dsz k L) ⟹ (⋀b. b ∈ D ⟹ nodeval mech2 order2 d2 b ov2 n = dec (enc b)) ⟹ card (swap_row mech1 order1 rd1 d1 n ov1 ` D) ≤ card (sparse_codes Dsz k L) | chain Cap1 with the code count | — | (rule capacity_necessary) | method |

# theorem CapacityNotBinding
> Cap4. At dictionary size 64, 8 active latents and 10 levels the condition holds for any set of up to 10^15 behaviours, so counting capacity is not the obstruction on finite evaluation sets of the sizes in use.

## imports
| Theory |
|--------|
| Capacity_Counting |

## goal
| Statement |
|-----------|
| m ≤ 10 ^ 15 ⟹ m ≤ card (sparse_codes 64 8 10) |

## proof
| Id | Claim | By | Using | Method | Status |
|----|-------|----|-------|--------|--------|
| s_show | m ≤ 10 ^ 15 ⟹ m ≤ card (sparse_codes 64 8 10) | lower bound (8^8) * 10^8 on the code count | — | (rule capacity_not_binding_64_8_10) | method |
