/-
  Lean 4 skeleton — STRUCTURE ONLY (SPEC §6.Lean, §11.4).
  Propositions are carried verbatim from i-orca in HOL syntax; they do not
  parse as Lean and every method is a hole. This transfers the proof SHAPE,
  not the proof. Re-state each claim in Lean/Mathlib syntax to make it real.
-/
-- isabelle imports: Complex_Main

-- context (assumed facts):
--   c3_def : ⋀j v. c3 (j::nat) (v::nat) = (if j = 1 then (if v = 0 then (2::real) else if v = 1 then 3 else 0) else if j = 2 then (if v = 0 then 2 else if v = 1 then 0 else 3) else (if v = 0 then 0 else 1/2))
-- goal: (∀j∈{1,2,3}. ¬ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{j}. c3 i v) < (∑i∈{j}. c3 i 0))) ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{1,2,3}. c3 i v) < (∑i∈{1,2,3}. c3 i 0)) ∧ (∃P. P ≠ {} ∧ P ⊂ {1,2,3} ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈P. c3 i v) < (∑i∈P. c3 i 0)))
-- proof DAG (id  [status]  using → claim):
--   s_mu0  [method]  · → ∀j∈{1,2,3}. ¬ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{j}. c3 i v) < (∑i∈{j}. c3 i 0))
--   s_dec  [method]  · → ∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{1,2,3}. c3 i v) < (∑i∈{1,2,3}. c3 i 0)
--   s_suff  [method]  · → ∃P. P ≠ {} ∧ P ⊂ {1,2,3} ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈P. c3 i v) < (∑i∈P. c3 i 0))
--   s_show  [method]  using s_mu0,s_dec,s_suff → (∀j∈{1,2,3}. ¬ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{j}. c3 i v) < (∑i∈{j}. c3 i 0))) ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈{1,2,3}. c3 i v) < (∑i∈{1,2,3}. c3 i 0)) ∧ (∃P. P ≠ {} ∧ P ⊂ {1,2,3} ∧ (∀v∈{0,1,2}. v ≠ 0 ⟶ (∑i∈P. c3 i v) < (∑i∈P. c3 i 0)))

theorem muZeroDoesNotImplyIrreducible : True := by
  trivial

