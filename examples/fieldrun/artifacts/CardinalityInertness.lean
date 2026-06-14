/-
  Lean 4 skeleton — STRUCTURE ONLY (SPEC §6.Lean, §11.4).
  Propositions are carried verbatim from i-orca in HOL syntax; they do not
  parse as Lean and every method is a hole. This transfers the proof SHAPE,
  not the proof. Re-state each claim in Lean/Mathlib syntax to make it real.
-/
-- isabelle imports: Main

-- context (assumed facts):
--   eqtot : ⋀v. (∑j∈J. c j v) = (∑j∈J. c' j v)
-- goal: (∀w∈V. (∑j∈J. c j w) ≤ (∑j∈J. c j t)) = (∀w∈V. (∑j∈J. c' j w) ≤ (∑j∈J. c' j t))
-- proof DAG (id  [status]  using → claim):
--   s_tot  [method]  using eqtot → ⋀w. (∑j∈J. c j w) = (∑j∈J. c' j w)
--   s_dec  [method]  using s_tot → (∀w∈V. (∑j∈J. c j w) ≤ (∑j∈J. c j t)) = (∀w∈V. (∑j∈J. c' j w) ≤ (∑j∈J. c' j t))

theorem cardinalityInertness : True := by
  trivial

