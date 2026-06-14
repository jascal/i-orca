/-
  Lean 4 skeleton — STRUCTURE ONLY (SPEC §6.Lean, §11.4).
  Propositions are carried verbatim from i-orca in HOL syntax; they do not
  parse as Lean and every method is a hole. This transfers the proof SHAPE,
  not the proof. Re-state each claim in Lean/Mathlib syntax to make it real.
-/
-- isabelle imports: HOL-Analysis.Inner_Product

-- context (assumed facts):
--   ut : norm (U t) = 1
--   uv : norm (U v) = 1
-- goal: (norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v)) ∧ (inner (U t) (U v) = 0 ⟶ (norm (U t - U v)) ^ 2 = 2)
-- proof DAG (id  [status]  using → claim):
--   s1  [method]  · → (norm (U t - U v)) ^ 2 = (norm (U t)) ^ 2 - 2 * inner (U t) (U v) + (norm (U v)) ^ 2
--   s2  [method]  using s1 → (norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v))
--   s3  [method]  using s2 → (norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v)) ∧ (inner (U t) (U v) = 0 ⟶ (norm (U t - U v)) ^ 2 = 2)

theorem nonTruthFunctionalityBudget : True := by
  trivial

