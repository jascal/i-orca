/-
  Lean 4 skeleton — STRUCTURE ONLY (SPEC §6.Lean, §11.4).
  Propositions are carried verbatim from i-orca in HOL syntax; they do not
  parse as Lean and every method is a hole. This transfers the proof SHAPE,
  not the proof. Re-state each claim in Lean/Mathlib syntax to make it real.
-/
-- isabelle imports: HOL-Analysis.Inner_Product

-- goal: (inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar)
-- proof DAG (id  [status]  using → claim):
--   s1  [method]  · → inner r (U t - U vstar) = inner r (U t) - inner r (U vstar)
--   s2  [method]  using s1 → (inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar)

theorem propMarginDistance : True := by
  trivial

