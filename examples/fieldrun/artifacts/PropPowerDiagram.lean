/-
  Lean 4 skeleton — STRUCTURE ONLY (SPEC §6.Lean, §11.4).
  Propositions are carried verbatim from i-orca in HOL syntax; they do not
  parse as Lean and every method is a hole. This transfers the proof SHAPE,
  not the proof. Re-state each claim in Lean/Mathlib syntax to make it real.
-/
-- isabelle imports: HOL-Analysis.Inner_Product

-- goal: ((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w))
-- proof DAG (id  [status]  using → claim):
--   s1v  [method]  · → (norm (r - U v)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U v) + (norm (U v)) ^ 2
--   s1w  [method]  · → (norm (r - U w)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U w) + (norm (U w)) ^ 2
--   s2  [method]  using s1v,s1w → ((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w))

theorem propPowerDiagram : True := by
  trivial

