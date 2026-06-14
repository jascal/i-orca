/-
  Lean 4 skeleton — STRUCTURE ONLY (SPEC §6.Lean, §11.4).
  Propositions are carried verbatim from i-orca in HOL syntax; they do not
  parse as Lean and every method is a hole. This transfers the proof SHAPE,
  not the proof. Re-state each claim in Lean/Mathlib syntax to make it real.
-/
-- isabelle imports: Complex_Main

-- context (assumed facts):
--   c1_def : c1 = (λx::nat. if x = 0 then (2::real) else if x = 1 then 3 else 0)
--   c2_def : c2 = (λx::nat. if x = 0 then (2::real) else if x = 1 then 0 else 3)
--   L_def : L = (λx. c1 x + c2 x)
-- goal: L 0 > L 1 ∧ L 0 > L 2 ∧ c1 1 > c1 0 ∧ c2 2 > c2 0
-- proof DAG (id  [status]  using → claim):
--   s1  [method]  · → L 0 = 4 ∧ L 1 = 3 ∧ L 2 = 3
--   s2  [method]  · → c1 1 > c1 0 ∧ c2 2 > c2 0
--   s3  [method]  using s1,s2 → L 0 > L 1 ∧ L 0 > L 2 ∧ c1 1 > c1 0 ∧ c2 2 > c2 0

theorem weightedThresholdExpressivity : True := by
  trivial

