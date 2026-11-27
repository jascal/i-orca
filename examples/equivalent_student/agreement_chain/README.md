# Agreement chain (Isabelle, kernel-checked)
Written 2026-11-23 by observer session code-22 at the user's request ("work on proving the additional step"). Own session so it
does not touch Student_Formal or code-da's Swap_Bounds. Labels (proved / empirical / open) as in ../../GLOSSARY.md. Measurement:
../certificate/R1_HYPOTHESIS_CHECK.md.

## Status
`proved`: Isabelle2025-2, session `Agreement_Chain`, no sorry. 9 of 9 statements show 0 oracles and 0 hypotheses (check session
with a negative control that shows 1 oracle). About the definitions here; not a check of any training or scoring script.

## The question
code-da's R1 (../swap_bounds, Rounding_Margin) proves rounding keeps the CONTINUOUS student's top answer. To reach the HOST's
answer one more premise is needed at each position, "link 1": the continuous student's top answer is the host's. Link 1 is a
property of trained weights. The students measured here fail it at 13.5% of sampled decisive positions, so no theorem "this recipe
gives link 1" holds for them; whether another objective could guarantee it is `open`. It can be shown by exhaustion on a finite
input set (done for the rounded case-14 students by ../certificate, as certified numerics over a trusted base, not a kernel proof)
or estimated on a sample (pythia-14m, measured here).

## Statements
- `top_unique`: a function has at most one unique top answer.
- `sup_implies_spread`: if every logit moves by at most E, no two logits move apart by more than 2E.
- `spread_top_kept` (sharper than R1): if no two logits move apart by more than B and the continuous student ranks i first by at
  least m > B, the rounded student's top answer is i. Shift-invariant: a common shift cannot change a top answer.
- `sup_top_kept`: R1's uniform version (2E < m) as a corollary, without the Lipschitz layer.
- `rounded_top_is_host_top`: the chain. Host top i, link 1 (continuous margin m at i), spread bound B < m, then any top answer of the
  rounded student equals i.
- `certified_count_le_agree`: on a finite set of positions the count where link 1 and the margin test hold is a lower bound on the
  agreement count.
- `shift_example_*`: the sup-norm test is not necessary (a common shift of 5 with margin 1 keeps the top; any sup-norm bound is at
  least 5), and the spread test is strictly sharper.

## Not covered
Link 1 itself; any Lipschitz constant for a trained model (code-da's `lip` hypothesis); the training steps.

## Rebuild
    cd /home/allans/code/student-lab/formal/agreement_chain
    nice -n 10 isabelle build -j 1 -o threads=1 -D .
(no -f: it would also rebuild the HOL base heap, which cost a GPU queue on 2026-11-23)
