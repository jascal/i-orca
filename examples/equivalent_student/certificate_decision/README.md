# Soundness of the certificate's decision logic (Isabelle, kernel-checked)

Filed 2026-11-24 at the user's request. The problem statement was sent to Fable (advisor agent), which returned a first theory
text; this session compiled it and repaired the proofs (tactics and two helper lemmas only, no statement changed). Labels
(proved / empirical / open) as in ../../GLOSSARY.md. Context: ../certificate/RESULTS.md and ../certificate/certify_student.py.

## Status
`proved` (Isabelle2025-2, session `Certificate_Decision`, no `sorry`, no `quick_and_dirty`): 74 theorems in the theory, **0 oracles**.
The oracle check (`check_oracles/`) collects every theorem of the theory and asks Isabelle for the oracles each depends on; a
negative control (one `sorry` under `quick_and_dirty`) reported exactly 1 oracle (`Pure.skip_proof`), so the check can see an
unproved step.

The statements are about the definitions in the theory. They are **not** a check of `certify_student.py`. Whether the Python
computes this specification is `open` (Fable read the code against the specification and found no divergence; nothing was run).

## What is proved
Model: a site keeps the top k of the POSITIVE pre-activations (ReLU then TopK, any tie-break, stated as the relation
`valid_support`), and each kept latent contributes the level value of its pre-activation (`level` counts thresholds strictly
below, as in ../Quantiser_Levels.thy).

Part A, the three checks of `decide_site` are sound:
- `valid_support_exists`: every pre-activation vector has a valid support (so nothing below is vacuous).
- `support_unique`: if a box passes the support checks (every selected lower bound positive; every other upper bound at most 0 or,
  when k are selected, strictly below every selected lower bound), the valid support of any point in the box is exactly the
  selected set, for every tie-break.
- `site_sound`: additionally, if no level threshold lies inside the box for any selected latent, the exact site code at any point
  of the box equals the certified code computed from the lower bounds.

Part B, the exact robustness radius of a decision (support plus levels), for an open eps-ball of sup-norm perturbations:
- `robust_iff_stable_cond`: for any valid support, the decision record is unchanged by every perturbation (and every valid
  support of the perturbed point) if and only if eps is at most each of: every selected value; the distance of each selected
  value to each of its thresholds; (when k are selected) half of each gap between a selected and an unselected RAW pre-activation;
  (when fewer than k are selected) the distance of each unselected value to 0.
- `robust_iff_le_rho`: the same as `eps <= Min` of a finite constraint set, when that set is non-empty (it is empty when k = 0).
- `stable_sufficient`, `stable_necessary` (the two directions) and `break_margin`, `break_level`, `break_zero`, `break_gap`
  (an explicit perturbation inside the ball that changes the decision whenever one constraint is violated).

Part C, composition through the sites, as the locale `certified_run` (per-site k, thresholds and level values; a position index):
- `code_agree`, `run_sound`, `certified_codes`: if every site check passes along the abstract run, every exact code equals the
  certified code and the exact residual stays inside the abstract one.
- `verdict_sound`: a certified top class of the host and of the student implies the exact argmaxes are those classes; so a
  certified "agree" means the exact top-1 answers coincide and a certified "disagree" means they differ, for any argmax tie-break.

## Corrections to the problem as first posed (Fable)
The gap in Part B is on the RAW pre-activation, not the ReLU'd one (z_i = 1, z_j = -3 has radius 1, not 0.5). The radius is
stated as a predicate because it is infinite when k = 0. Uniqueness of the support is not needed.

## Hypotheses, not oracles
The locale `certified_run` assumes `pre_sound`, `upd_sound`, `readout_sound` and `sel_valid`: the enclosure primitives (matmul, exp,
GELU, softmax, and the real-versus-float model) are NOT proved here. The result is "if the interval primitives enclose, the decision
logic is sound". `thm_oracles` does not list these; they are visible assumptions of the locale theorems.

## Not covered, and risks found by the audit (read, not run)
Ranked by how much they could invalidate a certified result:
1. Float32 gap (largest). The certified object is the real-arithmetic student with float64-promoted parameters; the deployed float32
   forward can take a different discrete decision where a margin is below float32 error. Part B's radius is the quantity to bound it;
   nothing does so yet.
2. `decide_site` returns a code even when its check fails and the run continues. Soundness depends on the per-sequence `bad` flag
   being applied to the whole sequence (it is). A per-position relaxation would be unsound before the last attention layer, because
   attention is bidirectional.
3. Clamped MLP sites are skipped, not checked. Sound only because their output is fully replaced; a partial clamp would break it.
4. The "decisive" test uses libm `np.exp`; it only gates the decisive label, never agree or disagree.
5. A negative k from the arguments would change a slice silently. Unvalidated.
`open`, cheap, empirical: a differential test of `decide_site` against the exact semantics on random boxes.

## Rebuild and check
    cd /home/allans/code/student-lab/formal/certificate_decision
    nice -n 10 isabelle build -j 1 -o threads=1 -D .
    nice -n 10 isabelle build -j 1 -o threads=1 -d . -D check_oracles
The second command FAILS if any theorem of the theory depends on an oracle (or if no theorem is found). Do not use `-f`: it also
rebuilds the HOL base heap (about 8 minutes, java 4 GB), which once tripped the low-memory guard and killed a GPU queue.

## Gotchas found while compiling (Isabelle2025-2)
- `linarith` does not distribute division over a subtraction: `e <= (a - b) / 2` is not used (a goal with `a / 2` is fine). Use `argo`
  there, or clear the division first. `argo` does not handle `nat`; keep `linarith` for those.
- Applying a lemma with a pattern like `?z ?i` through `OF` raised "multiple unifiers"; instantiate with `[where ... , OF ...]`.
- `thm_oracles` prints nothing in a batch log; the check session therefore writes its verdict by failing the build.
