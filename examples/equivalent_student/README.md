# Equivalent student — i-orca corpus

Kernel-checked statements behind the **equivalent-student** study (Nov 2026). That study distilled
transformer hosts (InterpBench planted-circuit models, pythia-14m, pythia-70m) into sparse, discrete
"students" whose outputs, and ideally whose internal nodes under interchange ("swap") interventions,
match the host. The study's code and findings live in the `equivalent-student` repo (local, not
published). This corpus holds only the mathematics, which stands on its own.

Every statement is about the definitions written in these theories. They mirror the trainer's
quantiser, TopK, clamp and swap operations, but **nothing here is checked against the training code**,
and nothing says that a trained student is faithful. That is an empirical question.

## Sessions

| Session | Dir | Says |
|---|---|---|
| `Student_Formal` | `.` | Quantiser levels: a code at least δ from every threshold keeps its level, and a zero margin penalty means perturbations below w·sp cannot change a level (`Quantiser_Levels`). A TopK code has at most k nonzeros (`Sparse_TopK`). Clamp/mask facts: a clamped node's computation does not reach the output, swapping a clamped node is a no-op, a counting bound on clamp cost, and two duplicate nodes that are each inert alone but not together (`Node_Mask_Clamp`). What swap tests can identify: matching every single-node swap does not imply matching a two-node swap, and on a redundant pair the ablation screen's mask is not inert (`Swap_Probe_Identifiability`). Capacity counting: exact single-node swap equivalence forces at least as many distinct student values as host swap behaviours, plus code-count bounds for a sparse discrete site, and two corollaries showing the condition does not bind at the study's operating points: D 64, k 8, L 10 (toy hosts, at least 10^15 codes) and D 1024, k 32, L 40 (pythia-14m, at least 10^99) (`Capacity_Counting`). |
| `Swap_Bounds` | `swap_bounds/` | Swap-score triangle bounds, the no-op floor, Lipschitz top-answer preservation and rounding-margin bounds that connect continuous and discrete students. |
| `Agreement_Chain` | `agreement_chain/` | If the host's top answer is i, the continuous student ranks i first by a margin m ("link 1", a premise), and rounding moves no two logits apart by more than B < m, then the rounded student's top answer is i. Link 1 is a property of trained weights; it is a premise here, not proved. |
| `Certificate_Decision` | `certificate_decision/` | Soundness of the decision logic of the interval/ball output certificate: given enclosures that contain the true logits, "certified agree", "certified disagree" and "undecided" are reported correctly. |
| `Check_Certificate_Decision` | `certificate_decision/check_oracles/` | Fails the build if any `Certificate_Decision_Soundness` theorem depends on an oracle (`sorry`, `quick_and_dirty`, evaluation). |

`student_formal.i.orca.md` is the readable i-orca surface for `Student_Formal` (18 theorem blocks;
`i-orca check` gave formal_fraction_real 1.000 on each when it was written).

## Related corpora

These sessions import only HOL; nothing here depends on another corpus, but several sit close to one:
- [`../provable_opt/`](../provable_opt): PO-T3's margin-certified decode invariance is the same "margin beats
  perturbation, so the top answer is kept" argument as `Rounding_Margin` and `Agreement_Chain`, applied there to
  a Datalog transform.
- [`../pic_core/`](../pic_core) (`PIC_Cleanup.thy`, T6(a)): a linear projection preserves every decision margin
  iff it fixes every readout difference. That is the exact counterpart of the spread bound used here, which only
  bounds the differences.
- [`../recoverability/`](../recoverability) and [`../superposition/`](../superposition): capacity questions for
  SAE-style dictionaries. `Capacity_Counting` is a counting bound on code space, not a geometric one.

`Certificate_Decision_Soundness.thy` restates some quantiser-level lemmas from `Quantiser_Levels.thy` so that the
session stands alone. A shared level theory would remove the copy if the two sessions start to evolve together.

## Status

`proved` over the stated definitions: all five sessions build under Isabelle2025-2, no `sorry`, no
`quick_and_dirty`, and the oracle check passes.

    isabelle build -D examples/equivalent_student     # about 20 s, 4 GB peak RSS

**Not proved:** the training steps; that learned gates find the right mask; any model-level
equivalence. The certificate that checks trained students numerically (interval and Arb balls over
a finite domain) is certified numerics over a trusted base (IEEE double, python-flint/Arb). It is not
a kernel proof, and it lives in the study repo.

The sub-folder READMEs are copied from the study repo. Their relative links (`../../GLOSSARY.md`,
`../certificate/...`) point into that repo and do not resolve here.

Build note: command-line builds reject Unicode cartouches and symbols in `.thy` files, so these
theories use the ASCII forms (`\<open>`, `\<Longrightarrow>`).
