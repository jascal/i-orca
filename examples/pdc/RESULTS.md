# R0 result, 2026-10-24

**Proved.** Isabelle2025-2 accepted `PDC_Derive.thy` in session `PDC`, parent
`PIC_Core`, with `quick_and_dirty = false` and zero proof holes.

Command from workspace root:

```sh
isabelle build -o timeout=40 -d i-orca/examples/pic_core -D i-orca/examples/pdc
```

Exit 0; `Finished PDC (0:00:01 elapsed time)`, total 0:00:07.
The README lists every theorem and its precise scope. No model was evaluated.
At that build R0 closed; later empirical gates are tracked in fieldrun/pil. This is a theorem about the stated
translation, not a claim that trained transformers implement a PDC chart.

## R4 kernel packaging, 2026-10-24

The same strict command now builds `PDC_Admission.thy` too, exit 0,
`Finished PDC (0:00:02 elapsed time)`, total 0:00:09.
Three lemmas package the existing PIC margin certificate:

- `admitted_source_preserves_decision`: offset-centered score perturbations.
- `pic.crystallization_admitted_write`: an admitted residual write preserves
  the coalition's decision under that bound.
- `pic.crystallization_complement_certified`: the omitted-source form of the
  PDC rule, with disjoint finite coalitions partitioning the full source set.

Every bound includes the target and all rivals in one unchanged candidate set.
The coalition margin is strictly above gamma, which is strictly above 2delta.
The runtime oracle checks these same inequalities. These are kernel theorems
about those premises; solver success on concrete data is separate evidence.

## R5 pairwise packaging, 2026-10-24

`pairwise_source_preserves_decision` passes the same strict session build,
exit 0, `Finished PDC (0:00:02 elapsed time)`, total 0:00:07.
It proves a candidate-wise guard: for every rival, the coalition gap exceeds
the absolute difference between the source/coalition errors at target and
rival. This covers common offsets without introducing a uniform global
perturbation radius. It says nothing about truth in an external theory.
