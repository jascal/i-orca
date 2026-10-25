# PDC: the finite derive stratum

`PDC_Derive.thy` formalizes R0 of the workspace PDC program. Its parent is
`PIC_Core`; it imports the existing PIC definitions, rather than a parallel logit.
The session disables `quick_and_dirty`. No external theory is interpreted.

Bodies have distinct identifiers and real, temperature-independent scores. Thus
two bodies of equal score remain two summands. An absent body set has score
`None`, representing negative infinity; it is excluded from winning even when
all candidates are absent. Argmax retains ties as sets, without committing an
arbitrary member. Only finite body tables describe the intended semantics.

| Statement | Artifact |
|---|---|
| Singleton marginal equals its bracket | `mar_singleton` |
| Empty/singleton marginal equals Viterbi | `one_body_agreement` |
| One-body argmax sets are temperature independent | `one_body_temperature_invariance` |
| Two zero-score bodies beat one half-score body marginally | `witness_marginal` |
| Viterbi selects the half-score body | `witness_viterbi` |
| Those readouts disagree | `witness_fragile` |
| Full-coalition singleton annotation equals PIC's biased logit | `pic.specialization_alpha_eq_logit` |
| Annotation equals the residual reading | `pic.specialization_alpha_eq_residual` |
| Positive-temperature softmax preserves PIC logit order and argmax | `pic.specialization_softmax_order`, `pic.specialization_softmax_argmax` |

The seam is deliberately a single position, vocabulary atoms, full-coalition
body, and no external judgment. The bias enters once per complete body. An
absent atom remains absent; equating its score to a finite PIC logit is not
claimed. Chart recursion, read-head reconstruction, and admission are not
proved in `PDC_Derive.thy`.

`PDC_Admission.thy` additionally packages the pointwise margin rule as
`admitted_source_preserves_decision`, `pic.crystallization_admitted_write`,
and `pic.crystallization_complement_certified`. Bounds cover both the target
and its rivals, with strict margin > gamma > 2delta. This is not a proof that
a particular solver or learned frame satisfies the premises.

`pairwise_source_preserves_decision` adds a candidate-wise form: each body's
gap must exceed the absolute source-to-host gap drift for that rival. It
does not require pooling all rivals into a single whole-vocabulary radius.
The R5 exporter stores every finite pairwise slack separately.

Build from the repository root:

```sh
isabelle build -o timeout=40 -d examples/pic_core -D examples/pdc
```


`decode_fixed_outside_max` proves that a fixed finite nonempty outside set
can be reduced to its maximum when checking strict decoding of an inside
target. It is the decision reduction used by R7; an outside logsumexp is
used only in the empirical loss and is not substituted for that maximum.
