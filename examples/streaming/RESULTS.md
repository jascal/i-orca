# Results — event-time streaming corpus

Isabelle2025-2. Session `Streaming` = `HOL` + `EventTime` + `Streaming_Surface`.

## Structural verification

```
$ i-orca verify examples/streaming/streaming.i.orca.md
theorem WatermarkSafety: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem IdleChannelPinsWatermark: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem WindowNeverClosesWithIdleChannel: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem IdleExclusionProgress: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem LateEventMissesWindow: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem EmissionRequiresFutureEvent: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem LatencyFloorNewest: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem LatencyFloorOldest: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem ChainFloorLower: VALID  (formal_fraction_static=1.000, 0 frontier holes)
theorem ChainFloorUpper: VALID  (formal_fraction_static=1.000, 0 frontier holes)
```

## Kernel check

```
$ isabelle build -D examples/streaming -o quick_and_dirty Streaming
Running Streaming ...
Finished Streaming (0:00:01 elapsed time)
```

10 theorems, 0 `sorry`, 0 `oops`.

## Non-vacuity

A green kernel build only means the stated theorems follow. To confirm the citations carry
content rather than being accepted by a lax `by`, a strictly stronger variant of
`emission_requires_future_event` (demanding `d + 1` rather than `d`) was discharged against the
same lemma. Isabelle rejected it:

```
*** goal (1 subgoal):
***  1. ⟦xs ≠ []; int hi ≤ wmk d xs⟧ ⟹ ∃t∈set xs. int hi + int d + 1 ≤ int t
*** Failed to apply initial proof method
```

The corpus also deliberately does **not** list cited lemmas in `## context`: the compiler lowers
context rows to local `assumes`, which would turn each citation into a vacuous `P ⟹ P`.

## Downstream

`chain_floor_upper` is the soundness argument for s-orca's `latency_floor` property
(`s_orca/verifier/verifier.py:latency_floor_ms`). Worked figures from that implementation:

| Pipeline | Floor | Composition |
|---|---|---|
| `clickstream-sessions` | 33m | 30m session gap + 2m watermark + 1m Spark trigger |
| `kafka-roundtrip` | 17s | 10s window + 5s watermark + 2s Spark trigger |
| `fraud-detection` | not decided | a `process` timeout is an unmodelled wait, so the property is skipped rather than passed |

The third row is the intended behaviour: the modelled figure would be an under-estimate, and an
under-estimate would let an unmeetable budget pass.
