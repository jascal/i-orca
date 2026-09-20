# Event-time streaming — i-orca corpus

The mathematical core underneath [s-orca](https://github.com/jascal/s-orca)'s Flink and PySpark
pipelines: what a watermark guarantees, when it fails to advance, and what latency a pipeline
specification makes unavoidable.

> **Not the same "watermark" as [`../watermark/`](../watermark/).** That corpus formalises
> Aaronson's LLM watermarking scheme, a keyed sampling rule for detecting model-generated text.
> This one is about the event-time progress marker of a dataflow. The word is shared; no
> mathematics is.

## The model

A stream is the arrival-ordered list of its events' event times, so `xs ! i` is the event time of
the *i*-th event **to arrive** and out-of-order arrival is simply a non-monotone list. The
watermark after a prefix is `max(times seen) − d`, the bounded-out-of-orderness strategy both
engines implement. A tumbling window of width `w` around `t` is `[win_lo w t, win_hi w t)`, and it
closes once the watermark reaches `win_hi`.

## What is established

| Theorem | Says |
|---|---|
| `watermark_safety` | Under bounded lateness `d`, every event belonging to a window has already arrived when that window closes. Closing on the watermark loses nothing. |
| `idle_channel_pins_watermark` | The global watermark is the minimum over input channels, so it is capped by every one of them. |
| `window_never_closes_with_idle_channel` | One channel below `hi` prevents the window at `hi` from ever closing, however far the others advance. |
| `idle_exclusion_progress` | Taking the minimum over *active* channels only restores progress. |
| `late_event_misses_window` | An event arriving more than a window width below the watermark has missed its window: progress is bought with data loss. |
| `emission_requires_future_event` | A window cannot close until an event at least `d` beyond its upper edge is observed. |
| `latency_floor_newest` / `latency_floor_oldest` | The single-stage wait is bracketed in `[d, w + d]`. |
| `chain_floor_lower` / `chain_floor_upper` | Along a chain the waits add: the composed floor lies between `Σd` and `Σ(w + d)`. |

## Why it exists

`window_never_closes_with_idle_channel` is not hypothetical. s-orca's cross-engine Kafka gate ran
one pipeline on both engines against a single-partition topic while Flink's default parallelism was
16. Fifteen subtasks had no partition, never advanced their watermark, and pinned the global
minimum. The job reported RUNNING and healthy and emitted nothing at all, while the same pipeline
on Spark was correct. The theorem pair says exactly why, and `idle_exclusion_progress` says what
fixes it.

`late_event_misses_window` is the other half, and it is why s-orca makes `idle_timeout` a declared
attribute rather than a compiler default. Excluding idle channels advances the watermark, and
advancing the watermark makes events late. That is a trade the pipeline author owns.

`chain_floor_upper` licenses s-orca's `latency_floor` property, which sums `window + watermark`
along each path and answers whether a pipeline could meet a latency budget *on any hardware at
all*.

## Scope

Every theorem is about the model. **None is a statement about Flink or Spark**, neither of which
has a formal semantics to prove against. Transfer to an engine is an assumption, carried in
s-orca's portability matrix with basis `documented`, and is never promoted to `proved`. Nothing
here bounds queueing delay, checkpoint cost or throughput; those are deployment properties and
need measurement, not proof.

## Verifying

```bash
# structural, no Isabelle
i-orca verify examples/streaming/streaming.i.orca.md

# kernel check (Isabelle2025-2), from the repository root
isabelle build -D examples/streaming -o quick_and_dirty Streaming
```

`EventTime.thy` carries the proofs and contains no `sorry` and no `oops`.
`Streaming_Surface.thy` is generated from `streaming.i.orca.md` by
`i-orca compile --target isar --document` and discharges each stated theorem by `(rule …)` against
`EventTime.thy`.
