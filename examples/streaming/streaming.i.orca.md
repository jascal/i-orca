<!--
  i-orca surface for the EVENT-TIME STREAMING corpus -- the mathematical core
  underneath s-orca's Flink/PySpark pipelines.

  NOT to be confused with ../watermark/, which formalises Aaronson's LLM
  watermarking scheme. Different sense of "watermark" entirely: that one is a
  keyed sampling rule for detecting model-generated text, this one is the
  event-time progress marker of a dataflow. No shared mathematics.

  The model (EventTime.thy): a stream is the arrival-ordered list of its events'
  event times, so `xs ! i` is the event time of the i-th event TO ARRIVE and
  out-of-order arrival is a non-monotone list. The watermark after a prefix is
  `max(times seen) - d`. A tumbling window of width w around t is
  [win_lo w t, win_hi w t), and closes once the watermark reaches win_hi.

  As in ../provenance/ and ../complexity/, the content lives in the kernel-checked
  theory; each theorem below is STATED in i-orca form and discharged by
  `(rule <lemma>)` resolved through `## imports`.

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID.
    - Kernel check, inside this directory's session:
        isabelle build -D examples/streaming -o quick_and_dirty Streaming
      EventTime.thy contains no `sorry` and no `oops`.

  WHAT THIS DOES AND DOES NOT SAY. Every theorem is about the model. None is a
  statement about Flink or Spark, neither of which has a formal semantics to prove
  against. Transfer to an engine is an ASSUMPTION, carried in s-orca's portability
  matrix with basis `documented`, and is never promoted to `proved`.

  Map to s-orca:
    SAFETY      -> why `watermark:` is sound: closing on it loses nothing
    PROGRESS    -> PORTABILITY_IDLE_SOURCE and the `idle_timeout:` attribute
    THE TRADE   -> why `idle_timeout` is a declared choice, not a compiler default
    FLOOR       -> the `latency_floor:` property, computed from the document alone
-->

# theorem WatermarkSafety

> Closing a window on the watermark loses nothing. Under bounded lateness `d` — every arriving event is at most `d` behind the largest event time already seen — if the watermark has reached a window's upper edge `hi`, then every event whose time falls below `hi` has already arrived. Contrapositively, no event belonging to a closed window can still be in flight. This is the theorem that makes a declared `watermark:` sound rather than merely conventional. Cites `watermark_safety`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| bounded_lateness d xs ⟹ n ≤ length xs ⟹ int hi ≤ wmk d (take n xs) ⟹ i < length xs ⟹ xs ! i < hi ⟹ i < n |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | bounded_lateness d xs ⟹ n ≤ length xs ⟹ int hi ≤ wmk d (take n xs) ⟹ i < length xs ⟹ xs ! i < hi ⟹ i < n | a later arrival would be at least `hi` by bounded lateness, contradicting membership of the window | — | (rule watermark_safety) | method |


# theorem IdleChannelPinsWatermark

> The global watermark is the minimum over input channels, so it is bounded above by every single channel. A channel that never advances therefore caps the whole job. Cites `idle_channel_pins_watermark`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| j < length ws ⟹ global_wmk ws ≤ ws ! j |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | j < length ws ⟹ global_wmk ws ≤ ws ! j | the minimum of a finite set is below each of its elements | — | (rule idle_channel_pins_watermark) | method |


# theorem WindowNeverClosesWithIdleChannel

> The failure mode in full. One channel sitting below `hi` prevents the window at `hi` from EVER closing, however far every other channel has advanced. This is the empirically-observed bug that motivated the corpus: against a one-partition topic with parallelism 16, fifteen idle subtasks pinned the watermark, and the Flink job reported RUNNING while emitting nothing at all. Cites `window_never_closes_with_idle_channel`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| j < length ws ⟹ ws ! j < int hi ⟹ ¬ int hi ≤ global_wmk ws |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | j < length ws ⟹ ws ! j < int hi ⟹ ¬ int hi ≤ global_wmk ws | the pinning bound instantiated at the lagging channel | — | (rule window_never_closes_with_idle_channel) | method |


# theorem IdleExclusionProgress

> Excluding idle channels restores progress. If the minimum is taken over the ACTIVE channels only, and every active channel has reached `hi`, the global watermark reaches `hi`. This is the invariant Flink's `table.exec.source.idle-timeout` implements, and what s-orca's `idle_timeout:` source attribute compiles to. Cites `idle_exclusion_progress`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| ∃c ∈ set cs. snd c ⟹ ∀c ∈ set cs. snd c ⟶ int hi ≤ fst c ⟹ int hi ≤ active_wmk cs |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∃c ∈ set cs. snd c ⟹ ∀c ∈ set cs. snd c ⟶ int hi ≤ fst c ⟹ int hi ≤ active_wmk cs | a minimum over a finite non-empty set all of whose members clear the bound clears it | — | (rule idle_exclusion_progress) | method |


# theorem LateEventMissesWindow

> Progress is bought with data loss. An event arriving more than one window width below the watermark has definitively missed its window: that window is already closed. Read together with `IdleExclusionProgress` this makes the safety/liveness tension precise, and it is the reason `idle_timeout` is a declared choice in s-orca rather than a default the compiler picks on the author's behalf. Cites `late_event_misses_window`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| 0 < w ⟹ int t + int w < wmk d xs ⟹ int (win_hi w t) ≤ wmk d xs |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < w ⟹ int t + int w < wmk d xs ⟹ int (win_hi w t) ≤ wmk d xs | the window's upper edge is at most one width above the event | — | (rule late_event_misses_window) | method |


# theorem EmissionRequiresFutureEvent

> A window cannot close until an event at least `d` BEYOND its upper edge has actually been observed. The wait is not a scheduling artefact and no amount of compute removes it. Cites `emission_requires_future_event`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| xs ≠ [] ⟹ int hi ≤ wmk d xs ⟹ (∃t ∈ set xs. int hi + int d ≤ int t) |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | xs ≠ [] ⟹ int hi ≤ wmk d xs ⟹ (∃t ∈ set xs. int hi + int d ≤ int t) | the witness is the maximum observed event time, which is attained | — | (rule emission_requires_future_event) | method |


# theorem LatencyFloorNewest

> The floor for the newest event in a window is the watermark delay. An event inside a window that has closed is separated from the triggering observation by at least `d` in event time. Cites `latency_floor_newest`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| xs ≠ [] ⟹ t < hi ⟹ int hi ≤ wmk d xs ⟹ (∃t' ∈ set xs. int d ≤ int t' - int t) |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | xs ≠ [] ⟹ t < hi ⟹ int hi ≤ wmk d xs ⟹ (∃t' ∈ set xs. int d ≤ int t' - int t) | the triggering event sits at least `d` past the window edge, itself past the event | — | (rule latency_floor_newest) | method |


# theorem LatencyFloorOldest

> The floor for the OLDEST event in a window is the window width plus the watermark delay. Taken with `LatencyFloorNewest` this brackets the single-stage floor in `[d, w + d]`, and both ends are computable from the pipeline document with no measurement whatsoever. Cites `latency_floor_oldest`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| xs ≠ [] ⟹ hi = lo + w ⟹ int hi ≤ wmk d xs ⟹ (∃t' ∈ set xs. int w + int d ≤ int t' - int lo) |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | xs ≠ [] ⟹ hi = lo + w ⟹ int hi ≤ wmk d xs ⟹ (∃t' ∈ set xs. int w + int d ≤ int t' - int lo) | the window's lower edge is a full width below the triggering observation | — | (rule latency_floor_oldest) | method |


# theorem ChainFloorLower

> Along a chain of windowed stages the floors ADD, and the sum of the watermark delays alone is already unavoidable. A windowed stage emits at the event time of its window's upper edge, so a downstream stage windows those upper edges and its own delay accumulates on top. Cites `chain_floor_lower`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| 0 < w1 ⟹ 0 < w2 ⟹ t + d1 + d2 ≤ win_hi w2 (win_hi w1 t) + d1 + d2 |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < w1 ⟹ 0 < w2 ⟹ t + d1 + d2 ≤ win_hi w2 (win_hi w1 t) + d1 + d2 | each stage's upper edge strictly exceeds its input time | — | (rule chain_floor_lower) | method |


# theorem ChainFloorUpper

> The composed floor is at most the sum of (window + watermark) over the stages. This is the bound that licenses s-orca computing a pipeline's `latency_floor` by summing `window + watermark` along each path: the figure it reports is a genuine upper bound on the unavoidable wait, not an estimate. Cites `chain_floor_upper`.

## imports

| Theory    |
|-----------|
| EventTime |

## goal

| Statement |
|-----------|
| 0 < w1 ⟹ 0 < w2 ⟹ win_hi w2 (win_hi w1 t) + d1 + d2 ≤ t + w1 + w2 + d1 + d2 |

## proof

| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < w1 ⟹ 0 < w2 ⟹ win_hi w2 (win_hi w1 t) + d1 + d2 ≤ t + w1 + w2 + d1 + d2 | each stage's upper edge is at most one width above its input time | — | (rule chain_floor_upper) | method |
