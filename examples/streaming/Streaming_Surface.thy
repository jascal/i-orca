theory Streaming_Surface
  imports EventTime Equivalence
begin

text \<open>Closing a window on the watermark loses nothing. Under bounded lateness `d` — every arriving event is at most `d` behind the largest event time already seen — if the watermark has reached a window's upper edge `hi`, then every event whose time falls below `hi` has already arrived. Contrapositively, no event belonging to a closed window can still be in flight. This is the theorem that makes a declared `watermark:` sound rather than merely conventional. Cites `watermark_safety`.\<close>
theorem watermarksafety:
  shows "bounded_lateness d xs \<Longrightarrow> n \<le> length xs \<Longrightarrow> int hi \<le> wmk d (take n xs) \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i < hi \<Longrightarrow> i < n"
proof -
  show "bounded_lateness d xs \<Longrightarrow> n \<le> length xs \<Longrightarrow> int hi \<le> wmk d (take n xs) \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i < hi \<Longrightarrow> i < n" by (rule watermark_safety)
qed

text \<open>The global watermark is the minimum over input channels, so it is bounded above by every single channel. A channel that never advances therefore caps the whole job. Cites `idle_channel_pins_watermark`.\<close>
theorem idlechannelpinswatermark:
  shows "j < length ws \<Longrightarrow> global_wmk ws \<le> ws ! j"
proof -
  show "j < length ws \<Longrightarrow> global_wmk ws \<le> ws ! j" by (rule idle_channel_pins_watermark)
qed

text \<open>The failure mode in full. One channel sitting below `hi` prevents the window at `hi` from EVER closing, however far every other channel has advanced. This is the empirically-observed bug that motivated the corpus: against a one-partition topic with parallelism 16, fifteen idle subtasks pinned the watermark, and the Flink job reported RUNNING while emitting nothing at all. Cites `window_never_closes_with_idle_channel`.\<close>
theorem windownevercloseswithidlechannel:
  shows "j < length ws \<Longrightarrow> ws ! j < int hi \<Longrightarrow> \<not> int hi \<le> global_wmk ws"
proof -
  show "j < length ws \<Longrightarrow> ws ! j < int hi \<Longrightarrow> \<not> int hi \<le> global_wmk ws" by (rule window_never_closes_with_idle_channel)
qed

text \<open>Excluding idle channels restores progress. If the minimum is taken over the ACTIVE channels only, and every active channel has reached `hi`, the global watermark reaches `hi`. This is the invariant Flink's `table.exec.source.idle-timeout` implements, and what s-orca's `idle_timeout:` source attribute compiles to. Cites `idle_exclusion_progress`.\<close>
theorem idleexclusionprogress:
  shows "\<exists>c \<in> set cs. snd c \<Longrightarrow> \<forall>c \<in> set cs. snd c \<longrightarrow> int hi \<le> fst c \<Longrightarrow> int hi \<le> active_wmk cs"
proof -
  show "\<exists>c \<in> set cs. snd c \<Longrightarrow> \<forall>c \<in> set cs. snd c \<longrightarrow> int hi \<le> fst c \<Longrightarrow> int hi \<le> active_wmk cs" by (rule idle_exclusion_progress)
qed

text \<open>Progress is bought with data loss. An event arriving more than one window width below the watermark has definitively missed its window: that window is already closed. Read together with `IdleExclusionProgress` this makes the safety/liveness tension precise, and it is the reason `idle_timeout` is a declared choice in s-orca rather than a default the compiler picks on the author's behalf. Cites `late_event_misses_window`.\<close>
theorem lateeventmisseswindow:
  shows "0 < w \<Longrightarrow> int t + int w < wmk d xs \<Longrightarrow> int (win_hi w t) \<le> wmk d xs"
proof -
  show "0 < w \<Longrightarrow> int t + int w < wmk d xs \<Longrightarrow> int (win_hi w t) \<le> wmk d xs" by (rule late_event_misses_window)
qed

text \<open>A window cannot close until an event at least `d` BEYOND its upper edge has actually been observed. The wait is not a scheduling artefact and no amount of compute removes it. Cites `emission_requires_future_event`.\<close>
theorem emissionrequiresfutureevent:
  shows "xs \<noteq> [] \<Longrightarrow> int hi \<le> wmk d xs \<Longrightarrow> (\<exists>t \<in> set xs. int hi + int d \<le> int t)"
proof -
  show "xs \<noteq> [] \<Longrightarrow> int hi \<le> wmk d xs \<Longrightarrow> (\<exists>t \<in> set xs. int hi + int d \<le> int t)" by (rule emission_requires_future_event)
qed

text \<open>The floor for the newest event in a window is the watermark delay. An event inside a window that has closed is separated from the triggering observation by at least `d` in event time. Cites `latency_floor_newest`.\<close>
theorem latencyfloornewest:
  shows "xs \<noteq> [] \<Longrightarrow> t < hi \<Longrightarrow> int hi \<le> wmk d xs \<Longrightarrow> (\<exists>t' \<in> set xs. int d \<le> int t' - int t)"
proof -
  show "xs \<noteq> [] \<Longrightarrow> t < hi \<Longrightarrow> int hi \<le> wmk d xs \<Longrightarrow> (\<exists>t' \<in> set xs. int d \<le> int t' - int t)" by (rule latency_floor_newest)
qed

text \<open>The floor for the OLDEST event in a window is the window width plus the watermark delay. Taken with `LatencyFloorNewest` this brackets the single-stage floor in `[d, w + d]`, and both ends are computable from the pipeline document with no measurement whatsoever. Cites `latency_floor_oldest`.\<close>
theorem latencyflooroldest:
  shows "xs \<noteq> [] \<Longrightarrow> hi = lo + w \<Longrightarrow> int hi \<le> wmk d xs \<Longrightarrow> (\<exists>t' \<in> set xs. int w + int d \<le> int t' - int lo)"
proof -
  show "xs \<noteq> [] \<Longrightarrow> hi = lo + w \<Longrightarrow> int hi \<le> wmk d xs \<Longrightarrow> (\<exists>t' \<in> set xs. int w + int d \<le> int t' - int lo)" by (rule latency_floor_oldest)
qed

text \<open>Along a chain of windowed stages the floors ADD, and the sum of the watermark delays alone is already unavoidable. A windowed stage emits at the event time of its window's upper edge, so a downstream stage windows those upper edges and its own delay accumulates on top. Cites `chain_floor_lower`.\<close>
theorem chainfloorlower:
  shows "0 < w1 \<Longrightarrow> 0 < w2 \<Longrightarrow> t + d1 + d2 \<le> win_hi w2 (win_hi w1 t) + d1 + d2"
proof -
  show "0 < w1 \<Longrightarrow> 0 < w2 \<Longrightarrow> t + d1 + d2 \<le> win_hi w2 (win_hi w1 t) + d1 + d2" by (rule chain_floor_lower)
qed

text \<open>The composed floor is at most the sum of (window + watermark) over the stages. This is the bound that licenses s-orca computing a pipeline's `latency_floor` by summing `window + watermark` along each path: the figure it reports is a genuine upper bound on the unavoidable wait, not an estimate. Cites `chain_floor_upper`.\<close>
theorem chainfloorupper:
  shows "0 < w1 \<Longrightarrow> 0 < w2 \<Longrightarrow> win_hi w2 (win_hi w1 t) + d1 + d2 \<le> t + w1 + w2 + d1 + d2"
proof -
  show "0 < w1 \<Longrightarrow> 0 < w2 \<Longrightarrow> win_hi w2 (win_hi w1 t) + d1 + d2 \<le> t + w1 + w2 + d1 + d2" by (rule chain_floor_upper)
qed

text \<open>A filter is a per-record map, so it denotes the same function in any engine whatsoever. This is the base case of portability: for stateless work there is no side condition to discharge and nothing for a migration to get wrong. Cites `stateless_op_agrees(1)`.\<close>
theorem filterisengineagnostic:
  shows "op_agrees E1 E2 (Filter p)"
proof -
  show "op_agrees E1 E2 (Filter p)" by (rule stateless_op_agrees(1))
qed

text \<open>The same for a projection. Cites `stateless_op_agrees(2)`.\<close>
theorem projectisengineagnostic:
  shows "op_agrees E1 E2 (Project f)"
proof -
  show "op_agrees E1 E2 (Project f)" by (rule stateless_op_agrees(2))
qed

text \<open>The congruence, and the theorem `portable:` discharges. If two engines agree operator by operator, they agree on the whole pipeline. This is what licenses checking portability construct by construct — a per-operator matrix — instead of reasoning about pipelines as indivisible wholes. Cites `compatible_implies_equivalent`.\<close>
theorem compatibleimpliesequivalent:
  shows "compatible E1 E2 ps \<Longrightarrow> run E1 ps xs = run E2 ps xs"
proof -
  show "compatible E1 E2 ps \<Longrightarrow> run E1 ps xs = run E2 ps xs" by (rule compatible_implies_equivalent)
qed

text \<open>The unconditional corollary: a pipeline built only from stateless operators is portable between any two engines, with an empty side-condition list. Cites `stateless_pipeline_portable`.\<close>
theorem statelesspipelineisportable:
  shows "\<forall>p \<in> set ps. (\<exists>q. p = Filter q) \<or> (\<exists>f. p = Project f) \<Longrightarrow> run E1 ps xs = run E2 ps xs"
proof -
  show "\<forall>p \<in> set ps. (\<exists>q. p = Filter q) \<or> (\<exists>f. p = Project f) \<Longrightarrow> run E1 ps xs = run E2 ps xs" by (rule stateless_pipeline_portable)
qed

text \<open>Each event lies in the window the assignment gives it: `win_lo w t ≤ t < win_lo w t + w`. Well-definedness, and the fact that makes "same assignment" a meaningful condition. Cites `window_containment`.\<close>
theorem windowcontainment:
  shows "0 < w \<Longrightarrow> win_lo w t \<le> t \<and> t < win_lo w t + w"
proof -
  show "0 < w \<Longrightarrow> win_lo w t \<le> t \<and> t < win_lo w t + w" by (rule window_containment)
qed

text \<open>Window assignment is forced, so it is not a place two engines can differ. ANY epoch-aligned tumbling window of width `w` containing `t` is `win_lo w t`. This converts a strong assumption, that the engines assign events to the same windows, into a weak and checkable one: that both use epoch-aligned tumbling windows. Cites `window_assignment_unique`.\<close>
theorem windowassignmentunique:
  shows "0 < w \<Longrightarrow> b mod w = 0 \<Longrightarrow> b \<le> t \<Longrightarrow> t < b + w \<Longrightarrow> b = win_lo w t"
proof -
  show "0 < w \<Longrightarrow> b mod w = 0 \<Longrightarrow> b \<le> t \<Longrightarrow> t < b + w \<Longrightarrow> b = win_lo w t" by (rule window_assignment_unique)
qed

text \<open>Deduplication with a bounded key memory suppresses no more than deduplication with an unbounded one. Operationally: the engine that forgets keys may emit duplicates the other removes, and the difference is one-directional. Cites `dedup_bounded_keeps_superset`.\<close>
theorem dedupboundedkeepssuperset:
  shows "kept None xs \<subseteq> kept (Some d) xs"
proof -
  show "kept None xs \<subseteq> kept (Some d) xs" by (rule dedup_bounded_keeps_superset)
qed

text \<open>The two deduplication semantics agree when every repeat of a key falls inside the horizon. Note what this condition is about: the DATA, not the pipeline. Cites `dedup_agree_on_clustered`.\<close>
theorem dedupagreeonclustered:
  shows "clustered d xs \<Longrightarrow> dedup_list None xs = dedup_list (Some d) xs"
proof -
  show "clustered d xs \<Longrightarrow> dedup_list None xs = dedup_list (Some d) xs" by (rule dedup_agree_on_clustered)
qed

text \<open>And nothing about the pipeline can reconcile them: two records sharing a key and separated by more than the horizon are kept by the bounded engine and dropped by the unbounded one. This is why s-orca reports `PORTABILITY_DEDUP_SEMANTICS` as a warning requiring a human decision rather than an error the verifier can clear — the formalisation says there is nothing for the verifier to check, because the missing premise is about the data. Cites `dedup_horizons_differ_witness`.\<close>
theorem deduphorizonsdifferwitness:
  shows "dedup_list None [(0, 7), (100, 7)] \<noteq> dedup_list (Some 10) [(0, 7), (100, 7)]"
proof -
  show "dedup_list None [(0, 7), (100, 7)] \<noteq> dedup_list (Some 10) [(0, 7), (100, 7)]" by (rule dedup_horizons_differ_witness)
qed

text \<open>An aggregate emitted as a changelog and the same aggregate emitted once are different functions, not different renderings of one function. This is why an output-mode mismatch is an error in s-orca rather than a note. Cites `output_mode_is_semantic`.\<close>
theorem outputmodeissemantic:
  shows "update_out [1, 2] \<noteq> append_out [1, 2]"
proof -
  show "update_out [1, 2] \<noteq> append_out [1, 2]" by (rule output_mode_is_semantic)
qed

end
