(*
  EventTime.thy -- event-time streams, watermarks and tumbling windows.

  The abstract model behind s-orca's streaming pipelines. A stream is represented
  by the arrival-ordered list of its events' event times: `xs ! i` is the event
  time of the i-th event to ARRIVE, so list position is processing order and the
  value is event-time. Out-of-order arrival is therefore just a non-monotone list.

  The watermark after a prefix is `max(event times seen) - d`, the standard
  bounded-out-of-orderness strategy both Flink and Spark implement. A tumbling
  window of width w containing event time t is [win_lo w t, win_hi w t), and it
  CLOSES once the watermark reaches win_hi.

  What is established here:

    SAFETY     watermark_safety        -- under bounded lateness d, every event
                                          belonging to a window has already
                                          arrived when that window closes: closing
                                          on the watermark loses nothing.
    PROGRESS   idle_channel_pins_watermark, window_never_closes_with_idle_channel
                                       -- the global watermark is the MINIMUM over
                                          input channels, so a single channel that
                                          never produces pins it and no window ever
                                          closes, however far the others advance.
               idle_exclusion_progress -- excluding idle channels from that minimum
                                          restores progress.
    THE TRADE  late_event_misses_window -- and it is not free: advancing the
                                          watermark makes events late, and a late
                                          event's window is already closed. This is
                                          why `idle_timeout` is an explicit choice
                                          in s-orca rather than a compiler default.
    FLOOR      emission_requires_future_event, latency_floor_newest,
               latency_floor_oldest     -- a window cannot emit until an event at
                                          least d BEYOND its upper edge is seen, so
                                          output lag is at least d, and at least
                                          w + d for the oldest event in the window.
                                          This bound is a property of the
                                          specification, not of the deployment.
    COMPOSITION chain_floor_bounds      -- along a chain of windowed stages the
                                          floors add: the composed floor lies
                                          between (sum of d) and (sum of w + d).
                                          This is what licenses s-orca summing
                                          (window + watermark) along a path.

  Nothing here is a statement about Flink or Spark. It is a statement about the
  model; transfer to either engine is an assumption, tagged `documented` in
  s-orca's portability matrix, never proved.
*)

theory EventTime
  imports Main
begin

section \<open>Streams and watermarks\<close>

text \<open>The largest event time in a prefix. The empty prefix yields 0, which for
  natural-valued time is the bottom of the domain.\<close>

definition maxtime :: "nat list \<Rightarrow> nat" where
  "maxtime xs = (if xs = [] then 0 else Max (set xs))"

lemma maxtime_Nil [simp]: "maxtime [] = 0"
  by (simp add: maxtime_def)

lemma maxtime_ge: "x \<in> set xs \<Longrightarrow> x \<le> maxtime xs"
  by (auto simp: maxtime_def)

lemma maxtime_mem: "xs \<noteq> [] \<Longrightarrow> maxtime xs \<in> set xs"
  by (simp add: maxtime_def)

lemma maxtime_mono_subset:
  assumes "set xs \<subseteq> set ys"
  shows "maxtime xs \<le> maxtime ys"
proof (cases "xs = []")
  case True
  then show ?thesis by simp
next
  case False
  then have "set xs \<noteq> {}" by simp
  with assms have "set ys \<noteq> {}" by auto
  then have "ys \<noteq> []" by auto
  have "Max (set xs) \<le> Max (set ys)"
    using assms \<open>set xs \<noteq> {}\<close> by (intro Max_mono) auto
  with False \<open>ys \<noteq> []\<close> show ?thesis by (simp add: maxtime_def)
qed

lemma maxtime_take_mono:
  assumes "m \<le> n"
  shows "maxtime (take m xs) \<le> maxtime (take n xs)"
  using assms by (intro maxtime_mono_subset set_take_subset_set_take)

text \<open>The watermark: the largest event time observed, discounted by the declared
  out-of-orderness bound @{term d}. Integer-valued so that an early prefix may sit
  below zero.\<close>

definition wmk :: "nat \<Rightarrow> nat list \<Rightarrow> int" where
  "wmk d xs = int (maxtime xs) - int d"

lemma wmk_mono_take:
  assumes "m \<le> n"
  shows "wmk d (take m xs) \<le> wmk d (take n xs)"
  using maxtime_take_mono[OF assms] by (simp add: wmk_def)

text \<open>Bounded lateness: when an event arrives, its event time is no more than
  @{term d} behind the largest event time already observed. This is the hypothesis
  a declared watermark delay asserts about the source.\<close>

definition bounded_lateness :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "bounded_lateness d xs \<longleftrightarrow>
     (\<forall>i < length xs. int (maxtime (take i xs)) - int d \<le> int (xs ! i))"

section \<open>Tumbling windows\<close>

definition win_lo :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "win_lo w t = (t div w) * w"
definition win_hi :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "win_hi w t = (t div w) * w + w"

lemma win_lo_le: "0 < w \<Longrightarrow> win_lo w t \<le> t"
  by (simp add: win_lo_def minus_mod_eq_div_mult [symmetric])

lemma less_win_hi: "0 < w \<Longrightarrow> t < win_hi w t"
  by (simp add: win_hi_def) (metis div_mult_mod_eq mod_less_divisor add_strict_left_mono)

lemma win_hi_le: "0 < w \<Longrightarrow> win_hi w t \<le> t + w"
  using win_lo_le[of w t] by (simp add: win_hi_def win_lo_def)

section \<open>Safety: closing on the watermark loses nothing\<close>

text \<open>If the watermark has reached a window's upper edge @{term hi}, then every
  event whose time falls below @{term hi} has already arrived. Contrapositively, no
  event that belongs to a closed window can still be in flight.\<close>

theorem watermark_safety:
  assumes bl:     "bounded_lateness d xs"
      and n_len:  "n \<le> length xs"
      and closed: "int hi \<le> wmk d (take n xs)"
      and i_len:  "i < length xs"
      and in_win: "xs ! i < hi"
  shows "i < n"
proof (rule ccontr)
  assume "\<not> i < n"
  then have "n \<le> i" by simp
  have "int hi + int d \<le> int (maxtime (take n xs))"
    using closed by (simp add: wmk_def)
  also have "int (maxtime (take n xs)) \<le> int (maxtime (take i xs))"
    using maxtime_take_mono[OF \<open>n \<le> i\<close>] by simp
  finally have "int hi + int d \<le> int (maxtime (take i xs))" .
  moreover have "int (maxtime (take i xs)) - int d \<le> int (xs ! i)"
    using bl i_len by (simp add: bounded_lateness_def)
  ultimately have "int hi \<le> int (xs ! i)" by simp
  with in_win show False by simp
qed

section \<open>Progress: the global watermark is a minimum, so one idle channel pins it\<close>

definition global_wmk :: "int list \<Rightarrow> int" where
  "global_wmk ws = Min (set ws)"

theorem idle_channel_pins_watermark:
  assumes "j < length ws"
  shows "global_wmk ws \<le> ws ! j"
proof -
  have "ws ! j \<in> set ws" using assms by simp
  then show ?thesis by (simp add: global_wmk_def)
qed

text \<open>The failure mode in full: a single channel sitting below @{term hi} prevents
  the window at @{term hi} from ever closing, no matter how far ahead every other
  channel has advanced. The job is healthy and emits nothing.\<close>

corollary window_never_closes_with_idle_channel:
  assumes "j < length ws" and "ws ! j < int hi"
  shows "\<not> int hi \<le> global_wmk ws"
  using idle_channel_pins_watermark[OF assms(1)] assms(2) by simp

text \<open>Excluding idle channels restores progress: if the minimum is taken over the
  ACTIVE channels only, and every active channel has reached @{term hi}, the global
  watermark reaches @{term hi}. A channel is a pair (watermark, active).\<close>

definition active_wmk :: "(int \<times> bool) list \<Rightarrow> int" where
  "active_wmk cs = Min (fst ` {c \<in> set cs. snd c})"

theorem idle_exclusion_progress:
  assumes nonempty: "\<exists>c \<in> set cs. snd c"
      and advanced: "\<forall>c \<in> set cs. snd c \<longrightarrow> int hi \<le> fst c"
  shows "int hi \<le> active_wmk cs"
proof -
  let ?A = "fst ` {c \<in> set cs. snd c}"
  have "finite ?A" by simp
  moreover have "?A \<noteq> {}"
  proof -
    from nonempty obtain c where "c \<in> set cs" and "snd c" by blast
    then have "c \<in> {c \<in> set cs. snd c}" by simp
    then show ?thesis by blast
  qed
  moreover have "\<And>x. x \<in> ?A \<Longrightarrow> int hi \<le> x" using advanced by auto
  ultimately show ?thesis by (simp add: active_wmk_def)
qed

section \<open>The trade: advancing the watermark makes events late\<close>

text \<open>An event arriving more than one window width below the watermark has
  definitively missed its window: that window is already closed. Progress is
  therefore bought with data loss, which is why @{text idle_timeout} is a declared
  choice in s-orca and not a default the compiler picks.\<close>

theorem late_event_misses_window:
  assumes w_pos: "0 < w"
      and late:  "int t + int w < wmk d xs"
  shows "int (win_hi w t) \<le> wmk d xs"
proof -
  have "int (win_hi w t) \<le> int t + int w"
    using win_hi_le[OF w_pos, of t] by simp
  also have "\<dots> < wmk d xs" using late .
  finally show ?thesis by simp
qed

section \<open>The latency floor is a property of the specification\<close>

text \<open>A window cannot close until an event at least @{term d} beyond its upper edge
  has actually been observed. No amount of compute removes this wait.\<close>

theorem emission_requires_future_event:
  assumes ne:     "xs \<noteq> []"
      and closed: "int hi \<le> wmk d xs"
  shows "\<exists>t \<in> set xs. int hi + int d \<le> int t"
proof -
  have "maxtime xs \<in> set xs" using ne by (rule maxtime_mem)
  moreover have "int hi + int d \<le> int (maxtime xs)"
    using closed by (simp add: wmk_def)
  ultimately show ?thesis by blast
qed

corollary latency_floor_newest:
  assumes "xs \<noteq> []" and "t < hi" and "int hi \<le> wmk d xs"
  shows "\<exists>t' \<in> set xs. int d \<le> int t' - int t"
proof -
  obtain t' where "t' \<in> set xs" and "int hi + int d \<le> int t'"
    using emission_requires_future_event[OF assms(1,3)] by blast
  moreover from \<open>t < hi\<close> have "int t < int hi" by simp
  ultimately have "int d \<le> int t' - int t" by simp
  with \<open>t' \<in> set xs\<close> show ?thesis by blast
qed

corollary latency_floor_oldest:
  assumes "xs \<noteq> []" and "hi = lo + w" and "int hi \<le> wmk d xs"
  shows "\<exists>t' \<in> set xs. int w + int d \<le> int t' - int lo"
proof -
  obtain t' where "t' \<in> set xs" and "int hi + int d \<le> int t'"
    using emission_requires_future_event[OF assms(1,3)] by blast
  then have "int lo + int w + int d \<le> int t'" using assms(2) by simp
  then have "int w + int d \<le> int t' - int lo" by simp
  with \<open>t' \<in> set xs\<close> show ?thesis by blast
qed

section \<open>Composition: along a chain the floors add\<close>

text \<open>A windowed stage emits at the event time of its window's upper edge, so a
  downstream stage windows those upper edges and its own delay accumulates. For a
  two-stage chain the event time that must be observed before the final output
  appears lies between @{term "t + d1 + d2"} and @{term "t + w1 + w2 + d1 + d2"}.

  The upper bound is what licenses s-orca reporting the sum of
  (window + watermark) along a path as the worst-case floor; the lower bound says
  the sum of the watermark delays alone is already unavoidable.\<close>

theorem chain_floor_lower:
  assumes w1: "0 < w1" and w2: "0 < w2"
  shows "t + d1 + d2 \<le> win_hi w2 (win_hi w1 t) + d1 + d2"
proof -
  have "t < win_hi w1 t" using less_win_hi[OF w1] .
  moreover have "win_hi w1 t < win_hi w2 (win_hi w1 t)" using less_win_hi[OF w2] .
  ultimately show ?thesis by simp
qed

theorem chain_floor_upper:
  assumes w1: "0 < w1" and w2: "0 < w2"
  shows "win_hi w2 (win_hi w1 t) + d1 + d2 \<le> t + w1 + w2 + d1 + d2"
proof -
  have "win_hi w2 (win_hi w1 t) \<le> win_hi w1 t + w2" using win_hi_le[OF w2] .
  moreover have "win_hi w1 t \<le> t + w1" using win_hi_le[OF w1] .
  ultimately show ?thesis by simp
qed

end
