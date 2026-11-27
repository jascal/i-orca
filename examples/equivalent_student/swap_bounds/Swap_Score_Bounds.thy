theory Swap_Score_Bounds
  imports Complex_Main
begin

section \<open>Bounds on swap scores over a finite set of trials\<close>

text \<open>A trial is one (node, input pair, position) case of a swap test. For each system (host h,
clamped host c, student s) a function gives its output after the swap in that trial. The swap score
(IIA) of s against h over a finite trial set P is the fraction of trials where the outputs agree.\<close>

definition dis :: "'t set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> 't set" where
  "dis P f g = {t \<in> P. f t \<noteq> g t}"

definition agr :: "'t set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> 't set" where
  "agr P f g = {t \<in> P. f t = g t}"

definition score :: "'t set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> real" where
  "score P f g = real (card (agr P f g)) / real (card P)"

lemma agr_dis_card:
  assumes "finite P"
  shows "card (agr P f g) + card (dis P f g) = card P"
proof -
  have "agr P f g \<union> dis P f g = P" and "agr P f g \<inter> dis P f g = {}"
    by (auto simp: agr_def dis_def)
  moreover have "finite (agr P f g)" "finite (dis P f g)"
    using assms by (auto simp: agr_def dis_def)
  ultimately show ?thesis by (metis card_Un_disjoint)
qed

subsection \<open>S1: triangle inequality (licenses a host-only clamp screen)\<close>

theorem dis_triangle: "dis P s h \<subseteq> dis P s c \<union> dis P c h"
  by (auto simp: dis_def)

theorem card_dis_triangle:
  assumes "finite P"
  shows "card (dis P s h) \<le> card (dis P s c) + card (dis P c h)"
proof -
  have "card (dis P s h) \<le> card (dis P s c \<union> dis P c h)"
    using assms by (intro card_mono) (auto simp: dis_def)
  also have "\<dots> \<le> card (dis P s c) + card (dis P c h)" by (rule card_Un_le)
  finally show ?thesis .
qed

theorem score_triangle:
  assumes "finite P" and "P \<noteq> {}"
  shows "score P s c + score P c h - 1 \<le> score P s h"
proof -
  let ?n = "real (card P)"
  have n: "0 < ?n" using assms by (simp add: card_gt_0_iff)
  have e1: "real (card (agr P s h)) = ?n - real (card (dis P s h))"
   and e2: "real (card (agr P s c)) = ?n - real (card (dis P s c))"
   and e3: "real (card (agr P c h)) = ?n - real (card (dis P c h))"
    using agr_dis_card[OF assms(1)] by (metis add_diff_cancel_right' of_nat_add)+
  have t: "real (card (dis P s h)) \<le> real (card (dis P s c)) + real (card (dis P c h))"
    using card_dis_triangle[OF assms(1)] by (metis of_nat_add of_nat_le_iff)
  have "score P s c + score P c h - 1 = (real (card (agr P s c)) + real (card (agr P c h)) - ?n) / ?n"
    using n by (simp add: score_def field_simps)
  also have "\<dots> \<le> real (card (agr P s h)) / ?n"
    using n t by (intro divide_right_mono) (simp_all add: e1 e2 e3)
  finally show ?thesis by (simp add: score_def)
qed

corollary exact_screen:
  assumes "\<forall>t\<in>P. c t = h t" and "\<forall>t\<in>P. s t = c t"
  shows "\<forall>t\<in>P. s t = h t"
  using assms by simp

subsection \<open>S2: the floor a no-op student gets for free\<close>

text \<open>Per trial: h0 / s0 are the unswapped outputs, hs / ss the outputs after the swap. A no-op
student ignores the swap (ss = s0). Its raw swap score is at least its plain agreement minus the
fraction of trials where the swap changes the host's output, and it is wrong on every changed trial
where it matched the host before the swap.\<close>

theorem noop_floor_card:
  assumes fin: "finite P" and noop: "\<forall>t\<in>P. ss t = s0 t"
  shows "card (agr P s0 h0) \<le> card (agr P ss hs) + card (dis P hs h0)"
proof -
  have "agr P s0 h0 \<subseteq> agr P ss hs \<union> dis P hs h0"
    using noop by (auto simp: agr_def dis_def)
  then have "card (agr P s0 h0) \<le> card (agr P ss hs \<union> dis P hs h0)"
    using fin by (intro card_mono) (auto simp: agr_def dis_def)
  also have "\<dots> \<le> card (agr P ss hs) + card (dis P hs h0)" by (rule card_Un_le)
  finally show ?thesis .
qed

theorem noop_floor:
  assumes fin: "finite P" and ne: "P \<noteq> {}" and noop: "\<forall>t\<in>P. ss t = s0 t"
  shows "score P s0 h0 - real (card (dis P hs h0)) / real (card P) \<le> score P ss hs"
proof -
  have n: "0 < real (card P)" using fin ne by (simp add: card_gt_0_iff)
  have "real (card (agr P s0 h0)) \<le> real (card (agr P ss hs)) + real (card (dis P hs h0))"
    using noop_floor_card[OF fin noop] by (metis of_nat_add of_nat_le_iff)
  then have "(real (card (agr P s0 h0)) - real (card (dis P hs h0))) / real (card P) \<le> real (card (agr P ss hs)) / real (card P)"
    using n by (intro divide_right_mono) simp_all
  then show ?thesis by (simp add: score_def diff_divide_distrib)
qed

theorem noop_fails_changed:
  assumes "\<forall>t\<in>P. ss t = s0 t" and "t \<in> P" and "s0 t = h0 t" and "hs t \<noteq> h0 t"
  shows "ss t \<noteq> hs t"
  using assms by simp

end
