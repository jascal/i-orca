(*
  Lifecycle.thy -- the certificate-gated omega lifecycle: drop + drift under ONE margin budget.

  Closes the last gap in the theta/gamma-turnstile correspondence flagged in the Wyly review
  (pil PR #10). Wyly's design puts a unit's whole lifecycle on one incidence axis omega --
  reserve -> drop below theta -> plastic -> frozen as omega -> infinity. The three regimes were
  theorem-backed separately: drop = pic_krein's PIC_Prune certificate, freeze = C4, finite-omega
  drift = C8's anchored bound. This theory composes them into the SINGLE certificate an
  implementation can gate on:

    * score model: a decision's class-v score is the sum over units of per-unit contributions
      (the PIC incidence sum; value-system agnostic scalars);
    * lifecycle_perturbation: dropping the units in D while the kept units drift perturbs every
      class score by at most  Delta = Sum_{kept} delta_k + Sum_{dropped} beta_k  -- one triangle
      budget mixing the C8 drift budgets delta_k with PIC_Prune-style drop budgets beta_k;
    * lifecycle_decode_preserved: winner margin > 2 * Delta  =>  the argmax decision is IDENTICAL
      before and after the whole lifecycle step (drop + drift), exactly;
    * omega_lifecycle_certificate: the omega-instrumented form. Kept units at stationarity of the
      lam * omega_k anchor contribute delta_k = G_k / (2 * lam * omega_k) * R (task-gradient bound
      G_k, reader-norm bound R); dropped units contribute their TRACKED majorant beta_k. The
      theta-drop is certificate-gated: drop any D whose beta-sum fits the margin budget --
      soundness is decoupled from the search, exactly as in PIC_Prune.

  Honest scope: the score model is linear-per-unit (each unit's contribution is its parameter
  vector read against a fixed per-class reader) -- exact for readout/head layers and for linear
  decodes over memberships; upstream soft-AND layers need composition with their Lipschitz
  constants (empirical) or the per-concept membership certificate (C8). beta_k as an omega-derived
  quantity is a HYPOTHESIS the implementation must maintain (track the contribution majorant;
  usage-derived importance does not automatically majorize it). Stationarity, per-input margins:
  as in C8.
*)
theory Lifecycle
  imports GradedConsolidation
begin

subsection \<open>Abstract argmax over scores\<close>

text \<open>The argmax decoder over an abstract score function (amax is the inner-product instance).\<close>
definition argmax_set :: "'v set \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> 'v set" where
  "argmax_set V s = {v \<in> V. \<forall>w\<in>V. s w \<le> s v}"

lemma amax_is_argmax_set: "amax V U r = argmax_set V (\<lambda>v. U v \<bullet> r)"
  unfolding amax_def argmax_set_def by (rule refl)

lemma argmax_strict_winner:
  assumes v0: "v0 \<in> V"
      and str: "\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow> s w < s v0"
  shows "argmax_set V s = {v0}"
proof (rule set_eqI)
  fix v
  show "v \<in> argmax_set V s \<longleftrightarrow> v \<in> {v0}"
  proof
    assume vin: "v \<in> argmax_set V s"
    hence vV: "v \<in> V" and best: "\<forall>w\<in>V. s w \<le> s v" unfolding argmax_set_def by auto
    show "v \<in> {v0}"
    proof (cases "v = v0")
      case True thus ?thesis by simp
    next
      case False
      have "s v < s v0" by (rule str[OF vV False])
      moreover have "s v0 \<le> s v" using best v0 by auto
      ultimately have False by linarith
      thus ?thesis ..
    qed
  next
    assume "v \<in> {v0}"
    hence v: "v = v0" by simp
    have all: "\<forall>w\<in>V. s w \<le> s v0"
    proof
      fix w assume wV: "w \<in> V"
      show "s w \<le> s v0"
      proof (cases "w = v0")
        case True thus ?thesis by simp
      next
        case False show ?thesis using str[OF wV False] by linarith
      qed
    qed
    show "v \<in> argmax_set V s" using v0 all unfolding argmax_set_def v by simp
  qed
qed

subsection \<open>The per-unit score model and the lifecycle perturbation budget\<close>

text \<open>A decision's class-v score: the sum of per-unit contributions over the unit bank K.\<close>
definition score :: "'k set \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> real" where
  "score K c v = (\<Sum>k\<in>K. c k v)"

text \<open>One triangle budget for the whole lifecycle step: kept units drift by at most delta_k per
      class, dropped units forfeit at most their contribution majorant beta_k.\<close>
lemma lifecycle_perturbation:
  assumes finK: "finite K" and DK: "D \<subseteq> K"
      and kept: "\<And>k. k \<in> K - D \<Longrightarrow> \<bar>c' k v - c k v\<bar> \<le> \<delta> k"
      and dropped: "\<And>k. k \<in> D \<Longrightarrow> \<bar>c k v\<bar> \<le> \<beta> k"
  shows "\<bar>score (K - D) c' v - score K c v\<bar> \<le> (\<Sum>k\<in>K - D. \<delta> k) + (\<Sum>k\<in>D. \<beta> k)"
proof -
  have split: "score K c v = score (K - D) c v + (\<Sum>k\<in>D. c k v)"
    unfolding score_def by (rule sum.subset_diff[OF DK finK])
  have "score (K - D) c' v - score K c v
          = score (K - D) c' v - score (K - D) c v - (\<Sum>k\<in>D. c k v)"
    by (simp add: split)
  also have "\<dots> = (\<Sum>k\<in>K - D. c' k v - c k v) - (\<Sum>k\<in>D. c k v)"
    unfolding score_def by (simp add: sum_subtractf)
  finally have "\<bar>score (K - D) c' v - score K c v\<bar>
          \<le> \<bar>\<Sum>k\<in>K - D. c' k v - c k v\<bar> + \<bar>\<Sum>k\<in>D. c k v\<bar>"
    by (simp add: abs_triangle_ineq4)
  also have "\<dots> \<le> (\<Sum>k\<in>K - D. \<bar>c' k v - c k v\<bar>) + (\<Sum>k\<in>D. \<bar>c k v\<bar>)"
    by (intro add_mono sum_abs)
  also have "\<dots> \<le> (\<Sum>k\<in>K - D. \<delta> k) + (\<Sum>k\<in>D. \<beta> k)"
  proof (rule add_mono)
    show "(\<Sum>k\<in>K - D. \<bar>c' k v - c k v\<bar>) \<le> (\<Sum>k\<in>K - D. \<delta> k)"
      by (rule sum_mono) (rule kept)
    show "(\<Sum>k\<in>D. \<bar>c k v\<bar>) \<le> (\<Sum>k\<in>D. \<beta> k)"
      by (rule sum_mono) (rule dropped)
  qed
  finally show ?thesis .
qed

subsection \<open>The lifecycle decode certificate\<close>

text \<open>Winner margin beyond twice the lifecycle budget => the argmax decision is identical before
      and after dropping D and drifting the rest. Exact, per input; any D passing the check is
      certified, whatever heuristic (theta on omega) proposed it.\<close>
theorem lifecycle_decode_preserved:
  assumes finK: "finite K" and DK: "D \<subseteq> K" and v0: "v0 \<in> V"
      and kept: "\<And>k v. k \<in> K - D \<Longrightarrow> v \<in> V \<Longrightarrow> \<bar>c' k v - c k v\<bar> \<le> \<delta> k"
      and dropped: "\<And>k v. k \<in> D \<Longrightarrow> v \<in> V \<Longrightarrow> \<bar>c k v\<bar> \<le> \<beta> k"
      and margin: "\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow>
             score K c w + 2 * ((\<Sum>k\<in>K - D. \<delta> k) + (\<Sum>k\<in>D. \<beta> k)) < score K c v0"
  shows "argmax_set V (score (K - D) c') = {v0} \<and> argmax_set V (score K c) = {v0}"
proof -
  define \<Delta> where "\<Delta> = (\<Sum>k\<in>K - D. \<delta> k) + (\<Sum>k\<in>D. \<beta> k)"
  have d1: "0 \<le> (\<Sum>k\<in>K - D. \<delta> k)"
  proof (rule sum_nonneg)
    fix k assume kK: "k \<in> K - D"
    have "(0::real) \<le> \<bar>c' k v0 - c k v0\<bar>" by (rule abs_ge_zero)
    also have "\<dots> \<le> \<delta> k" by (rule kept[OF kK v0])
    finally show "0 \<le> \<delta> k" .
  qed
  have d2: "0 \<le> (\<Sum>k\<in>D. \<beta> k)"
  proof (rule sum_nonneg)
    fix k assume kD: "k \<in> D"
    have "(0::real) \<le> \<bar>c k v0\<bar>" by (rule abs_ge_zero)
    also have "\<dots> \<le> \<beta> k" by (rule dropped[OF kD v0])
    finally show "0 \<le> \<beta> k" .
  qed
  have D0: "0 \<le> \<Delta>" unfolding \<Delta>_def using d1 d2 by linarith
  have pert: "\<bar>score (K - D) c' v - score K c v\<bar> \<le> \<Delta>" if vV: "v \<in> V" for v
    unfolding \<Delta>_def
  proof (rule lifecycle_perturbation[OF finK DK])
    fix k assume "k \<in> K - D"
    thus "\<bar>c' k v - c k v\<bar> \<le> \<delta> k" using vV by (rule kept)
  next
    fix k assume "k \<in> D"
    thus "\<bar>c k v\<bar> \<le> \<beta> k" using vV by (rule dropped)
  qed
  have old: "argmax_set V (score K c) = {v0}"
  proof (rule argmax_strict_winner[OF v0])
    fix w assume "w \<in> V" and "w \<noteq> v0"
    from margin[OF this] D0 show "score K c w < score K c v0"
      unfolding \<Delta>_def[symmetric] by linarith
  qed
  have new: "argmax_set V (score (K - D) c') = {v0}"
  proof (rule argmax_strict_winner[OF v0])
    fix w assume wV: "w \<in> V" and wne: "w \<noteq> v0"
    from margin[OF wV wne] abs_le_D1[OF pert[OF wV]] abs_le_D2[OF pert[OF v0]]
    show "score (K - D) c' w < score (K - D) c' v0"
      unfolding \<Delta>_def[symmetric] by linarith
  qed
  from new old show ?thesis by (rule conjI)
qed

subsection \<open>The omega-instrumented certificate\<close>

text \<open>The form an implementation gates on. Each unit contributes its parameter vector read against
      a fixed per-class reader. Kept units sit at stationarity of their lam * omega_k anchor with
      task-gradient bound G_k and reader norms bounded by R, so they drift-perturb by at most
      G_k / (2 * lam * omega_k) * R; dropped units forfeit at most their tracked majorant beta_k.
      Margin beyond twice the total => the decode survives the whole lifecycle step exactly.
      Raising omega_k shrinks its term at rate 1/omega_k (consolidation buys stability); the
      theta-drop is sound for ANY dropped set whose beta-sum fits the budget.\<close>
theorem omega_lifecycle_certificate:
  fixes p p' :: "'k \<Rightarrow> 'a::real_inner" and reader :: "'k \<Rightarrow> 'v \<Rightarrow> 'a"
    and gL :: "'k \<Rightarrow> 'a" and om G \<beta> :: "'k \<Rightarrow> real" and lam R :: real
  assumes finK: "finite K" and DK: "D \<subseteq> K" and v0: "v0 \<in> V"
      and stat: "\<And>k. k \<in> K - D \<Longrightarrow> gL k + (2 * lam * om k) *\<^sub>R (p' k - p k) = 0"
      and gb: "\<And>k. k \<in> K - D \<Longrightarrow> norm (gL k) \<le> G k"
      and lam: "0 < lam" and om: "\<And>k. k \<in> K - D \<Longrightarrow> 0 < om k"
      and rd: "\<And>k v. k \<in> K - D \<Longrightarrow> v \<in> V \<Longrightarrow> norm (reader k v) \<le> R"
      and beta: "\<And>k v. k \<in> D \<Longrightarrow> v \<in> V \<Longrightarrow> \<bar>p k \<bullet> reader k v\<bar> \<le> \<beta> k"
      and margin: "\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow>
             score K (\<lambda>k v. p k \<bullet> reader k v) w
               + 2 * ((\<Sum>k\<in>K - D. G k / (2 * lam * om k) * R) + (\<Sum>k\<in>D. \<beta> k))
             < score K (\<lambda>k v. p k \<bullet> reader k v) v0"
  shows "argmax_set V (score (K - D) (\<lambda>k v. p' k \<bullet> reader k v)) = {v0} \<and>
         argmax_set V (score K (\<lambda>k v. p k \<bullet> reader k v)) = {v0}"
proof (rule lifecycle_decode_preserved[OF finK DK v0, where
         \<delta> = "\<lambda>k. G k / (2 * lam * om k) * R" and \<beta> = \<beta>])
  fix k v assume kK: "k \<in> K - D" and vV: "v \<in> V"
  have drift: "norm (p' k - p k) \<le> G k / (2 * lam * om k)"
    by (rule anchored_drift_bound[OF stat[OF kK] gb[OF kK] lam om[OF kK]])
  have drift0: "0 \<le> G k / (2 * lam * om k)"
    by (rule order_trans[OF norm_ge_zero drift])
  have "\<bar>p' k \<bullet> reader k v - p k \<bullet> reader k v\<bar>
          \<le> G k / (2 * lam * om k) * norm (reader k v)"
    by (rule inner_drift_bound[OF drift])
  also have "\<dots> \<le> G k / (2 * lam * om k) * R"
    by (rule mult_left_mono[OF rd[OF kK vV] drift0])
  finally show "\<bar>p' k \<bullet> reader k v - p k \<bullet> reader k v\<bar> \<le> G k / (2 * lam * om k) * R" .
next
  fix k v assume "k \<in> D" and "v \<in> V"
  thus "\<bar>p k \<bullet> reader k v\<bar> \<le> \<beta> k" by (rule beta)
next
  fix w assume "w \<in> V" and "w \<noteq> v0"
  thus "score K (\<lambda>k v. p k \<bullet> reader k v) w
          + 2 * ((\<Sum>k\<in>K - D. G k / (2 * lam * om k) * R) + (\<Sum>k\<in>D. \<beta> k))
        < score K (\<lambda>k v. p k \<bullet> reader k v) v0" by (rule margin)
qed

end
