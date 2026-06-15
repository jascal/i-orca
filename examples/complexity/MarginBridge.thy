theory MarginBridge
  imports MinimalDecider
begin

text \<open>GAP #4 -- the per-input MODEL BRIDGE. The static theory works with an
  input-independent contribution `c j v`. Real measurements are per-INPUT: a source j
  on input x contributes `c_x x j v`, and -- the key physical fact -- a source that does
  NOT fire on x contributes nothing on x. This theory makes that gate explicit and
  proves the decision on any input is carried entirely by the FIRING sources
  (`active_on`, the quantity fieldrun actually measures), so the static irreducibility /
  minimal-decider / pipeline results lift onto measured firing.\<close>


section \<open>Per-input contributions, gated by firing\<close>

text \<open>`c_at c_x x` specialises the per-input contribution to a fixed input x, giving a
  static contribution of the exact shape the Separation theory consumes.\<close>

definition c_at :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real)" where
  "c_at c_x x = (\<lambda>j v. c_x x j v)"

text \<open>`margin_x` is the per-input margin; `gated` is the firing gate: a non-firing source
  contributes 0 to every outcome on that input (`a x j` = its activation, `\<theta>` the
  threshold; `fires a \<theta> x j \<longleftrightarrow> \<theta> < a x j`, from Density).\<close>

definition margin_x ::
  "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "margin_x c_x t v j x = c_x x j t - c_x x j v"

definition gated :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "gated c_x a \<theta> \<longleftrightarrow> (\<forall>y i u. \<not> fires a \<theta> y i \<longrightarrow> c_x y i u = 0)"

text \<open>Exactly the bridge the model needs in margin form: no firing, no margin.\<close>

lemma not_fires_margin_zero:
  assumes g: "gated c_x a \<theta>" and nf: "\<not> fires a \<theta> x j"
  shows "margin_x c_x t v j x = 0"
proof -
  have "c_x x j t = 0 \<and> c_x x j v = 0"
    using g nf unfolding gated_def by blast
  thus ?thesis by (simp add: margin_x_def)
qed


section \<open>The decision on an input depends only on the firing sources\<close>

text \<open>Under the gate, a coalition sum equals the sum over its FIRING part: the
  non-firing members drop out at 0.\<close>

lemma sum_active_eq:
  assumes g: "gated c_x a \<theta>" and finP: "finite P"
  shows "(\<Sum>j\<in>P. c_x x j v) = (\<Sum>j\<in>active_on a \<theta> x P. c_x x j v)"
proof (rule sum.mono_neutral_right[OF finP])
  show "active_on a \<theta> x P \<subseteq> P" by (auto simp: active_on_def)
  show "\<forall>j\<in>P - active_on a \<theta> x P. c_x x j v = 0"
  proof
    fix j assume "j \<in> P - active_on a \<theta> x P"
    hence "\<not> fires a \<theta> x j" by (auto simp: active_on_def)
    thus "c_x x j v = 0" using g by (simp add: gated_def)
  qed
qed

text \<open>Hence deciding on input x is preserved by passing to the firing sub-coalition:
  the active (measured) neurons carry the whole decision.\<close>

theorem decides_iff_active:
  assumes g: "gated c_x a \<theta>" and finP: "finite P"
  shows "decides (c_at c_x x) P V t \<longleftrightarrow> decides (c_at c_x x) (active_on a \<theta> x P) V t"
proof -
  have eq: "(\<Sum>j\<in>P. c_at c_x x j w) = (\<Sum>j\<in>active_on a \<theta> x P. c_at c_x x j w)" for w
    using sum_active_eq[OF g finP] by (simp add: c_at_def)
  have "decides (c_at c_x x) P V t
        = (\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (\<Sum>j\<in>P. c_at c_x x j v) < (\<Sum>j\<in>P. c_at c_x x j t))"
    by (simp add: decides_def)
  also have "\<dots> = (\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
                    (\<Sum>j\<in>active_on a \<theta> x P. c_at c_x x j v)
                  < (\<Sum>j\<in>active_on a \<theta> x P. c_at c_x x j t))"
    by (simp add: eq)
  also have "\<dots> = decides (c_at c_x x) (active_on a \<theta> x P) V t"
    by (simp add: decides_def)
  finally show ?thesis .
qed


section \<open>The bridge: measured firing carries an irreducible atom\<close>

text \<open>On a real input x (gated contributions, S decides), the decision is carried by a
  genuinely IRREDUCIBLE atom that is a subset of the FIRING sources `active_on a \<theta> x S`
  -- the per-input active set fieldrun measures. So the measured active count
  `card (active_on a \<theta> x S)` upper-bounds the decision-relevant irreducible atom. This
  connects the static `irreducible_core_exists` to measured activations.\<close>

theorem effective_irreducible_atom_on_input:
  assumes g: "gated c_x a \<theta>" and finS: "finite S"
      and dec: "decides (c_at c_x x) S V t" and Vt: "\<exists>v\<in>V. v \<noteq> t"
  shows "\<exists>A. A \<subseteq> active_on a \<theta> x S
            \<and> decides (c_at c_x x) A V t
            \<and> irreducible (c_at c_x x) A V t
            \<and> card A \<le> card (active_on a \<theta> x S)"
proof -
  have sub: "active_on a \<theta> x S \<subseteq> S" by (auto simp: active_on_def)
  have finA: "finite (active_on a \<theta> x S)" using sub finS by (rule finite_subset)
  have decA: "decides (c_at c_x x) (active_on a \<theta> x S) V t"
    using dec decides_iff_active[OF g finS] by blast
  from irreducible_core_exists[OF finA decA Vt]
  obtain A where A: "A \<subseteq> active_on a \<theta> x S" "decides (c_at c_x x) A V t"
                   "irreducible (c_at c_x x) A V t" by blast
  have "card A \<le> card (active_on a \<theta> x S)" by (rule card_mono[OF finA A(1)])
  thus ?thesis using A by blast
qed

text \<open>Lift to an input SAMPLE: choosing one atom per input (bchoice) yields a family of
  irreducible atoms, each inside its input's measured active set. This is the measured
  counterpart of `pipeline_composition` -- the static pipeline bound transported onto a
  real firing sample.\<close>

theorem bridge_pipeline:
  assumes g: "gated c_x a \<theta>"
      and props: "\<forall>x\<in>Xs. finite (S x) \<and> decides (c_at c_x x) (S x) (V x) (t x)
                          \<and> (\<exists>v\<in>V x. v \<noteq> t x)"
  shows "\<exists>A. \<forall>x\<in>Xs. A x \<subseteq> active_on a \<theta> x (S x)
                    \<and> decides (c_at c_x x) (A x) (V x) (t x)
                    \<and> irreducible (c_at c_x x) (A x) (V x) (t x)
                    \<and> card (A x) \<le> card (active_on a \<theta> x (S x))"
proof -
  have "\<forall>x\<in>Xs. \<exists>A. A \<subseteq> active_on a \<theta> x (S x)
                  \<and> decides (c_at c_x x) A (V x) (t x)
                  \<and> irreducible (c_at c_x x) A (V x) (t x)
                  \<and> card A \<le> card (active_on a \<theta> x (S x))"
  proof
    fix x assume x: "x \<in> Xs"
    with props have "finite (S x)" "decides (c_at c_x x) (S x) (V x) (t x)"
                    "\<exists>v\<in>V x. v \<noteq> t x" by auto
    thus "\<exists>A. A \<subseteq> active_on a \<theta> x (S x)
              \<and> decides (c_at c_x x) A (V x) (t x)
              \<and> irreducible (c_at c_x x) A (V x) (t x)
              \<and> card A \<le> card (active_on a \<theta> x (S x))"
      by (rule effective_irreducible_atom_on_input[OF g])
  qed
  thus ?thesis by (rule bchoice)
qed

end
