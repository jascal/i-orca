(*
  Compositional.thy -- C3: the compositional capacity gap (factored vs partition codes).

  Inputs are assignments of A independent binary attributes, encoded as the subsets S <= A of
  attributes that are ON. Two codes for a readout:

    FACTORED  : one membership per attribute; a linear readout  fpred th th0 S = th0 + sum_{i in S} th i.
    PARTITION : one indicator per observed combination; the readout is a free value per cell (any
                function w : cell => real -- the memorizing code).

  Proved, over this stated domain:

    (b) EXACT GENERALIZATION vs UNDETERMINED CELLS. Two factored readouts that agree on the canonical
        covering set -- the empty assignment plus the A singletons -- agree on EVERY combination:
        fitting a (linear-in-attributes) target on A+1 covering examples generalizes exactly to all
        2^A held-out combinations. The partition readout provably cannot: for any target and any
        unseen combination there are two partition readouts with ZERO training error that disagree
        on it -- the held-out cell is undetermined (chance), which is what `compositional` measures
        as 0.90 vs 0.69.
    (c) SAMPLE COMPLEXITY. The covering set has exactly card A + 1 elements (O(A)); the partition
        code is undetermined unless every one of the 2^A cells was seen: fewer than 2^A training
        cells leave a combination whose output is a free parameter (Omega(2^A)).
    (a) EXPRESSIVENESS (the monotone core). A conjunction over S0 is ONE linear-threshold rule on
        the factored code -- [sum_{i in S0} m_i(S) >= card S0] -- while the partition code spends
        one cell per positive combination: exactly 2^(card A - card S0) cells.

  The i-orca tie is RoutingRank-style dimension counting: the factored code has A+1 free directions,
  the partition code 2^A. Bridge from this domain to any trained model's inductive bias: `open`.
*)
theory Compositional
  imports "HOL-Analysis.Analysis"
begin

subsection \<open>The factored code and its readout\<close>

text \<open>Factored linear readout over attribute memberships: bias plus the sum of the weights of the
      attributes that are ON. (For S <= A finite this is the linear readout on the A-hyperplane code.)\<close>
definition fpred :: "('i \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> 'i set \<Rightarrow> real" where
  "fpred \<theta> \<theta>0 S = \<theta>0 + (\<Sum>i\<in>S. \<theta> i)"

text \<open>The canonical covering set: the base (all-OFF) assignment and each single-attribute flip.
      Every attribute is seen both OFF (base) and ON (its flip).\<close>
definition covering :: "'i set \<Rightarrow> 'i set set" where
  "covering A = insert {} ((\<lambda>i. {i}) ` A)"

lemma covering_card:
  assumes "finite A"
  shows "card (covering A) = card A + 1"
proof -
  have inj: "inj_on (\<lambda>i. {i}) A" by (rule inj_onI) auto
  have notin: "{} \<notin> (\<lambda>i. {i}) ` A" by auto
  have "card (covering A) = Suc (card ((\<lambda>i. {i}) ` A))"
    unfolding covering_def
    by (intro card_insert_disjoint finite_imageI assms notin)
  also have "card ((\<lambda>i. {i}) ` A) = card A" by (rule card_image[OF inj])
  finally show ?thesis by simp
qed

subsection \<open>(b) Factored code: fitting the covering set generalizes exactly\<close>

text \<open>Identification: two factored readouts that agree on the covering set of A agree on EVERY
      assignment S <= A. The base fixes the bias; each flip then fixes that attribute's weight;
      linearity does the rest. Fitting A+1 examples pins all 2^A outputs -- exact compositional
      generalization to never-seen combinations.\<close>
theorem factored_identification:
  assumes finA: "finite A"
      and agree: "\<And>T. T \<in> covering A \<Longrightarrow> fpred \<theta> \<theta>0 T = fpred \<theta>' \<theta>0' T"
      and SA: "S \<subseteq> A"
  shows "fpred \<theta> \<theta>0 S = fpred \<theta>' \<theta>0' S"
proof -
  have base: "\<theta>0 = \<theta>0'"
    using agree[of "{}"] unfolding covering_def fpred_def by simp
  have flip: "\<theta> i = \<theta>' i" if "i \<in> A" for i
    using agree[of "{i}"] that base unfolding covering_def fpred_def by auto
  have "(\<Sum>i\<in>S. \<theta> i) = (\<Sum>i\<in>S. \<theta>' i)"
    by (rule sum.cong[OF refl]) (use flip SA in auto)
  thus ?thesis using base unfolding fpred_def by simp
qed

text \<open>Corollary in target form: a factored readout with zero error on the covering examples of a
      linear target has zero error on all held-out combinations as well.\<close>
corollary factored_exact_generalization:
  assumes finA: "finite A"
      and fit: "\<And>T. T \<in> covering A \<Longrightarrow> fpred \<theta> \<theta>0 T = fpred \<tau> \<tau>0 T"
      and SA: "S \<subseteq> A"
  shows "fpred \<theta> \<theta>0 S = fpred \<tau> \<tau>0 S"
  by (rule factored_identification[OF finA fit SA])

subsection \<open>(b) Partition code: unseen cells are undetermined\<close>

text \<open>The partition (memorizing) code has a free output per cell: for ANY target T and any
      combination S0 outside the training set, two partition readouts exist that both fit the
      training set exactly and disagree on S0. Training says nothing about the held-out cell.\<close>
theorem partition_no_generalization:
  fixes T :: "'i set \<Rightarrow> real"
  assumes "S0 \<notin> Train"
  shows "\<exists>w w'. (\<forall>S\<in>Train. w S = T S) \<and> (\<forall>S\<in>Train. w' S = T S) \<and> w S0 \<noteq> w' S0"
proof -
  let ?w' = "T(S0 := T S0 + 1)"
  have a: "\<forall>S\<in>Train. T S = T S" by simp
  have b: "\<forall>S\<in>Train. ?w' S = T S" using assms by auto
  have c: "T S0 \<noteq> ?w' S0" by simp
  show ?thesis by (intro exI[of _ T] exI[of _ ?w'] conjI a b c)
qed

subsection \<open>(c) Sample complexity: O(A) covering examples vs Omega(2^A) cells\<close>

text \<open>The factored side of the gap, packaged: there is a training set of card A + 1 assignments
      whose fit determines the readout on all of Pow A.\<close>
theorem factored_sample_complexity:
  assumes finA: "finite A"
  shows "\<exists>Cov \<subseteq> Pow A. card Cov = card A + 1 \<and>
           (\<forall>\<theta> \<theta>0 \<tau> \<tau>0. (\<forall>T\<in>Cov. fpred \<theta> \<theta>0 T = fpred \<tau> \<tau>0 T) \<longrightarrow>
                        (\<forall>S\<in>Pow A. fpred \<theta> \<theta>0 S = fpred \<tau> \<tau>0 S))"
proof -
  have 1: "covering A \<subseteq> Pow A" unfolding covering_def by auto
  have 2: "card (covering A) = card A + 1" by (rule covering_card[OF finA])
  have 3: "\<forall>\<theta> \<theta>0 \<tau> \<tau>0. (\<forall>T\<in>covering A. fpred \<theta> \<theta>0 T = fpred \<tau> \<tau>0 T) \<longrightarrow>
             (\<forall>S\<in>Pow A. fpred \<theta> \<theta>0 S = fpred \<tau> \<tau>0 S)"
  proof (intro allI impI ballI)
    fix \<theta> \<theta>0 \<tau> \<tau>0 and S :: "'a set"
    assume fit: "\<forall>T\<in>covering A. fpred \<theta> \<theta>0 T = fpred \<tau> \<tau>0 T" and SP: "S \<in> Pow A"
    show "fpred \<theta> \<theta>0 S = fpred \<tau> \<tau>0 S"
      by (rule factored_identification[OF finA]) (use fit SP in auto)
  qed
  show ?thesis
    by (intro exI[of _ "covering A"] conjI 1 2 3)
qed

text \<open>The partition side: any training set with fewer than 2^A cells misses some combination, and
      that combination's output is a free parameter -- no sub-exponential sample size determines
      the partition readout.\<close>
theorem partition_needs_all_cells:
  assumes finA: "finite A"
      and Tr: "Train \<subseteq> Pow A"
      and less: "card Train < 2 ^ card A"
  shows "\<exists>S0 \<in> Pow A - Train. \<forall>T :: 'i set \<Rightarrow> real.
           \<exists>w w'. (\<forall>S\<in>Train. w S = T S) \<and> (\<forall>S\<in>Train. w' S = T S) \<and> w S0 \<noteq> w' S0"
proof -
  have "Pow A - Train \<noteq> {}"
  proof
    assume "Pow A - Train = {}"
    hence "Pow A \<subseteq> Train" by auto
    hence "card (Pow A) \<le> card Train"
      using Tr finA by (intro card_mono) (auto intro: finite_subset)
    thus False using less card_Pow[OF finA] by simp
  qed
  then obtain S0 where S0: "S0 \<in> Pow A - Train" by auto
  show ?thesis
  proof (rule bexI[OF _ S0], intro allI)
    fix T :: "'i set \<Rightarrow> real"
    show "\<exists>w w'. (\<forall>S\<in>Train. w S = T S) \<and> (\<forall>S\<in>Train. w' S = T S) \<and> w S0 \<noteq> w' S0"
      using S0 by (intro partition_no_generalization) auto
  qed
qed

subsection \<open>(a) Expressiveness: a conjunction is one rule, or exponentially many cells\<close>

text \<open>The conjunction over S0 is a SINGLE linear-threshold rule on the factored code: unit weights
      on S0, threshold card S0.\<close>
theorem conjunction_single_threshold:
  assumes finS0: "finite S0"
  shows "(S0 \<subseteq> S) \<longleftrightarrow> real (card S0) \<le> (\<Sum>i\<in>S0. if i \<in> S then (1::real) else 0)"
proof -
  have sum_eq: "(\<Sum>i\<in>S0. if i \<in> S then (1::real) else 0) = real (card (S0 \<inter> S))"
    using finS0 by (simp add: sum.inter_restrict[symmetric])
  show ?thesis
  proof
    assume "S0 \<subseteq> S"
    hence "S0 \<inter> S = S0" by auto
    thus "real (card S0) \<le> (\<Sum>i\<in>S0. if i \<in> S then (1::real) else 0)" by (simp add: sum_eq)
  next
    assume "real (card S0) \<le> (\<Sum>i\<in>S0. if i \<in> S then (1::real) else 0)"
    hence "card S0 \<le> card (S0 \<inter> S)" by (simp add: sum_eq)
    hence "S0 \<inter> S = S0" using finS0 by (intro card_seteq) auto
    thus "S0 \<subseteq> S" by auto
  qed
qed

text \<open>The same conjunction on the partition code occupies one cell per positive combination:
      exactly 2^(card A - card S0) cells -- exponentially many whenever S0 is small relative to A.\<close>
theorem conjunction_partition_cells:
  assumes finA: "finite A" and S0A: "S0 \<subseteq> A"
  shows "card {S \<in> Pow A. S0 \<subseteq> S} = 2 ^ (card A - card S0)"
proof -
  have bij: "bij_betw (\<lambda>S. S - S0) {S \<in> Pow A. S0 \<subseteq> S} (Pow (A - S0))"
  proof (rule bij_betwI[where g = "\<lambda>T. T \<union> S0"])
    show "(\<lambda>S. S - S0) \<in> {S \<in> Pow A. S0 \<subseteq> S} \<rightarrow> Pow (A - S0)" by auto
    show "(\<lambda>T. T \<union> S0) \<in> Pow (A - S0) \<rightarrow> {S \<in> Pow A. S0 \<subseteq> S}" using S0A by auto
    show "\<And>S. S \<in> {S \<in> Pow A. S0 \<subseteq> S} \<Longrightarrow> S - S0 \<union> S0 = S" by auto
    show "\<And>T. T \<in> Pow (A - S0) \<Longrightarrow> (T \<union> S0) - S0 = T" by auto
  qed
  have finS0: "finite S0" by (rule finite_subset[OF S0A finA])
  have "card {S \<in> Pow A. S0 \<subseteq> S} = card (Pow (A - S0))" by (rule bij_betw_same_card[OF bij])
  also have "\<dots> = 2 ^ card (A - S0)" using finA by (simp add: card_Pow)
  also have "card (A - S0) = card A - card S0"
    using finS0 S0A by (rule card_Diff_subset)
  finally show ?thesis .
qed

end
