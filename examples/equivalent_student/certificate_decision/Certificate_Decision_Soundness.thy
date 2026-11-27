theory Certificate_Decision_Soundness
  imports Complex_Main
begin

section \<open>Levels (copied from Quantiser_Levels)\<close>

definition level :: "real list \<Rightarrow> real \<Rightarrow> nat" where
  "level th c = length (filter (\<lambda>t. t < c) th)"

lemma length_filter_mono_pred:
  assumes "\<And>t. P t \<Longrightarrow> Q t"
  shows "length (filter P xs) \<le> length (filter Q xs)"
  using assms by (induct xs) auto

lemma length_filter_strict_mono_pred:
  assumes imp: "\<And>t. P t \<Longrightarrow> Q t" and mem: "x \<in> set xs" and np: "\<not> P x" and q: "Q x"
  shows "length (filter P xs) < length (filter Q xs)"
  using mem
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "x = y")
    case True
    have "length (filter P ys) \<le> length (filter Q ys)"
      by (rule length_filter_mono_pred[OF imp])
    with True np q show ?thesis by simp
  next
    case False
    with Cons.prems have "x \<in> set ys" by simp
    then have ih: "length (filter P ys) < length (filter Q ys)" by (rule Cons.hyps)
    show ?thesis using ih imp by (cases "P y") auto
  qed
qed

lemma level_mono:
  assumes "c \<le> c'"
  shows "level th c \<le> level th c'"
  unfolding level_def using assms by (intro length_filter_mono_pred) auto

lemma level_stable:
  assumes far: "\<And>t. t \<in> set th \<Longrightarrow> d \<le> \<bar>c - t\<bar>" and nr: "\<bar>c' - c\<bar> < d"
  shows "level th c' = level th c"
proof -
  have "\<And>t. t \<in> set th \<Longrightarrow> (t < c') = (t < c)"
  proof -
    fix t assume t: "t \<in> set th"
    from far[OF t] nr show "(t < c') = (t < c)"
      by (cases "t < c") (auto simp: abs_if split: if_splits)
  qed
  then show ?thesis unfolding level_def
    by (intro arg_cong[where f = length] filter_cong) auto
qed

lemma level_drop:
  assumes "t \<in> set th" and "t < c" and "c' \<le> t"
  shows "level th c' < level th c"
  unfolding level_def using assms
  by (intro length_filter_strict_mono_pred[of "\<lambda>u. u < c'" "\<lambda>u. u < c" t th]) auto

lemma level_rise:
  assumes "t \<in> set th" and "c \<le> t" and "t < c'"
  shows "level th c < level th c'"
  unfolding level_def using assms
  by (intro length_filter_strict_mono_pred[of "\<lambda>u. u < c" "\<lambda>u. u < c'" t th]) auto

definition thr_dist :: "real list \<Rightarrow> real \<Rightarrow> real" where
  "thr_dist th c = Min ((\<lambda>t. \<bar>c - t\<bar>) ` set th)"

lemma thr_dist_ge_iff:
  assumes "th \<noteq> []"
  shows "(d \<le> thr_dist th c) = (\<forall>t\<in>set th. d \<le> \<bar>c - t\<bar>)"
  using assms unfolding thr_dist_def by (simp add: Min_ge_iff)

section \<open>ReLU-TopK supports, relationally (any tie-break)\<close>

definition valid_support :: "nat \<Rightarrow> ('d::finite \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> bool" where
  "valid_support k z S \<longleftrightarrow>
     S \<subseteq> {i. 0 < z i} \<and> card S \<le> k \<and>
     (\<forall>j. j \<notin> S \<and> 0 < z j \<longrightarrow> card S = k \<and> (\<forall>i\<in>S. z j \<le> z i))"

lemma topk_subset_exists:
  fixes z :: "'d::finite \<Rightarrow> real" and P :: "'d set"
  shows "k \<le> card P \<Longrightarrow> \<exists>S. S \<subseteq> P \<and> card S = k \<and> (\<forall>i\<in>S. \<forall>j\<in>P - S. z j \<le> z i)"
proof (induct k)
  case 0
  show ?case by (rule exI[of _ "{}"]) simp
next
  case (Suc k)
  from Suc.prems have "k \<le> card P" by simp
  from Suc.hyps[OF this] obtain S where
    S: "S \<subseteq> P" "card S = k" "\<forall>i\<in>S. \<forall>j\<in>P - S. z j \<le> z i" by blast
  have ne: "P - S \<noteq> {}"
  proof
    assume "P - S = {}"
    then have PS: "P \<subseteq> S" by blast
    have "card P \<le> card S" by (rule card_mono) (simp_all add: PS)
    with S(2) Suc.prems show False by linarith
  qed
  define M where "M = Max (z ` (P - S))"
  have fin: "finite (z ` (P - S))" by simp
  have ne': "z ` (P - S) \<noteq> {}" using ne by simp
  have "M \<in> z ` (P - S)" unfolding M_def by (rule Max_in[OF fin ne'])
  then obtain m where m: "m \<in> P - S" "M = z m" by blast
  have Mge: "\<And>j. j \<in> P - S \<Longrightarrow> z j \<le> z m"
  proof -
    fix j assume "j \<in> P - S"
    then have "z j \<in> z ` (P - S)" by (rule imageI)
    then have "z j \<le> M" unfolding M_def by (rule Max_ge[OF fin])
    then show "z j \<le> z m" using m(2) by simp
  qed
  have a1: "insert m S \<subseteq> P" using S(1) m(1) by blast
  have a2: "card (insert m S) = Suc k" using S(2) m(1) by (simp add: card_insert_disjoint)
  have a3: "\<forall>i\<in>insert m S. \<forall>j\<in>P - insert m S. z j \<le> z i"
  proof (intro ballI)
    fix i j assume i: "i \<in> insert m S" and j: "j \<in> P - insert m S"
    from j have j': "j \<in> P - S" by blast
    show "z j \<le> z i"
    proof (cases "i = m")
      case True then show ?thesis using Mge[OF j'] by simp
    next
      case False
      with i have "i \<in> S" by blast
      with S(3) j' show ?thesis by blast
    qed
  qed
  from a1 a2 a3 show ?case by blast
qed

lemma valid_support_exists:
  fixes z :: "'d::finite \<Rightarrow> real"
  shows "\<exists>S. valid_support k z S"
proof (cases "card {i. 0 < z i} \<le> k")
  case True
  have "valid_support k z {i. 0 < z i}" using True by (auto simp: valid_support_def)
  then show ?thesis by blast
next
  case False
  then have kc: "k \<le> card {i. 0 < z i}" by linarith
  have "\<exists>S. S \<subseteq> {i. 0 < z i} \<and> card S = k \<and> (\<forall>i\<in>S. \<forall>j\<in>{i. 0 < z i} - S. z j \<le> z i)"
    using kc by (rule topk_subset_exists)
  then obtain S where S: "S \<subseteq> {i. 0 < z i}" "card S = k"
      "\<forall>i\<in>S. \<forall>j\<in>{i. 0 < z i} - S. z j \<le> z i" by blast
  have "valid_support k z S" unfolding valid_support_def using S by auto
  then show ?thesis by blast
qed

section \<open>Part A: the three checks certify support and levels\<close>

definition site_code ::
  "('d::finite \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> 'd \<Rightarrow> real" where
  "site_code th vb z S i = (if i \<in> S then vb i ! level (th i) (z i) else 0)"

definition cert_code ::
  "('d::finite \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> 'd \<Rightarrow> real" where
  "cert_code th vb lo Sel i = (if i \<in> Sel then vb i ! level (th i) (lo i) else 0)"

definition support_checks :: "nat \<Rightarrow> ('d::finite \<Rightarrow> real) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> bool" where
  "support_checks k lo hi Sel \<longleftrightarrow>
     card Sel \<le> k \<and> (\<forall>i\<in>Sel. 0 < lo i) \<and>
     (\<forall>j. j \<notin> Sel \<longrightarrow> hi j \<le> 0 \<or> (card Sel = k \<and> (\<forall>i\<in>Sel. hi j < lo i)))"

definition checks ::
  "nat \<Rightarrow> ('d::finite \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> bool" where
  "checks k th lo hi Sel \<longleftrightarrow>
     support_checks k lo hi Sel \<and> (\<forall>i\<in>Sel. level (th i) (lo i) = level (th i) (hi i))"

lemma support_unique:
  fixes z :: "'d::finite \<Rightarrow> real" and lo :: "'d \<Rightarrow> real" and hi :: "'d \<Rightarrow> real"
  assumes box: "\<And>i. lo i \<le> z i \<and> z i \<le> hi i"
    and ck: "support_checks k lo hi Sel"
    and vs: "valid_support k z S"
  shows "S = Sel"
proof -
  have cardSel: "card Sel \<le> k" using ck unfolding support_checks_def by blast
  have ok1: "\<And>i. i \<in> Sel \<Longrightarrow> 0 < lo i" using ck unfolding support_checks_def by blast
  have ok2: "\<And>j. j \<notin> Sel \<Longrightarrow> hi j \<le> 0 \<or> (card Sel = k \<and> (\<forall>i\<in>Sel. hi j < lo i))"
    using ck unfolding support_checks_def by blast
  have Spos: "\<And>i. i \<in> S \<Longrightarrow> 0 < z i" using vs unfolding valid_support_def by blast
  have cardS: "card S \<le> k" using vs unfolding valid_support_def by blast
  have out: "\<And>j. j \<notin> S \<Longrightarrow> 0 < z j \<Longrightarrow> card S = k \<and> (\<forall>i\<in>S. z j \<le> z i)"
    using vs unfolding valid_support_def by blast
  have Selpos: "\<And>i. i \<in> Sel \<Longrightarrow> 0 < z i"
  proof -
    fix i assume "i \<in> Sel"
    from ok1[OF this] box[of i] show "0 < z i" by linarith
  qed
  have SelS: "Sel \<subseteq> S"
  proof
    fix i assume i: "i \<in> Sel"
    show "i \<in> S"
    proof (rule ccontr)
      assume ni: "i \<notin> S"
      from out[OF ni Selpos[OF i]] have cS: "card S = k" and les: "\<forall>s\<in>S. z i \<le> z s" by auto
      have sub: "S \<subseteq> Sel"
      proof
        fix j assume j: "j \<in> S"
        show "j \<in> Sel"
        proof (rule ccontr)
          assume nj: "j \<notin> Sel"
          from Spos[OF j] box[of j] have "\<not> hi j \<le> 0" by linarith
          with ok2[OF nj] have "\<forall>i\<in>Sel. hi j < lo i" by blast
          with i have h1: "hi j < lo i" by blast
          from les j have h2: "z i \<le> z j" by blast
          from h1 h2 box[of i] box[of j] show False by linarith
        qed
      qed
      have "S = Sel"
      proof (rule card_seteq)
        show "finite Sel" by simp
        show "S \<subseteq> Sel" by (rule sub)
        show "card Sel \<le> card S" using cardSel cS by simp
      qed
      with i ni show False by simp
    qed
  qed
  have SSel: "S \<subseteq> Sel"
  proof
    fix j assume j: "j \<in> S"
    show "j \<in> Sel"
    proof (rule ccontr)
      assume nj: "j \<notin> Sel"
      from Spos[OF j] box[of j] have "\<not> hi j \<le> 0" by linarith
      with ok2[OF nj] have cSel: "card Sel = k" by blast
      have "Sel = S"
      proof (rule card_seteq)
        show "finite S" by simp
        show "Sel \<subseteq> S" by (rule SelS)
        show "card S \<le> card Sel" using cardS cSel by simp
      qed
      with j nj show False by simp
    qed
  qed
  from SelS SSel show "S = Sel" by blast
qed

theorem site_sound:
  fixes z :: "'d::finite \<Rightarrow> real" and lo :: "'d \<Rightarrow> real" and hi :: "'d \<Rightarrow> real"
  assumes box: "\<And>i. lo i \<le> z i \<and> z i \<le> hi i"
    and ck: "checks k th lo hi Sel"
    and vs: "valid_support k z S"
  shows "S = Sel"
    and "site_code th vb z S = cert_code th vb lo Sel"
    and "\<And>i. i \<in> Sel \<Longrightarrow> level (th i) (z i) = level (th i) (lo i)"
proof -
  have sc: "support_checks k lo hi Sel" using ck unfolding checks_def by blast
  have ok3: "\<And>i. i \<in> Sel \<Longrightarrow> level (th i) (lo i) = level (th i) (hi i)"
    using ck unfolding checks_def by blast
  show eq: "S = Sel" by (rule support_unique[OF box sc vs])   (* RISK: HO unification of box *)
  show lev: "\<And>i. i \<in> Sel \<Longrightarrow> level (th i) (z i) = level (th i) (lo i)"
  proof -
    fix i assume i: "i \<in> Sel"
    have a: "lo i \<le> z i" using box[of i] by simp
    have b: "z i \<le> hi i" using box[of i] by simp
    have "level (th i) (lo i) \<le> level (th i) (z i)" by (rule level_mono[OF a])
    moreover have "level (th i) (z i) \<le> level (th i) (hi i)" by (rule level_mono[OF b])
    ultimately show "level (th i) (z i) = level (th i) (lo i)" using ok3[OF i] by simp
  qed
  show "site_code th vb z S = cert_code th vb lo Sel"
  proof (rule ext)
    fix i show "site_code th vb z S i = cert_code th vb lo Sel i"
      by (cases "i \<in> Sel") (simp_all add: site_code_def cert_code_def eq lev)
  qed
qed

lemma abs_ltD2:
  fixes a b e :: real
  assumes "\<bar>a - b\<bar> < e"
  shows "b - e < a \<and> a < b + e"
proof -
  have h: "- e < a - b \<and> a - b < e" using assms by (simp add: abs_less_iff)
  then show ?thesis by linarith
qed

lemma abs_ltI2:
  fixes a b e :: real
  assumes "b - e < a" and "a < b + e"
  shows "\<bar>a - b\<bar> < e"
  using assms by (simp add: abs_less_iff)

section \<open>Part B: the exact robustness radius of the decision record\<close>

definition near :: "real \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> bool" where
  "near eps z z' \<longleftrightarrow> (\<forall>i. \<bar>z' i - z i\<bar> < eps)"

definition drec :: "('d::finite \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> 'd set \<times> ('d \<Rightarrow> nat)" where
  "drec th z S = (S, \<lambda>i. if i \<in> S then level (th i) (z i) else 0)"

definition robust ::
  "nat \<Rightarrow> ('d::finite \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> real \<Rightarrow> bool" where
  "robust k th z S eps \<longleftrightarrow>
     (\<forall>z' S'. near eps z z' \<and> valid_support k z' S' \<longrightarrow> drec th z' S' = drec th z S)"

definition stable_cond ::
  "nat \<Rightarrow> ('d::finite \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> real \<Rightarrow> bool" where
  "stable_cond k th z S eps \<longleftrightarrow>
     (\<forall>i\<in>S. eps \<le> z i) \<and>
     (\<forall>i\<in>S. \<forall>t\<in>set (th i). eps \<le> \<bar>z i - t\<bar>) \<and>
     (card S = k \<longrightarrow> (\<forall>i\<in>S. \<forall>j. j \<notin> S \<longrightarrow> eps \<le> (z i - z j) / 2)) \<and>
     (card S \<noteq> k \<longrightarrow> (\<forall>j. j \<notin> S \<longrightarrow> eps \<le> - z j))"

lemma near_upd1:
  assumes "0 < eps" and "\<bar>c - z i\<bar> < eps"
  shows "near eps z (z(i := c))"
  unfolding near_def using assms by auto

lemma near_upd2:
  assumes "0 < eps" and "\<bar>c - z i\<bar> < eps" and "\<bar>d - z j\<bar> < eps"
  shows "near eps z (z(i := c, j := d))"
  unfolding near_def using assms by auto

lemma not_robustI:
  assumes "near eps z z'" and "valid_support k z' S'" and "drec th z' S' \<noteq> drec th z S"
  shows "\<not> robust k th z S eps"
  using assms unfolding robust_def by blast

lemma stable_sufficient:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes vs: "valid_support k z S" and sc: "stable_cond k th z S eps"
  shows "robust k th z S eps"
  unfolding robust_def
proof (intro allI impI)
  fix z' :: "'d \<Rightarrow> real" and S' :: "'d set"
  assume h: "near eps z z' \<and> valid_support k z' S'"
  have nr: "\<And>i. \<bar>z' i - z i\<bar> < eps" using h unfolding near_def by blast
  have nrl: "\<And>i. z i - eps < z' i" using abs_ltD2[OF nr] by blast
  have nru: "\<And>i. z' i < z i + eps" using abs_ltD2[OF nr] by blast
  have vs': "valid_support k z' S'" using h by blast
  have m: "\<And>i. i \<in> S \<Longrightarrow> eps \<le> z i" using sc unfolding stable_cond_def by blast
  have tdist: "\<And>i t. i \<in> S \<Longrightarrow> t \<in> set (th i) \<Longrightarrow> eps \<le> \<bar>z i - t\<bar>"
    using sc unfolding stable_cond_def by blast
  have gap: "\<And>i j. card S = k \<Longrightarrow> i \<in> S \<Longrightarrow> j \<notin> S \<Longrightarrow> eps \<le> (z i - z j) / 2"
    using sc unfolding stable_cond_def by blast
  have zero: "\<And>j. card S \<noteq> k \<Longrightarrow> j \<notin> S \<Longrightarrow> eps \<le> - z j"
    using sc unfolding stable_cond_def by blast
  have cardS: "card S \<le> k" using vs unfolding valid_support_def by blast
  have sck: "support_checks k z' z' S"
    unfolding support_checks_def
  proof (intro conjI ballI allI impI)
    show "card S \<le> k" by (rule cardS)
  next
    fix i assume "i \<in> S"
    from m[OF this] nrl[of i] show "0 < z' i" by argo
  next
    fix j assume j: "j \<notin> S"
    show "z' j \<le> 0 \<or> (card S = k \<and> (\<forall>i\<in>S. z' j < z' i))"
    proof (cases "card S = k")
      case True
      have "\<forall>i\<in>S. z' j < z' i"
      proof
        fix i assume i: "i \<in> S"
        from gap[OF True i j] nrl[of i] nru[of j] show "z' j < z' i" by argo
      qed
      with True show ?thesis by simp
    next
      case False
      from zero[OF False j] nru[of j] have "z' j \<le> 0" by argo
      then show ?thesis by simp
    qed
  qed
  have eq: "S' = S" by (rule support_unique[OF _ sck vs']) simp
  have F: "(\<lambda>i. if i \<in> S' then level (th i) (z' i) else 0)
         = (\<lambda>i. if i \<in> S then level (th i) (z i) else 0)"
  proof (rule ext)
    fix i
    show "(if i \<in> S' then level (th i) (z' i) else 0) = (if i \<in> S then level (th i) (z i) else 0)"
    proof (cases "i \<in> S")
      case True
      have "level (th i) (z' i) = level (th i) (z i)"
        by (rule level_stable[OF tdist[OF True] nr[of i]])
      with True eq show ?thesis by simp
    next
      case False with eq show ?thesis by simp
    qed
  qed
  show "drec th z' S' = drec th z S" using eq F unfolding drec_def by simp   (* RISK: fallback below *)
qed

lemma break_margin:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes i: "i \<in> S" and zi: "0 < z i" and big: "z i < eps"
  shows "\<not> robust k th z S eps"
proof -
  have pos: "0 < eps" using zi big by argo
  define c where "c = (z i - eps) / 2"
  have cn: "\<bar>c - z i\<bar> < eps" unfolding c_def using big zi by (intro abs_ltI2) (argo+)
  have nr: "near eps z (z(i := c))" by (rule near_upd1[where eps=eps and c=c and z=z and i=i, OF pos cn])
  have cneg: "c < 0" unfolding c_def using big by argo
  obtain S' where vs': "valid_support k (z(i := c)) S'"
    using valid_support_exists[where k = k and z = "z(i := c)"] by blast
  have "i \<notin> S'"
  proof
    assume "i \<in> S'"
    with vs' have "0 < (z(i := c)) i" unfolding valid_support_def by blast
    with cneg show False by simp
  qed
  with i have "S' \<noteq> S" by blast
  then have ne: "drec th (z(i := c)) S' \<noteq> drec th z S" unfolding drec_def by simp
  show ?thesis by (rule not_robustI[OF nr vs' ne])
qed

lemma break_level:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes i: "i \<in> S" and t: "t \<in> set (th i)" and big: "\<bar>z i - t\<bar> < eps"
  shows "\<not> robust k th z S eps"
proof -
  have bd: "t - eps < z i \<and> z i < t + eps" by (rule abs_ltD2[OF big])
  have pos: "0 < eps" using bd by argo
  obtain c where c: "\<bar>c - z i\<bar> < eps" "level (th i) c \<noteq> level (th i) (z i)"
  proof (cases "t < z i")
    case True
    have tt: "t \<le> t" by simp
    have "level (th i) t < level (th i) (z i)" by (rule level_drop[OF t True tt])
    then have ne: "level (th i) t \<noteq> level (th i) (z i)" by linarith
    have nr: "\<bar>t - z i\<bar> < eps" using bd by (intro abs_ltI2) (argo+)
    show ?thesis by (rule that[OF nr ne])
  next
    case False
    then have zt: "z i \<le> t" by argo
    define c where "c = (t + z i + eps) / 2"
    have tc: "t < c" unfolding c_def using bd zt by argo
    have "level (th i) (z i) < level (th i) c" by (rule level_rise[OF t zt tc])
    then have ne: "level (th i) c \<noteq> level (th i) (z i)" by linarith
    have nr: "\<bar>c - z i\<bar> < eps" unfolding c_def using bd zt by (intro abs_ltI2) (argo+)
    show ?thesis by (rule that[OF nr ne])
  qed
  have nr: "near eps z (z(i := c))" by (rule near_upd1[where eps=eps and c=c and z=z and i=i, OF pos c(1)])
  obtain S' where vs': "valid_support k (z(i := c)) S'"
    using valid_support_exists[where k = k and z = "z(i := c)"] by blast
  have ne: "drec th (z(i := c)) S' \<noteq> drec th z S"
  proof (cases "S' = S")
    case False then show ?thesis unfolding drec_def by simp
  next
    case True
    have "(\<lambda>x. if x \<in> S' then level (th x) ((z(i := c)) x) else 0)
        \<noteq> (\<lambda>x. if x \<in> S then level (th x) (z x) else 0)"
    proof
      assume e: "(\<lambda>x. if x \<in> S' then level (th x) ((z(i := c)) x) else 0)
               = (\<lambda>x. if x \<in> S then level (th x) (z x) else 0)"
      from fun_cong[OF e, of i] True i c(2) show False by simp   (* RISK *)
    qed
    then show ?thesis unfolding drec_def by simp
  qed
  show ?thesis by (rule not_robustI[OF nr vs' ne])
qed

lemma break_zero:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes j: "j \<notin> S" and cs: "card S \<noteq> k" and zj: "z j \<le> 0" and big: "- z j < eps"
  shows "\<not> robust k th z S eps"
proof -
  have pos: "0 < eps" using zj big by argo
  define c where "c = (z j + eps) / 2"
  have cpos: "0 < c" unfolding c_def using big by argo
  have cn: "\<bar>c - z j\<bar> < eps" unfolding c_def using big zj by (intro abs_ltI2) (argo+)
  have nr: "near eps z (z(j := c))" by (rule near_upd1[where eps=eps and c=c and z=z and i=j, OF pos cn])
  obtain S' where vs': "valid_support k (z(j := c)) S'"
    using valid_support_exists[where k = k and z = "z(j := c)"] by blast
  have "S' \<noteq> S"
  proof
    assume e: "S' = S"
    have H: "\<And>x. x \<notin> S' \<Longrightarrow> 0 < (z(j := c)) x \<Longrightarrow> card S' = k"
      using vs' unfolding valid_support_def by blast
    from H[of j] j e cpos cs show False by simp
  qed
  then have ne: "drec th (z(j := c)) S' \<noteq> drec th z S" unfolding drec_def by simp
  show ?thesis by (rule not_robustI[OF nr vs' ne])
qed

lemma break_gap:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes i: "i \<in> S" and j: "j \<notin> S" and le_ji: "z j \<le> z i"
    and marg: "eps \<le> z i" and big: "(z i - z j) / 2 < eps"
  shows "\<not> robust k th z S eps"
proof -
  have pos: "0 < eps" using le_ji big by argo
  define ci where "ci = (z i + z j) / 2 - (eps - (z i - z j) / 2) / 2"
  define cj where "cj = (z i + z j) / 2 + (eps - (z i - z j) / 2) / 2"
  have ni: "\<bar>ci - z i\<bar> < eps" unfolding ci_def using big le_ji by (intro abs_ltI2) (argo+)
  have nj: "\<bar>cj - z j\<bar> < eps" unfolding cj_def using big le_ji by (intro abs_ltI2) (argo+)
  have lt: "ci < cj" unfolding ci_def cj_def using big by argo
  have cipos: "0 < ci" unfolding ci_def using big marg by argo
  have ij: "i \<noteq> j" using i j by blast
  define z' where "z' = z(i := ci, j := cj)"
  have z'i: "z' i = ci" unfolding z'_def using ij by simp
  have z'j: "z' j = cj" unfolding z'_def by simp
  have nr: "near eps z z'" unfolding z'_def by (rule near_upd2[where eps=eps and c=ci and z=z and i=i and d=cj and j=j, OF pos ni nj])
  obtain S' where vs': "valid_support k z' S'"
    using valid_support_exists[where k = k and z = z'] by blast
  have "S' \<noteq> S"
  proof
    assume e: "S' = S"
    have H: "\<And>x y. x \<notin> S' \<Longrightarrow> 0 < z' x \<Longrightarrow> y \<in> S' \<Longrightarrow> z' x \<le> z' y"
      using vs' unfolding valid_support_def by blast
    have pj: "0 < z' j" using z'j lt cipos by argo
    have "z' j \<le> z' i" using H[of j i] e i j pj by simp
    then show False using z'i z'j lt by argo
  qed
  then have ne: "drec th z' S' \<noteq> drec th z S" unfolding drec_def by simp
  show ?thesis by (rule not_robustI[OF nr vs' ne])
qed

lemma stable_necessary:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes vs: "valid_support k z S" and rb: "robust k th z S eps"
  shows "stable_cond k th z S eps"
proof -
  have Spos: "\<And>i. i \<in> S \<Longrightarrow> 0 < z i" using vs unfolding valid_support_def by blast
  have out: "\<And>j. j \<notin> S \<Longrightarrow> 0 < z j \<Longrightarrow> card S = k \<and> (\<forall>i\<in>S. z j \<le> z i)"
    using vs unfolding valid_support_def by blast
  have m: "\<And>i. i \<in> S \<Longrightarrow> eps \<le> z i"
  proof (rule ccontr)
    fix i assume i: "i \<in> S" and n: "\<not> eps \<le> z i"
    from n have big: "z i < eps" by argo
    from break_margin[where k=k and th=th and z=z and S=S and eps=eps and i=i, OF i Spos[OF i] big] rb show False by blast
  qed
  have td: "\<And>i t. i \<in> S \<Longrightarrow> t \<in> set (th i) \<Longrightarrow> eps \<le> \<bar>z i - t\<bar>"
  proof (rule ccontr)
    fix i t assume i: "i \<in> S" and t: "t \<in> set (th i)" and n: "\<not> eps \<le> \<bar>z i - t\<bar>"
    from n have big: "\<bar>z i - t\<bar> < eps" by argo
    from break_level[where k=k and th=th and z=z and S=S and eps=eps and i=i and t=t, OF i t big] rb show False by blast
  qed
  have gp: "\<And>i j. i \<in> S \<Longrightarrow> j \<notin> S \<Longrightarrow> eps \<le> (z i - z j) / 2"
  proof (rule ccontr)
    fix i j assume i: "i \<in> S" and j: "j \<notin> S" and n: "\<not> eps \<le> (z i - z j) / 2"
    from n have big: "(z i - z j) / 2 < eps" by argo
    have le_ji: "z j \<le> z i"
    proof (cases "0 < z j")
      case True from out[OF j True] i show ?thesis by blast
    next
      case False with Spos[OF i] show ?thesis by argo
    qed
    from break_gap[where k=k and th=th and z=z and S=S and eps=eps and i=i and j=j, OF i j le_ji m[OF i] big] rb show False by blast
  qed
  have zr: "\<And>j. card S \<noteq> k \<Longrightarrow> j \<notin> S \<Longrightarrow> eps \<le> - z j"
  proof (rule ccontr)
    fix j assume cs: "card S \<noteq> k" and j: "j \<notin> S" and n: "\<not> eps \<le> - z j"
    from n have big: "- z j < eps" by argo
    have zj: "z j \<le> 0"
    proof (rule ccontr)
      assume "\<not> z j \<le> 0"
      then have "0 < z j" by argo
      from out[OF j this] cs show False by simp
    qed
    from break_zero[where k=k and th=th and z=z and S=S and eps=eps and j=j, OF j cs zj big] rb show False by blast
  qed
  show ?thesis unfolding stable_cond_def using m td gp zr by blast
qed

theorem robust_iff_stable_cond:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes "valid_support k z S"
  shows "robust k th z S eps \<longleftrightarrow> stable_cond k th z S eps"
  using stable_necessary[OF assms] stable_sufficient[OF assms] by blast

text \<open>The radius as a Min, when the constraint set is non-empty (it is empty when k = 0).\<close>

definition rho_set ::
  "nat \<Rightarrow> ('d::finite \<Rightarrow> real list) \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> 'd set \<Rightarrow> real set" where
  "rho_set k th z S =
     z ` S \<union> (\<Union>i\<in>S. (\<lambda>t. \<bar>z i - t\<bar>) ` set (th i)) \<union>
     (if card S = k then (\<Union>i\<in>S. (\<lambda>j. (z i - z j) / 2) ` (- S)) else (\<lambda>j. - z j) ` (- S))"

lemma stable_cond_rho_set:
  "stable_cond k th z S eps \<longleftrightarrow> (\<forall>r\<in>rho_set k th z S. eps \<le> r)"
proof
  assume sc: "stable_cond k th z S eps"
  show "\<forall>r\<in>rho_set k th z S. eps \<le> r"
    using sc unfolding stable_cond_def rho_set_def by (cases "card S = k") auto
next
  assume H: "\<forall>r\<in>rho_set k th z S. eps \<le> r"
  have m1: "\<forall>i\<in>S. eps \<le> z i"
  proof (intro ballI)
    fix i assume i: "i \<in> S"
    have "z i \<in> rho_set k th z S" using i unfolding rho_set_def by blast
    with H show "eps \<le> z i" by blast
  qed
  have m2: "\<forall>i\<in>S. \<forall>t\<in>set (th i). eps \<le> \<bar>z i - t\<bar>"
  proof (intro ballI)
    fix i t assume i: "i \<in> S" and t: "t \<in> set (th i)"
    have "\<bar>z i - t\<bar> \<in> rho_set k th z S" using i t unfolding rho_set_def by blast
    with H show "eps \<le> \<bar>z i - t\<bar>" by blast
  qed
  have m3: "card S = k \<longrightarrow> (\<forall>i\<in>S. \<forall>j. j \<notin> S \<longrightarrow> eps \<le> (z i - z j) / 2)"
  proof (intro impI ballI allI)
    fix i j assume ck: "card S = k" and i: "i \<in> S" and j: "j \<notin> S"
    have "(z i - z j) / 2 \<in> rho_set k th z S"
      unfolding rho_set_def if_P[OF ck] using i j by blast
    with H show "eps \<le> (z i - z j) / 2" by blast
  qed
  have m4: "card S \<noteq> k \<longrightarrow> (\<forall>j. j \<notin> S \<longrightarrow> eps \<le> - z j)"
  proof (intro impI allI)
    fix j assume ck: "card S \<noteq> k" and j: "j \<notin> S"
    have "- z j \<in> rho_set k th z S"
      unfolding rho_set_def if_not_P[OF ck] using j by blast
    with H show "eps \<le> - z j" by blast
  qed
  show "stable_cond k th z S eps" unfolding stable_cond_def using m1 m2 m3 m4 by blast
qed

lemma finite_rho_set: "finite (rho_set k th z S)"
  unfolding rho_set_def by simp

corollary robust_iff_le_rho:
  fixes z :: "'d::finite \<Rightarrow> real"
  assumes vs: "valid_support k z S" and ne: "rho_set k th z S \<noteq> {}"
  shows "robust k th z S eps \<longleftrightarrow> eps \<le> Min (rho_set k th z S)"
  unfolding robust_iff_stable_cond[OF vs] stable_cond_rho_set
  using finite_rho_set[of k th z S] ne by (simp add: Min_ge_iff)

lemma robust_k0: "robust 0 th z {} eps"   (* RISK *)
  unfolding robust_def valid_support_def drec_def by auto

section \<open>Part C: lifting through the sites, and the verdict\<close>

definition in_box :: "('i \<Rightarrow> real) \<times> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> bool" where
  "in_box b f \<longleftrightarrow> (\<forall>i. fst b i \<le> f i \<and> f i \<le> snd b i)"

definition cert_top :: "('c \<Rightarrow> real) \<times> ('c \<Rightarrow> real) \<Rightarrow> 'c \<Rightarrow> bool" where
  "cert_top b c \<longleftrightarrow> (\<forall>c'. c' \<noteq> c \<longrightarrow> snd b c' < fst b c)"

definition is_argmax :: "('c \<Rightarrow> real) \<Rightarrow> 'c \<Rightarrow> bool" where
  "is_argmax f c \<longleftrightarrow> (\<forall>c'. f c' \<le> f c)"

lemma cert_top_strict:
  assumes bx: "in_box b f" and ct: "cert_top b c" and ne: "c' \<noteq> c"
  shows "f c' < f c"
proof -
  from ct ne have "snd b c' < fst b c" unfolding cert_top_def by blast
  moreover have "f c' \<le> snd b c'" using bx unfolding in_box_def by blast
  moreover have "fst b c \<le> f c" using bx unfolding in_box_def by blast
  ultimately show ?thesis by linarith
qed

lemma cert_top_is_argmax:
  assumes bx: "in_box b f" and ct: "cert_top b c"
  shows "is_argmax f c"
  unfolding is_argmax_def
proof
  fix c' show "f c' \<le> f c"
  proof (cases "c' = c")
    case True then show ?thesis by simp
  next
    case False from cert_top_strict[OF bx ct False] show ?thesis by linarith
  qed
qed

lemma cert_top_argmax:
  assumes bx: "in_box b f" and ct: "cert_top b c" and am: "is_argmax f a"
  shows "a = c"
proof (rule ccontr)
  assume ne: "a \<noteq> c"
  have "f a < f c" by (rule cert_top_strict[OF bx ct ne])
  moreover have "f c \<le> f a" using am unfolding is_argmax_def by blast
  ultimately show False by linarith
qed

locale certified_run =
  fixes k :: "nat \<Rightarrow> nat"
    and th :: "nat \<Rightarrow> 'd::finite \<Rightarrow> real list"
    and vb :: "nat \<Rightarrow> 'd \<Rightarrow> real list"
    and pre :: "nat \<Rightarrow> 'v \<Rightarrow> 'p \<Rightarrow> 'd \<Rightarrow> real"
    and upd :: "nat \<Rightarrow> ('p \<Rightarrow> 'd \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v"
    and sel :: "nat \<Rightarrow> 'v \<Rightarrow> 'p \<Rightarrow> 'd set"
    and readout :: "'v \<Rightarrow> 'c \<Rightarrow> real"
    and gamma :: "'a \<Rightarrow> 'v set"
    and apre :: "nat \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> ('d \<Rightarrow> real) \<times> ('d \<Rightarrow> real)"
    and aupd :: "nat \<Rightarrow> ('p \<Rightarrow> 'd \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a"
    and asel :: "nat \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> 'd set"
    and areadout :: "'a \<Rightarrow> ('c \<Rightarrow> real) \<times> ('c \<Rightarrow> real)"
  assumes sel_valid: "\<And>l v p. valid_support (k l) (pre l v p) (sel l v p)"
    and pre_sound: "\<And>l v a p. v \<in> gamma a \<Longrightarrow> in_box (apre l a p) (pre l v p)"
    and upd_sound: "\<And>l c v a. v \<in> gamma a \<Longrightarrow> upd l c v \<in> gamma (aupd l c a)"
    and readout_sound: "\<And>v a. v \<in> gamma a \<Longrightarrow> in_box (areadout a) (readout v)"
begin

definition xcode :: "nat \<Rightarrow> 'v \<Rightarrow> 'p \<Rightarrow> 'd \<Rightarrow> real" where
  "xcode l v = (\<lambda>p. site_code (th l) (vb l) (pre l v p) (sel l v p))"

definition acode :: "nat \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> 'd \<Rightarrow> real" where
  "acode l a = (\<lambda>p. cert_code (th l) (vb l) (fst (apre l a p)) (asel l a p))"

definition site_ok :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "site_ok l a \<longleftrightarrow> (\<forall>p. checks (k l) (th l) (fst (apre l a p)) (snd (apre l a p)) (asel l a p))"

primrec xrun :: "nat \<Rightarrow> 'v \<Rightarrow> 'v" where
  "xrun 0 v = v"
| "xrun (Suc l) v = upd l (xcode l (xrun l v)) (xrun l v)"

primrec arun :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "arun 0 a = a"
| "arun (Suc l) a = aupd l (acode l (arun l a)) (arun l a)"

lemma code_agree:
  assumes v: "v \<in> gamma a" and ok: "site_ok l a"
  shows "xcode l v = acode l a"
proof (rule ext)
  fix p
  have b: "in_box (apre l a p) (pre l v p)" by (rule pre_sound[OF v])
  have box: "\<And>i. fst (apre l a p) i \<le> pre l v p i \<and> pre l v p i \<le> snd (apre l a p) i"
    using b unfolding in_box_def by blast
  have ck: "checks (k l) (th l) (fst (apre l a p)) (snd (apre l a p)) (asel l a p)"
    using ok unfolding site_ok_def by blast
  have "site_code (th l) (vb l) (pre l v p) (sel l v p)
      = cert_code (th l) (vb l) (fst (apre l a p)) (asel l a p)"
    by (rule site_sound(2)[OF box ck sel_valid])   (* RISK: HO unification *)
  then show "xcode l v p = acode l a p" unfolding xcode_def acode_def by simp
qed

lemma run_sound:
  assumes v0: "v0 \<in> gamma a0" and oks: "\<And>l. l < n \<Longrightarrow> site_ok l (arun l a0)"
  shows "l \<le> n \<Longrightarrow> xrun l v0 \<in> gamma (arun l a0)"
proof (induct l)
  case 0 show ?case using v0 by simp
next
  case (Suc l)
  from Suc.prems have lt_n: "l < n" by simp
  then have "l \<le> n" by simp
  then have IH: "xrun l v0 \<in> gamma (arun l a0)" by (rule Suc.hyps)
  have ce: "xcode l (xrun l v0) = acode l (arun l a0)" by (rule code_agree[OF IH oks[OF lt_n]])
  have "upd l (xcode l (xrun l v0)) (xrun l v0) \<in> gamma (aupd l (xcode l (xrun l v0)) (arun l a0))"
    by (rule upd_sound[OF IH])
  then show ?case using ce by simp
qed

theorem certified_codes:
  assumes v0: "v0 \<in> gamma a0" and oks: "\<And>l. l < n \<Longrightarrow> site_ok l (arun l a0)"
    and lt_n: "l < n"
  shows "xcode l (xrun l v0) = acode l (arun l a0)"
proof -
  from lt_n have le: "l \<le> n" by simp
  have "xrun l v0 \<in> gamma (arun l a0)" by (rule run_sound[OF v0 oks le])
  then show ?thesis by (rule code_agree[OF _ oks[OF lt_n]])
qed

theorem verdict_sound:
  fixes hf :: "'c \<Rightarrow> real"
  assumes v0: "v0 \<in> gamma a0" and oks: "\<And>l. l < n \<Longrightarrow> site_ok l (arun l a0)"
    and hbox: "in_box hb hf" and htop: "cert_top hb ht"
    and stop: "cert_top (areadout (arun n a0)) st"
    and ha: "is_argmax hf x" and sa: "is_argmax (readout (xrun n v0)) y"
  shows "ht = st \<Longrightarrow> x = y" and "ht \<noteq> st \<Longrightarrow> x \<noteq> y"
    and "is_argmax hf ht" and "is_argmax (readout (xrun n v0)) st"
proof -
  have "xrun n v0 \<in> gamma (arun n a0)" by (rule run_sound[OF v0 oks le_refl])
  then have sbox: "in_box (areadout (arun n a0)) (readout (xrun n v0))" by (rule readout_sound)
  have ex: "x = ht" by (rule cert_top_argmax[OF hbox htop ha])
  have ey: "y = st" by (rule cert_top_argmax[OF sbox stop sa])
  show "ht = st \<Longrightarrow> x = y" using ex ey by simp
  show "ht \<noteq> st \<Longrightarrow> x \<noteq> y" using ex ey by simp
  show "is_argmax hf ht" by (rule cert_top_is_argmax[OF hbox htop])
  show "is_argmax (readout (xrun n v0)) st" by (rule cert_top_is_argmax[OF sbox stop])
qed

end

end
