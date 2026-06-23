(*
  PIC_Forward.thy -- the forward pass IS a least fixpoint (lfp(layer program) = the model decode).

  Closes the PIC-LP open item: a single end-to-end theorem connecting the lfp semantics (PIC_Logic) to
  the numeric forward pass. The transformer forward pass is the lfp of a LAYERED Datalog program:

    atom (l, x)  =  "at layer l the residual is x"
    fact  ({}, (0, r0))                          -- the embedding (layer-0 residual)
    rule  ({(l, x)}, (Suc l, step l x))          -- one layer step (the encoder write at layer l)

  We prove the least model is EXACTLY the forward trajectory:

    layer_computed     : (l, R l) is in the lfp for every layer  (>= direction)
    lfp_is_trajectory  : answer (Player) = { (l, R l) | l }       (the lfp = the forward pass, exactly)
    lfp_determines     : any (l, r) in the lfp has r = R l        (no spurious residual -- the decode
                                                                   residual is pinned)

  So at depth L the lfp exposes the single forward residual R L, against which the frame read-out
  <R L, U_v> + b_v IS the model's decode (PIC_SPEC decode side). `step` is left abstract -- any per-layer
  residual update; the PIC encoder (PIC_Core.pic_encoder) is the instance step l x = x + enc-write.

  Self-contained over PIC_Logic; 0 sorry, quick_and_dirty = false. Companion to pic/spec/PIC_LP.md.
*)
theory PIC_Forward
  imports PIC_Logic
begin

section \<open>The forward pass as a least fixpoint\<close>

text \<open>The forward residual at each layer: @{term r0} at the embedding, then one @{term step} per layer.\<close>
primrec Rstep :: "(nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "Rstep s r0 0 = r0"
| "Rstep s r0 (Suc l) = s l (Rstep s r0 l)"

text \<open>The layered program: the embedding fact + one clause per layer step.\<close>
definition Player :: "(nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ((nat \<times> 'a) clause) set" where
  "Player s r0 = insert ({}, (0, r0)) {({(l, x)}, (Suc l, s l x)) | l x. True}"

text \<open>The forward trajectory as a set of (layer, residual) atoms.\<close>
definition traj :: "(nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a) set" where
  "traj s r0 = {(l, Rstep s r0 l) | l. True}"

lemma mem_traj [simp]: "((a, b) \<in> traj s r0) = (b = Rstep s r0 a)"
  by (auto simp: traj_def)

text \<open>(\<ge>) The lfp computes the forward residual at every layer.\<close>
theorem layer_computed: "(l, Rstep s r0 l) \<in> answer (Player s r0)"
proof (induct l)
  case 0
  have "({}, (0, r0)) \<in> Player s r0" by (simp add: Player_def)
  from answer_closed[OF this] show ?case by simp
next
  case (Suc l)
  have mem: "({(l, Rstep s r0 l)}, (Suc l, s l (Rstep s r0 l))) \<in> Player s r0"
    by (auto simp: Player_def)
  from answer_closed[OF mem] Suc have "(Suc l, s l (Rstep s r0 l)) \<in> answer (Player s r0)" by simp
  thus ?case by simp
qed

text \<open>The trajectory is closed under the program's immediate-consequence operator (a model).\<close>
lemma traj_closed: "Tp (Player s r0) (traj s r0) \<subseteq> traj s r0"
proof
  fix z assume "z \<in> Tp (Player s r0) (traj s r0)"
  then consider "z \<in> traj s r0"
    | B where "(B, z) \<in> Player s r0" and "B \<subseteq> traj s r0"
    unfolding Tp_def by blast
  thus "z \<in> traj s r0"
  proof cases
    case 1 thus ?thesis .
  next
    case (2 B)
    from \<open>(B, z) \<in> Player s r0\<close> consider "(B, z) = ({}, (0, r0))"
      | l x where "(B, z) = ({(l, x)}, (Suc l, s l x))"
      unfolding Player_def by blast
    thus ?thesis
    proof cases
      case 1 thus ?thesis by (simp add: traj_def)
    next
      case (2 l x)
      hence "(l, x) \<in> traj s r0" using \<open>B \<subseteq> traj s r0\<close> by auto
      hence "x = Rstep s r0 l" by simp
      with \<open>(B, z) = ({(l, x)}, (Suc l, s l x))\<close> show ?thesis by (auto simp: traj_def)
    qed
  qed
qed

text \<open>(=) Hence the least model is EXACTLY the forward trajectory: the layer program's lfp is the
  forward pass.\<close>
theorem lfp_is_trajectory: "answer (Player s r0) = traj s r0"
proof
  show "answer (Player s r0) \<subseteq> traj s r0" using traj_closed by (rule answer_least)
  show "traj s r0 \<subseteq> answer (Player s r0)" using layer_computed by (auto simp: traj_def)
qed

text \<open>So the lfp pins the decode residual: any (l, r) it contains has r = R l (no spurious residual).\<close>
corollary lfp_determines: "(l, r) \<in> answer (Player s r0) \<Longrightarrow> r = Rstep s r0 l"
  by (simp add: lfp_is_trajectory)

section \<open>End-to-end: the lfp determines the model decode\<close>

text \<open>At depth @{term L} the lfp exposes the single forward residual @{term "Rstep s r0 L"}; the model's
  decode logits are its frame read-out, so the lfp determines the decode. (Frame-side: PIC_SPEC \<section>4.)\<close>
context pic_frame
begin

corollary lfp_final_residual_unique:
  "answer (Player s r0) \<inter> ({L} \<times> UNIV) = {(L, Rstep s r0 L)}"
  by (auto simp: lfp_is_trajectory traj_def)

text \<open>The model logit on input residual @{term "Rstep s r0 L"} -- what the decode argmaxes over -- is
  exactly the read-out of the lfp's final-layer fact.\<close>
corollary lfp_decode_logits:
  assumes "(L, r) \<in> answer (Player s r0)"
  shows "inner r (U v) + b v = inner (Rstep s r0 L) (U v) + b v"
proof -
  have "r = Rstep s r0 L" using assms by (rule lfp_determines)
  thus ?thesis by simp
qed

end

end
