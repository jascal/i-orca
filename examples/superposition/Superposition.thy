(*
  Superposition.thy -- features, interference, and reconstruction loss.

  A kernel-checked formalisation of the geometric core of Anthropic's "Toy Models of
  Superposition" (Elhage et al., 2022). A model embeds n features into m dimensions via
  a matrix W whose columns W_i are the feature directions; it reconstructs an input by
  x' = W^T W x. The Gram matrix W^T W has the feature norms on its diagonal and the
  pairwise INTERFERENCE <W_i, W_j> off it. The whole story of superposition is the
  trade between packing more features (n > m) and the interference that forces.

  This theory sets up the inner product over a finite coordinate set and proves the
  bridge from geometry to LOSS: reconstructing a single active (unit) feature i incurs
  squared error exactly equal to its total interference with the other features
  (recon_error_eq_interference); orthogonal features reconstruct perfectly
  (orthogonal_perfect_recovery). Welch.thy then bounds that interference from below.
*)

theory Superposition
  imports Complex_Main
begin

text \<open>Inner product of two vectors over a finite coordinate set K (the embedding
  dimension is m = card K). <x,y> = sum over coordinates of x k * y k.\<close>

definition ip :: "'k set \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> real" where
  "ip K x y = (\<Sum>k\<in>K. x k * y k)"

lemma ip_commute: "ip K x y = ip K y x"
  by (simp add: ip_def mult.commute)

text \<open>Squared reconstruction error of the one-hot input e_i under x |-> W^T W x: the
  output at feature l is <W_l, W_i>, the target is the indicator of l = i.\<close>

definition recon_error :: "'k set \<Rightarrow> ('i \<Rightarrow> 'k \<Rightarrow> real) \<Rightarrow> 'i set \<Rightarrow> 'i \<Rightarrow> real" where
  "recon_error K W I i = (\<Sum>l\<in>I. (ip K (W l) (W i) - (if l = i then 1 else 0))\<^sup>2)"

text \<open>For a UNIT feature i, the reconstruction error is exactly the total squared
  interference of i with the other features -- geometry becomes loss.\<close>

theorem recon_error_eq_interference:
  assumes finI: "finite I" and iI: "i \<in> I" and unit: "ip K (W i) (W i) = 1"
  shows "recon_error K W I i = (\<Sum>l\<in>I - {i}. (ip K (W l) (W i))\<^sup>2)"
proof -
  have "recon_error K W I i
      = (ip K (W i) (W i) - 1)\<^sup>2 + (\<Sum>l\<in>I - {i}. (ip K (W l) (W i) - (if l = i then 1 else 0))\<^sup>2)"
    unfolding recon_error_def by (simp add: sum.remove[OF finI iI])
  also have "\<dots> = (\<Sum>l\<in>I - {i}. (ip K (W l) (W i))\<^sup>2)"
    using unit by simp
  finally show ?thesis .
qed

text \<open>Orthogonal features reconstruct perfectly: zero interference, zero error.\<close>

theorem orthogonal_perfect_recovery:
  assumes finI: "finite I" and iI: "i \<in> I" and unit: "ip K (W i) (W i) = 1"
      and orth: "\<And>l. l \<in> I \<Longrightarrow> l \<noteq> i \<Longrightarrow> ip K (W l) (W i) = 0"
  shows "recon_error K W I i = 0"
proof -
  have "recon_error K W I i = (\<Sum>l\<in>I - {i}. (ip K (W l) (W i))\<^sup>2)"
    using finI iI unit by (rule recon_error_eq_interference)
  also have "\<dots> = 0" using orth by simp
  finally show ?thesis .
qed

text \<open>The same with the orthogonality premise as a bounded quantifier (surface form).\<close>

corollary orthogonal_perfect_recovery':
  assumes "finite I" and "i \<in> I" and "ip K (W i) (W i) = 1"
      and "\<forall>l\<in>I. l \<noteq> i \<longrightarrow> ip K (W l) (W i) = 0"
  shows "recon_error K W I i = 0"
  using assms by (intro orthogonal_perfect_recovery) auto

end
