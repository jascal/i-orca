# PIC × tensor-product binding — an i-orca work package (see the tag ledger for what is `proved`)

**For:** an i-orca agent (Isabelle-kernel-checked proofs).
**Source:** McCoy, Soulos, Linzen & Smolensky (2026), *The Emergent Symbolic Structure of Artificial Neural
Networks*, arXiv:2608.29530. They report that hidden states of MLPs, GRUs, Transformers and seven LLMs are closely
approximated by **linearly-transformed tensor product representations** (TPRs):

> `E ≈ W(Σᵢ fᵢ ⊗ rᵢ) + b`, with fillers `fᵢ` and roles `rᵢ`.

**Purpose:** to state, in PIC terms (`pic/spec/PIC_SPEC.md` v0.3.4), the frame-side and decision-side facts that hold
*if* sources or residuals have this form. Each statement composes lemmas i-orca already has. Proposed home: a new
`pic_core/PIC_Binding.thy`.

## Discipline

- **Every item here is `open` until it exists in i-orca** (see the tag ledger below for what now does). Several have short classical proofs (sketched). That makes
  them *tractable*, not `proved`. Cite the `.thy` file and lemma before changing any tag in PIC_SPEC.
- **The paper is `empirical`** (sampled test sets, hand-chosen role schemes, templated stimuli). A proved T-theorem is
  a statement about TPR-shaped geometry. It is **not** evidence that any particular model is TPR-shaped. The paper's
  fit quality is not evidence for any theorem.
- **State the domain.** All statements are over finite filler and role sets, with the unit-norm / bias-free conventions
  of §5.1–5.3 unless stated otherwise.
- **Numerical checks are not support.** T1–T3 were checked on random frames (T1 and T2 to machine precision; T3 with
  0 violations in 4,540 cases where its condition held). That only catches a bug in implementing the sketch. A
  sufficient condition yields zero violations by construction. The check says nothing about tightness, the distance
  to the boundary, or the failure side, where the condition is false and decoding still succeeds. **T4–T6 were not
  checked at all.** No sibling repo may cite any T-item as a certificate until its `.thy` lemma exists.

## Tag ledger (2026-10-04)

The kernel-checked substrate is `examples/pic_core/PIC_Binding.thy` (session `PIC_Core`, `quick_and_dirty = false`,
0 sorry). The i-orca surface is `examples/pic_binding/pic_binding.i.orca.md`, checked with
`i-orca check … -d examples/pic_core --session PIC_Core`. All 23 surface theorems are kernel-checked
(`formal_fraction_real = 1.000` each).

| item | status | lemma(s) in `PIC_Binding.thy` |
|---|---|---|
| T0 bound incidence | `open` (definitional; not encoded) | — |
| T1 absolute coherence `μ(F⊗R) = max(μ_F, μ_R)` | **`proved`** | `tensor_coherence` |
| T1 signed coherence (the form to encode) | **`proved`** | `tensor_signed_coherence` |
| T1′ optimal margin ≥ 1 − signed coherence | **`proved`** | `tensor_optimal_margin` |
| T2 claims 1–3 (diagonal-inclusive FP, Welch value, ratio) | **`proved`** | `tensor_frame_potential`, `tensor_welch_value`, `tensor_fp_welch_ratio` |
| T2 claim 4 (tensor of tight frames is tight) | `open` | — |
| T3 matched-filter unbinding, one factor of 2 | **`proved`** | `unbind_certified` |
| T4 (a)–(c) | `open` | — |
| T5(a) last-layer substitution | **`proved`** | `substitution_certified`, `substitution_certified_max`, `substitution_certified_norm` |
| T5(a), pairwise, EXACT (iff): `L(t) − L(v) > ⟨r − r̂, U_t − U_v⟩` ∀ rivals | **`proved`** | `substitution_pairwise_iff`, `substitution_certified_pairwise` |
| uniform T5(a) ⟹ pairwise (pairwise is at least as strong) | **`proved`** | `uniform_implies_pairwise` |
| hybrid: pairwise on a rival set K + norm tail bound outside K | **`proved`** | `substitution_certified_hybrid` |
| T5(b) uniform over a domain (given ‖r − r̂‖ ≤ ε on all of D) | **`proved`** | `substitution_domain_norm`, `substitution_domain_pairwise` |
| T5(b) the per-rival domain form is at least as strong (norm premises with ε ≥ 0 ⟹ per-rival premises) | **`proved`** | `domain_norm_implies_pairwise`, `domain_norm_premise_implies_pairwise` |
| T5(b) premise: a bound on the fit error off the evaluated contexts | `open` | — |
| T5(c) hull ceiling (bias-free): a margin-threshold certificate needs `m < ‖r‖·hdist(t)` | **`proved`** | `hull_margin_upper_scaled`, `certificate_hull_ceiling`, `substitution_hull_ceiling` |
| T5(c) biased, via the lift `(U_v, b_v/s)`: `m < ‖(w, s)‖·hdist_lifted(t)` for every `s > 0` (upper bound) | **`proved`** | `certificate_hull_ceiling_biased` |
| T6 (a), (b) | `open` | — |

The tensor product is a concrete construction, `tprod f r = (χ i. f$i *⇩R r)` in `real^'m^'n`. The identity
`⟨f⊗r, g⊗s⟩ = ⟨f,g⟩⟨r,s⟩` is the proved lemma `inner_tprod`, not an assumption.

What `proved` covers:
- The geometry of TPR-shaped frames, and the decision-side substitution certificate.
- Nothing about whether any model is TPR-shaped.
- Empirical use: pil `docs/notes/tpr_substitution_certificate.md` (coverage of the certificate on GPT-2) and lm-sae
  `docs/TPR_SYSTEMATICITY_PREREG.md` (the representational test).

## Setup and notation

- **Fillers** `F = {f_a}_{a∈A} ⊂ ℝ^{d_F}` and **roles** `R = {r_s}_{s∈S} ⊂ ℝ^{d_R}`, both **unit-norm**.
- **Coherences:** `μ_F = max_{a≠b} |⟨f_a,f_b⟩|` and `μ_R = max_{s≠t} |⟨r_s,r_t⟩|`. Signed per-element versions
  `μ^F_a = max_{b≠a} ⟨f_a,f_b⟩` follow §5.3's `μ_t`.
- **Bound frame** `B = {f_a ⊗ r_s}` ⊂ `ℝ^{d_F d_R}`, with `|B| = |A|·|S|`. Every element has unit norm.
- **A structure** `σ` is a partial map from roles to fillers, with `k = |dom σ|` bound pairs. Its TPR is
  `T(σ) = Σ_{s∈dom σ} f_{σ(s)} ⊗ r_s`, realised in the residual as `x(σ) = W·T(σ) + b`, where
  `W : ℝ^{d_F d_R} → ℋ = ℝ^d`.
- **Frame potential** `FP(X) = Σ_{i,j} ⟨x_i,x_j⟩²` (diagonal included) and Welch value `W(X) = n²/d`, as in pil's
  `fp/welch`.

---

## T0 — Bound incidence (definitional; the PIC-native refinement)

**Claim.** For a source of TPR form `d_j = W(f ⊗ r)`, the incidence on token `v` is a **bilinear form**:

> `c_j(v) = ⟨W(f⊗r), U_v⟩ = fᵀ M_v r`, where `M_v ∈ ℝ^{d_F×d_R}` is `Wᵀ U_v` reshaped.

**Why it matters.**
- PIC's incidence `j ▷ v` (§2.5) is currently a scalar per (source, token). T0 types it by the source's binding.
- Additivity across bound pairs (the paper's "the whole is the sum of the parts", which underlies its constituent
  edits) is then exactly PIC's `⊗` = real `+` over sources (§1.3).
- Multiplicativity is *inside* each source.

**Proof.** Linear algebra (`vec(f rᵀ)` and the adjoint of `W`).
**Tractability:** trivial; mostly an encoding decision.

## T1 — Binding does not raise coherence

**Claim.** If `|A|, |S| ≥ 2`, then `μ(B) = max(μ_F, μ_R)`.

**Proof sketch.**
- The identity `⟨f_a⊗r_s, f_b⊗r_t⟩ = ⟨f_a,f_b⟩⟨r_s,r_t⟩` holds.
- Distinct pairs differ in the filler, the role, or both.
- If only one differs, the inner product is that factor's inner product: the other factor is 1.
- If both differ, `|·| ≤ μ_F μ_R ≤ min(μ_F, μ_R)`.

**Corollary T1′ (decodability of bound pairs).** By `optimal_margin_coherence_sandwich` (`PIC_Margin_Hull.thy`),
every bound pair `(a,s)` used as a unit decode direction has optimal margin at least `1 − max(μ_F, μ_R)`.
- Signed form: at least `1 − max(μ^F_a, μ^R_s, max_{b≠a, t≠s} ⟨f_a,f_b⟩⟨r_s,r_t⟩)`.
- Note: the last term can be positive even when both factors' signed coherences are negative.

**Encode the signed form, not the absolute-value slogan.** `1 − max(μ_F, μ_R)` is only a lower bound. Because the
both-differ term can be positive when both signed coherences are negative, the signed per-pair margin is the
statement worth kernel-checking.

**Tractability:** high. The lemma is two case splits. T1′ composes with an existing theorem.

## T2 — Frame potential and the Welch ratio are multiplicative

**Convention (load-bearing).** Here `FP` **includes the diagonal**, `FP(X) = Σ_{i,j}⟨x_i,x_j⟩²`, and
`W(X) = n²/d` is its Welch value. Only in this convention do the claims below factor. The off-diagonal form
`Σ_{i≠j}⟨x_i,x_j⟩² ≥ n(n−d)/d` does **not** factor the same way.

**Claims.**
1. `FP(B) = FP(F)·FP(R)`.
2. `W(B) = W(F)·W(R)`, because `|B|²/(d_F d_R)` factors.
3. Hence `FP(B)/W(B) = (FP(F)/W(F))·(FP(R)/W(R))`.
4. In particular, the tensor product of two tight frames is tight:
   `Σ (f⊗r)(f⊗r)ᵀ = (Σ f fᵀ) ⊗ (Σ r rᵀ)`.

**Why it matters, and what it does not predict.** In the diagonal-inclusive convention, binding *multiplies* the two
factors' ratios to the Welch value. pil's reported `fp/welch` uses the **other** convention:
- `geometry.frame_potential` is the off-diagonal mean `Σ_{i≠j}⟨·,·⟩² / (n(n−1))`;
- `geometry.welch_bound` is `(n−d)/(d(n−1))`.

That ratio does not factor. So T2 makes **no** "1.1 × 1.1 = 1.21" prediction about pil's number. A prediction for
pil has to be restated in pil's convention, or pil has to report the diagonal-inclusive ratio. For unit vectors the
conversion is `FP_incl = n + n(n−1)·fp_pil`.

**Proof.** Expand the double sum over pairs; it factors. Tightness via the Kronecker identity.
**Tractability:** high. It needs a Kronecker / tensor-product carrier in the Isabelle library, or `vec` reshaping
over `real^(n×m)`.

## T3 — Unbinding certificate (matched-filter role readout)

**Setting.** Read the filler in role `s` from `T(σ)` with the matched filter `r_s`, giving `y_s = T(σ) r_s`. Then
decode the filler by argmax over `F`, with scores `L(b) = ⟨y_s, f_b⟩`.

**Claim.** The decoded filler is `σ(s)` whenever

> `1 − μ^F_{σ(s)} > 2(k−1) μ_R`.

**Proof sketch.**
- Decompose: `L(b) = ⟨f_{σ(s)}, f_b⟩ + Σ_{t≠s} ⟨r_t,r_s⟩⟨f_{σ(t)},f_b⟩`.
- The first term has matched-filter margin `1 − μ^F_{σ(s)}` (`mfmargin_unit`).
- The crosstalk is a per-token perturbation bounded by `δ = (k−1)μ_R`, using unit norms and Cauchy–Schwarz.
- `decode_margin_certified` finishes it, with the same tightness caveat.

**Pin the constant before encoding.** The factor 2 enters **once**, from `decode_margin_certified`
(`margin > 2δ` for a per-score perturbation `|L′(b) − L(b)| ≤ δ`). Here `δ` must be the **per-score** crosstalk bound:
`|Σ_{t≠s}⟨r_t,r_s⟩⟨f_{σ(t)},f_b⟩| ≤ (k−1)μ_R`, since each `|⟨f_{σ(t)},f_b⟩| ≤ 1`.
- Do not bound the *difference* of two scores inside `δ`.
- Do not then apply the lemma's 2 again.

Either would double-count to `4(k−1)μ_R`. That is still sound, but it is a different, weaker statement.

**Why it matters.** This states the paper's "unbinding is exact when roles are independent" quantitatively and
non-asymptotically, in PIC's own certificate. It is exactly a frame-side condition on the role frame.
- With **dual** roles (exists iff `R` is linearly independent, so `|S| ≤ d_R`) the crosstalk vanishes.
- With `|S| > d_R`, `encoder_superposition` / `routing_superposition` force dependence and the dual does not exist.
  The matched-filter bound above is then what remains.

**Tractability:** high. It composes three existing lemmas.

## T4 — Compressed binding (superposition of bound pairs)

**Setting.** `d < |B|`: the paper's `W` maps the `d_F d_R`-dimensional tensor space into a smaller residual.

**Claims.**
- **(a)** When `|B| > d`, the realised bound directions `{W(f⊗r)}` are linearly dependent
  (`encoder_superposition`, applied to `B`).
- **(b)** Normalised, they obey the Welch floor `Σ_{i≠j}⟨·,·⟩² ≥ |B|(|B|−d)/d` (`welch_sos`).
- **(c) — open.** Suppose `W` is an `ε`-near-isometry on the difference set of `B`:
  `(1−ε)‖x‖² ≤ ‖Wx‖² ≤ (1+ε)‖x‖²` for every `x ∈ B − B`. Then T1′ and T3 hold with margins degraded by `O(ε)`.

**Why it matters.** This is the frame-side reason TPR structure and superposition are not rivals. The paper's 2–3K
role vocabularies in 2880-dimensional GPT-OSS force (a) and (b).
**Tractability:** (a) and (b) are corollaries of existing theorems. (c) needs the constant worked out.

## T5 — Last-layer substitution is certified by the margin theorem

**Setting.**
- `r` is the decode-input residual: after the final norm, which PIC folds into the frame (§1.4).
- `r̂ = W·T(σ) + b` is a TPR fit to it.
- Logits are `L(v) = ⟨r,U_v⟩ + b_v` and `L̂(v) = ⟨r̂,U_v⟩ + b_v`.
- `t = argmax L`.

**Claims.**
- **(a) Per context.** If `margin(L,V,t) > 2 max_v |⟨r − r̂, U_v⟩|`, then `argmax L̂ = t`. This is
  `decode_margin_certified` with `δ = max_v |⟨r − r̂, U_v⟩| ≤ u_max ‖r − r̂‖`.
- **(b) Uniform over a domain.** Suppose that on a set `D` of contexts, `‖r(x) − r̂(x)‖ ≤ ε` and
  `margin(L_x,V,t_x) > 2 u_max ε` for all `x ∈ D`. Then substituting the TPR preserves every decision on `D`.
  The certificate covers `D`, not only the sampled points, provided `ε` bounds the fit error on all of `D`.
- **(c) Hull ceiling (as proved).** For a **bias-free** decode and a residual of **any** norm, a certificate that
  needs every margin `⟨r, U_t⟩ − ⟨r, U_v⟩ > m` can fire only if `m < ‖r‖·hdist(t)`, where `hdist(t)` is the
  distance from `U_t` to the convex hull of its rivals. It bounds **threshold** certificates only (uniform, norm,
  the hybrid tail), not the exact pairwise iff. The ceiling is set by the frame `U` and `‖r‖`: it is independent of
  the substitute, **not** of the model. With a per-token bias, the lift `(U_v, b_v/s)` gives an upper bound for
  every `s > 0` (`certificate_hull_ceiling_biased`).

**Why it matters.** The paper's evidence that substitution preserves behaviour is a sampled accuracy (within 2.4
points on GPT-OSS). At the last layer, T5 turns that into a per-input, and conditionally domain-wide, **proof**, using
only decision-side machinery PIC already has. At earlier layers the downstream map is nonlinear, so no such
certificate is available. That boundary should be stated, not crossed.

**Scope warning.** For a substitution *before* the final RMSNorm/LayerNorm, (a) and (b) need a Lipschitz bound for the
norm on `{‖x‖ ≥ m}`. That bound is `open` and not attempted here.

**Tractability:** (a) and (b) are immediate instances of `decode_margin_certified`. (c) is immediate from
`gdecodable_iff_hull_dist`.

**Status (2026-10-04).** (b) and (c) are kernel-checked (see the ledger). Two refinements of the claims above:
- (b) is proved as stated, plus a per-rival form (`margin over v > ε·‖U_t − U_v‖`) that is at least as strong. Its
  premise, an error bound on *all* of `D`, is exactly the part that stays `open` for unevaluated contexts.
- (c) is proved for any residual norm: a margin-threshold certificate needs `m < ‖r‖·hdist(t)`. The ceiling is
  **independent of the substitute**, not of the model: it is set by the frame `U` and `‖r‖`. It bounds threshold
  certificates (uniform, norm, hybrid tail) only; the exact pairwise certificate is an iff and has no ceiling.

## T6 — What "projection" can and cannot widen (sets up the pil experiment)

**Claim (a).** Let `P` be the orthogonal projection onto a subspace `Π` containing every readout difference
`U_t − U_v`. Then `⟨Pr, U_t − U_v⟩ = ⟨r, U_t − U_v⟩` for all `t, v`. So **linear** projection onto such a subspace
leaves every margin unchanged.

**Consequence.** The paper's denoising gain cannot come from linear projection in the readout's own span. On complex
sentences, its unpacking decoder scored 0.96 on TPR approximations versus 0.71 on real encodings. That gain must come
from one of:
- **(i)** readout components outside `Π`;
- **(ii)** a nonlinear reader; or
- **(iii)** *snapping*. DISCOVER's `r̂` is computed from the gold structure `σ`, not from `r`. It replaces `r` by an
  ideal code point. Its deployable analogue is unbind → nearest filler → rebind, the "clean-up memory" of vector
  symbolic architectures.

**Claim (b) — open.** If the ideal points `{x(σ)}` form a `γ`-code in the readout geometry, and `r = x(σ) + n` with
`‖n‖ < γ/2`, then clean-up returns `x(σ)` exactly. It therefore raises the decision margin to the code's margin. This
is the PIC reading of the paper's "limitivism": the model realises a noisy point, and clean-up restores the code
point's margin.

**Tractability:** (a) trivial. (b) needs a careful statement of the clean-up operator; T3 supplies the unbinding step.

**What has *not* tested T6(a).** pil#132 projected onto `span(W)` of a fitted TPR. There only 44% of
`‖U_gold − U_rival‖²` lay inside the subspace, so (a)'s hypothesis was false at that site. Its margin change
(3.80 → 3.39) is consistent with removing out-of-span components. It is neither a test nor a refutation of (a).

---

## Suggested order

1. T1, T2 and T3 first: short, and they compose existing lemmas.
2. Then T5(a)/(b)/(c), which produces the certificate a substitution experiment can cite.
3. Then T6(a).
4. T4(c), T6(b) and the pre-norm Lipschitz scope stay `open` until someone works out the constants.

## Empirical hooks (not part of the proofs)

- **pil:** for the T6 experiment, compare linear projection with clean-up projection on margins and
  `retrievable_fraction`. Test T2's multiplicativity only in the diagonal-inclusive convention (see T2).
- **rosetta:** a certified TPR substitution at the last layer (T5) is a decision-side statement. It still does not
  produce a weights-free `circuits.dl`; the downstream decode stays the model's.
- **Pre-registration of any proposer use:** `rosetta/DISCOVER_BRIDGE.md`.
