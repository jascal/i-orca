<!--
  i-orca surface for PIC OVER A KREIN SPACE -- a thought experiment in i-orca's "fieldrun / PIC"
  track (the sibling of ../tropical's DecodeCapacity/RoutingRank and ../superposition's Welch).

  Companion to pic/spec/PIC_SPEC.md.  PIC's incidence j |> v = <d_j, U_v> lives in a Euclidean
  residual space.  This corpus asks: what survives, what breaks, and what is new if the inner product
  is INDEFINITE -- a Krein form [x,y] = <J x, y> with fundamental symmetry J (signature (p,q))?

  The answer is a clean split that mirrors PIC's own frame/decode cut:
    * DECODE SIDE is METRIC-FREE.  Because J is invertible, a Krein incidence is a Euclidean incidence
      of the J-transformed source ([d,U_v] = <J d, U_v>), so monomials/argmax/semiring/margins transfer
      verbatim under d_j |-> J d_j.  (KreinDecode.thy)
    * FRAME SIDE feels the signature.  Decode capacity COLLAPSES in the indefinite ball (timelike
      escape) and the Welch interference floor DEGRADES (signature cancellation).  (KreinWelch.thy)

  As in ../tropical and ../superposition the load-bearing math lives in the kernel-checked Isabelle
  theories; each theorem below is STATED in i-orca form and discharged by `(rule <lemma>)` against its
  lemma, resolved through `## imports`.  Following the house style we do NOT list the cited lemma in
  `## context` (the compiler lowers context rows to local `assumes`, which would turn the cite into a
  vacuous P => P).

  Verification:
    - `i-orca verify examples/pic_krein/pic_krein.i.orca.md`  (structural, zero Isabelle).
    - Kernel check: built INSIDE the `KreinPIC` session (this directory's ROOT):
          isabelle build -D examples/pic_krein -o quick_and_dirty KreinPIC

  Map to the spec (pic/spec/PIC_SPEC.md):
    DECODE INVARIANCE (sec 3.1)        -> KreinLogitDefinitize, KreinFormSymmetric, KreinMajorant
    CAPACITY (sec 5.1, survives)       -> KreinMarginPairSeparation
    CAPACITY (sec 5.1, collapses)      -> KreinIndefiniteBallUnbounded
    WELCH (sec 5.3, degrades)          -> KreinSelfCoherenceSigned, KreinTraceIsSignature,
                                          KreinWelchDriverVanishes
    NEW: null token (sec 5.7 sibling)  -> KreinNullToken
    BOTTOM-K (min-plus dual of §5.4)   -> KreinBottomKAsNegMax, KreinCodecodePartition,
                                          KreinCoheadCertifies, KreinCoheadArgminInCohead,
                                          KreinCotailIsResidue
    BOTTOM-K = TOP-K of negated frame  -> KreinIncidenceNegFrame, KreinBottomKIsTopKNegFrame
    SCHEME A (Krein in frame-update)   -> KreinGramFormNonneg, KreinIndefiniteNotGramForm,
                                          KreinPrecondNotReparam, KreinPsdPrecondDescends,
                                          KreinIndefinitePrecondNotDescent
-->

# theorem KreinLogitDefinitize
> DEFINITIZATION -- the one-liner the whole decode-side transfer rests on. A Krein incidence is the Euclidean incidence of the J-transformed source, so the full PIC monomial/logit under the indefinite form `[d_j, U_v]` equals the Euclidean logit with sources `d'_j = J d_j`. Hence monomials, argmax, the semiring family and every margin theorem are metric-free. Cites `krein_logit_definitize`.

## imports
| Theory      |
|-------------|
| KreinDecode |

## goal
| Statement |
|-----------|
| (∑j∈Jset. kinner J (d j) (U v)) + bb v = (∑j∈Jset. inner (J (d j)) (U v)) + bb v |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (∑j∈Jset. kinner J (d j) (U v)) + bb v = (∑j∈Jset. inner (J (d j)) (U v)) + bb v | the Krein incidence unfolds to the majorant of the J-transformed source, termwise | — | (rule krein_logit_definitize) | method |


# theorem KreinFormSymmetric
> The indefinite form `[x,y] = <J x, y>` is symmetric when J is self-adjoint for the majorant — the minimal hygiene that makes it a legitimate (if indefinite) Gram kernel. Cites `kinner_sym`.

## imports
| Theory      |
|-------------|
| KreinDecode |

## goal
| Statement |
|-----------|
| (⋀x y. inner (J x) y = inner x (J y)) ⟹ kinner J x y = kinner J y x |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀x y. inner (J x) y = inner x (J y)) ⟹ kinner J x y = kinner J y x | self-adjointness plus commutativity of the majorant inner product | — | (rule kinner_sym) | method |


# theorem KreinMajorant
> THE ESCAPE HATCH. Applying the fundamental symmetry J on BOTH sides recovers the positive-definite majorant: `[J x, y] = <x, y>` (J an involution). This is "retreat to the majorant" — and the precise reason a FIXED, freely-absorbable J adds nothing (with J = id this is ordinary PIC). The content is in fixing the signature / freezing the frame. Cites `kinner_majorant`.

## imports
| Theory      |
|-------------|
| KreinDecode |

## goal
| Statement |
|-----------|
| (⋀x. J (J x) = x) ⟹ kinner J (J x) y = inner x y |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀x. J (J x) = x) ⟹ kinner J (J x) y = inner x y | J ∘ J = id collapses the doubled symmetry to the identity | — | (rule kinner_majorant) | method |


# theorem KreinMarginPairSeparation
> CAPACITY SURVIVES IN THE MAJORANT. Two Krein-γ-decodable tokens (witnesses in the majorant unit ball) have γ-separated frames, `γ ≤ ‖U v − U w‖`. The proof runs the Euclidean separation argument on the J-transformed witnesses `J rv, J rw`, which the majorant isometry keeps in the unit ball — so DecodeCapacity transfers verbatim PROVIDED the residual ball is the majorant ball. Cites `margin_pair_separation_k`.

## imports
| Theory      |
|-------------|
| KreinDecode |

## goal
| Statement |
|-----------|
| gdecodes_k J U b γ v rv ⟹ gdecodes_k J U b γ w rw ⟹ norm rv ≤ 1 ⟹ norm rw ≤ 1 ⟹ v ≠ w ⟹ (⋀x. norm (J x) = norm x) ⟹ γ ≤ norm (U v - U w) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gdecodes_k J U b γ v rv ⟹ gdecodes_k J U b γ w rw ⟹ norm rv ≤ 1 ⟹ norm rw ≤ 1 ⟹ v ≠ w ⟹ (⋀x. norm (J x) = norm x) ⟹ γ ≤ norm (U v - U w) | apply the bias-cancelling Cauchy–Schwarz argument to the J-transformed witnesses, isometric in the majorant | — | (rule margin_pair_separation_k) | method |


# theorem KreinSelfCoherenceSigned
> UNIT NORM SPLITS. A feature on a single coordinate `b0` has self-coherence exactly `s b0`: with `s b0 = +1` it is a spacelike unit, with `s b0 = −1` a TIMELIKE unit (self-coherence −1). In a Krein frame "unit norm" is two classes, not one — the structural root of every frame-side change below. Cites `single_coord_self`.

## imports
| Theory     |
|------------|
| KreinWelch |

## goal
| Statement |
|-----------|
| finite K ⟹ b0 ∈ K ⟹ kip s K (λb. if b = b0 then 1 else 0) (λb. if b = b0 then 1 else 0) = s b0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite K ⟹ b0 ∈ K ⟹ kip s K (λb. if b = b0 then 1 else 0) (λb. if b = b0 then 1 else 0) = s b0 | the single-coordinate Kronecker sum collapses to the signature at b0 | — | (rule single_coord_self) | method |


# theorem KreinNullToken
> A KREIN-NATIVE INTRINSICALLY-COMPOSED TOKEN. In a signature-(1,1) pair there is a NON-ZERO null token with `[x,x] = 0` — it sits on the light cone. Steered by its own direction it gains zero self-incidence, so it can never be retrieved single-source: a frame-geometric sibling of the coalition-combinatorial "composed" token of `Separation.thy`. Cites `null_vector`.

## imports
| Theory     |
|------------|
| KreinWelch |

## goal
| Statement |
|-----------|
| finite K ⟹ bp ∈ K ⟹ bm ∈ K ⟹ bp ≠ bm ⟹ s bp = 1 ⟹ s bm = - 1 ⟹ kip s K (λb. if b = bp ∨ b = bm then 1 else 0) (λb. if b = bp ∨ b = bm then 1 else 0) = 0 ∧ (λb. if b = bp ∨ b = bm then (1::real) else 0) ≠ (λb. 0) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite K ⟹ bp ∈ K ⟹ bm ∈ K ⟹ bp ≠ bm ⟹ s bp = 1 ⟹ s bm = - 1 ⟹ kip s K (λb. if b = bp ∨ b = bm then 1 else 0) (λb. if b = bp ∨ b = bm then 1 else 0) = 0 ∧ (λb. if b = bp ∨ b = bm then (1::real) else 0) ≠ (λb. 0) | the spacelike and timelike unit contributions +1 and −1 cancel; the vector is non-zero at bp | — | (rule null_vector) | method |


# theorem KreinTraceIsSignature
> The Gram TRACE is the signature imbalance, not the count. For unit features (`[v_i,v_i] = ε_i ∈ {±1}`) the trace `∑_i [v_i,v_i] = ∑_i ε_i = p − q` — the quantity that drives the Welch floor. In the Euclidean case this is always `n`; here it can be anything in `[−n, n]`. Cites `kip_trace_eq_signature`.

## imports
| Theory     |
|------------|
| KreinWelch |

## goal
| Statement |
|-----------|
| (⋀i. i ∈ I ⟹ kip s K (v i) (v i) = eps i) ⟹ (∑i∈I. kip s K (v i) (v i)) = (∑i∈I. eps i) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀i. i ∈ I ⟹ kip s K (v i) (v i) = eps i) ⟹ (∑i∈I. kip s K (v i) (v i)) = (∑i∈I. eps i) | the diagonal is the per-feature signature; sum termwise | — | (rule kip_trace_eq_signature) | method |


# theorem KreinWelchDriverVanishes
> WELCH DEGRADATION. The welch_sos lower bound on total squared coherence is `(trace)² / |K|`. For a BALANCED signature (`∑_i ε_i = 0`) it is exactly 0: the floor that, in the positive-definite case, forces interference `n(n−d)/d > 0` when `n > d` is VACUOUS. The Welch obstruction is a positive-definiteness phenomenon — indefiniteness lets the Gram eigenvalues cancel. (Degradation of the GUARANTEE; achievability of small coherence with n > d is open.) Cites `krein_welch_driver_vanishes`.

## imports
| Theory     |
|------------|
| KreinWelch |

## goal
| Statement |
|-----------|
| (⋀i. i ∈ I ⟹ kip s K (v i) (v i) = eps i) ⟹ (∑i∈I. eps i) = 0 ⟹ (∑i∈I. kip s K (v i) (v i))^2 / real (card K) = 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀i. i ∈ I ⟹ kip s K (v i) (v i) = eps i) ⟹ (∑i∈I. eps i) = 0 ⟹ (∑i∈I. kip s K (v i) (v i))^2 / real (card K) = 0 | the trace is the signature, zero when balanced, so its square over the dimension is zero | — | (rule krein_welch_driver_vanishes) | method |


# theorem KreinIndefiniteBallUnbounded
> CAPACITY COLLAPSE (timelike escape). If any coordinate is timelike (`s b0 < 0`) the indefinite pseudo-ball `{x : [x,x] ≤ 1}` is UNBOUNDED in the majorant: for every radius R there is a point inside it with majorant norm² ≥ R. So the packing/covering number behind `DecodeCapacity.head_capacity` has no compact domain — the cell-capacity bound is a theorem about the MAJORANT, vacuous in the indefinite metric of record. Cites `indefinite_ball_unbounded`.

## imports
| Theory     |
|------------|
| KreinWelch |

## goal
| Statement |
|-----------|
| finite K ⟹ b0 ∈ K ⟹ s b0 < 0 ⟹ (∀R. ∃x. kip s K x x ≤ 1 ∧ ipK K x x ≥ R) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite K ⟹ b0 ∈ K ⟹ s b0 < 0 ⟹ (∀R. ∃x. kip s K x x ≤ 1 ∧ ipK K x x ≥ R) | a timelike ray has non-positive Krein norm but unbounded majorant norm | — | (rule indefinite_ball_unbounded) | method |


<!-- ============================================================================
     BOTTOM-K (min-plus) DECODE CERTIFICATE (KreinBottomK.thy) — the dual of tropical/HeadTail.thy.
     PIC's top-K decode is the max-plus aggregate Max_v L(v); its dual is the bottom-K decode Min_v L(v)
     — the most-suppressed token, the negative-temperature (T -> 0^-) limit of the PIC semiring family.
     Bottom-K = top-K of the negated frame (frame negation is the canonical top<->bottom involution, any J).
     ============================================================================ -->

# theorem KreinBottomKAsNegMax
> Bottom-K is top-K of the negated logits: the min-plus sum `comin = min` is the max-plus sum conjugated by negation, `min a b = − max (−a) (−b)`. The algebraic reason no new frame is needed — read the same monomials with the dual aggregator. Cites `comin_as_neg_max`.

## imports
| Theory       |
|--------------|
| KreinBottomK |

## goal
| Statement |
|-----------|
| comin a b = - max (- a) (- b) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | comin a b = - max (- a) (- b) | min and max are negation-conjugate | — | (rule comin_as_neg_max) | method |


# theorem KreinCodecodePartition
> The bottom-K decode splits over the head/tail partition, with the min-plus sum `comin = min`: `codecode L (H ∪ T) = comin (codecode L H) (codecode L T)`. The dual of `HeadTail.decode_partition`. Cites `codecode_partition`.

## imports
| Theory       |
|--------------|
| KreinBottomK |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L (H ∪ T) = comin (codecode L H) (codecode L T) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L (H ∪ T) = comin (codecode L H) (codecode L T) | Min over a union of finite nonempty sets is the min of the two Mins | — | (rule codecode_partition) | method |


# theorem KreinCoheadCertifies
> CO-HEAD CERTIFICATE (bottom-K). When the co-head's minimum is at or below the tail's (`codecode L H ≤ codecode L T`), the full bottom-K decode equals the co-head's — the co-head contains the most-suppressed token. Dual of `HeadTail.head_certifies_decode`. Cites `cohead_certifies_codecode`.

## imports
| Theory       |
|--------------|
| KreinBottomK |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L H ≤ codecode L T ⟹ codecode L (H ∪ T) = codecode L H |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L H ≤ codecode L T ⟹ codecode L (H ∪ T) = codecode L H | the min over the union collapses to the co-head when the co-head dominates from below | — | (rule cohead_certifies_codecode) | method |


# theorem KreinCoheadArgminInCohead
> Under the same domination, the bottom-K argMIN lies IN the co-head: a co-head token attains the full bottom-K decode and is `≤` every candidate. So the most-suppressed token is certifiably a co-head token. Dual of `HeadTail.head_argmax_in_head`. Cites `cohead_argmin_in_cohead`.

## imports
| Theory       |
|--------------|
| KreinBottomK |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L H ≤ codecode L T ⟹ (∃h∈H. L h = codecode L (H ∪ T) ∧ (∀v∈H ∪ T. L h ≤ L v)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L H ≤ codecode L T ⟹ (∃h∈H. L h = codecode L (H ∪ T) ∧ (∀v∈H ∪ T. L h ≤ L v)) | a co-head token attaining the co-head Min attains the full Min and is below every candidate | — | (rule cohead_argmin_in_cohead) | method |


# theorem KreinCotailIsResidue
> BOTTOM-K RESIDUE. When the co-head does NOT dominate from below (`codecode L T < codecode L H`), the most-suppressed token lies in the tail — the explicit bottom-K residue. Dual of `HeadTail.tail_is_residue`. Cites `cotail_is_residue`.

## imports
| Theory       |
|--------------|
| KreinBottomK |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L T < codecode L H ⟹ (∃t∈T. L t = codecode L (H ∪ T) ∧ (∀h∈H. L t < L h)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ codecode L T < codecode L H ⟹ (∃t∈T. L t = codecode L (H ∪ T) ∧ (∀h∈H. L t < L h)) | a tail token attaining the tail Min attains the full Min and is strictly below every co-head token | — | (rule cotail_is_residue) | method |


# theorem KreinIncidenceNegFrame
> Negating the frame negates the incidence: `[r, −U_v] = − [r, U_v]`. The metric-light fact (inner-product linearity only, no assumption on J) behind the top↔bottom involution. Cites `kinner_neg_frame`.

## imports
| Theory       |
|--------------|
| KreinBottomK |

## goal
| Statement |
|-----------|
| kinner J r (- (U v)) = - kinner J r (U v) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | kinner J r (- (U v)) = - kinner J r (U v) | the incidence is linear in the frame argument | — | (rule kinner_neg_frame) | method |


# theorem KreinBottomKIsTopKNegFrame
> BOTTOM-K = TOP-K OF THE NEGATED FRAME. The bottom-K (min-plus) decode read off the frame `U` is minus the top-K (max-plus) decode read off the negated frame `−U` — the canonical top↔bottom involution, holding for every fundamental symmetry `J`. Cites `bottomk_eq_topk_neg_frame`.

## imports
| Theory       |
|--------------|
| KreinBottomK |

## goal
| Statement |
|-----------|
| finite S ⟹ S ≠ {} ⟹ codecode (λv. kinner J r (U v)) S = - decode (λv. kinner J r (- (U v))) S |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ S ≠ {} ⟹ codecode (λv. kinner J r (U v)) S = - decode (λv. kinner J r (- (U v))) S | bottom-K is minus the top-K of the negated frame | — | (rule bottomk_eq_topk_neg_frame) | method |


<!-- ============================================================================
     SCHEME A — KREIN IN THE TUNABLE FRAME ONLY (KreinPrecond.thy).
     Forward pass + loss + training data stay Euclidean; the indefinite J enters only as a preconditioner
     on the frame gradient (U <- U - eta * J grad), so the timelike subspace gets sign-flipped (ascending)
     updates — "backprop allowed to send values negative". Non-trivial because a reparametrization-induced
     preconditioner is always M^T M (PSD), which an indefinite J can never equal. The optimizer-side
     companion of the forward-side absorb-J triviality (KreinMajorant).
     ============================================================================ -->

# theorem KreinGramFormNonneg
> Every Gram quadratic form `x ↦ ⟨M x, M x⟩` is `≥ 0` — these are exactly the preconditioners a linear reparametrization can realize (the PSD ones, `MᵀM`). Cites `gram_form_nonneg`.

## imports
| Theory       |
|--------------|
| KreinPrecond |

## goal
| Statement |
|-----------|
| inner (M x) (M x) ≥ 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | inner (M x) (M x) ≥ 0 | a Gram form is a squared norm, hence nonnegative | — | (rule gram_form_nonneg) | method |


# theorem KreinIndefiniteNotGramForm
> An indefinite fundamental symmetry `J` — one with a timelike vector `t` (`⟨t, J t⟩ < 0`) — has a quadratic form that is NOT a Gram form: no map `M` satisfies `⟨x, J x⟩ = ⟨M x, M x⟩` for all `x`. The timelike vector witnesses a negative value no nonnegative Gram form can match. Cites `indefinite_not_gram_form`.

## imports
| Theory       |
|--------------|
| KreinPrecond |

## goal
| Statement |
|-----------|
| inner t (J t) < 0 ⟹ ¬ (∃M. ∀x. inner x (J x) = inner (M x) (M x)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | inner t (J t) < 0 ⟹ ¬ (∃M. ∀x. inner x (J x) = inner (M x) (M x)) | a timelike vector gives a negative value that no squared-norm Gram form can equal | — | (rule indefinite_not_gram_form) | method |


# theorem KreinPrecondNotReparam
> SCHEME A IS GENUINELY NEW DYNAMICS. An indefinite preconditioner is induced by no real linear reparametrization of the parameters: since a reparametrization `V = M U` yields the PSD preconditioner `MᵀM`, and an indefinite `J` equals no `MᵀM`, the indefinite-preconditioned frame update is not the parameter-image of vanilla SGD. The optimizer-side companion to the forward-side absorb-J triviality (`KreinMajorant`). Cites `precond_not_reparam`.

## imports
| Theory       |
|--------------|
| KreinPrecond |

## goal
| Statement |
|-----------|
| inner t (J t) < 0 ⟹ ∄M. ∀x. inner x (J x) = inner (M x) (M x) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | inner t (J t) < 0 ⟹ ∄M. ∀x. inner x (J x) = inner (M x) (M x) | an indefinite preconditioner is not the PSD MᵀM any reparametrization would induce | — | (rule precond_not_reparam) | method |


# theorem KreinPsdPrecondDescends
> A PSD preconditioner always descends. Treating the gradient as a free vector `g`, the first-order loss change along the preconditioned step `−(J g)` is `⟨g, −(J g)⟩ = −⟨g, J g⟩ ≤ 0` whenever `J` is PSD. So Euclidean (or any PSD) preconditioning never increases the loss. Cites `psd_precond_descends`.

## imports
| Theory       |
|--------------|
| KreinPrecond |

## goal
| Statement |
|-----------|
| (⋀x. 0 ≤ inner x (J x)) ⟹ inner g (- (J g)) ≤ 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀x. 0 ≤ inner x (J x)) ⟹ inner g (- (J g)) ≤ 0 | the directional derivative along −(J g) is −⟨g, J g⟩, nonpositive for PSD J | — | (rule psd_precond_descends) | method |


# theorem KreinIndefinitePrecondNotDescent
> THE J-FLOW IS NOT A DESCENT FLOW. If `J` has a timelike vector `t` (`⟨t, J t⟩ < 0`), then at gradient `g = t` the preconditioned step `−(J t)` is a strict ASCENT direction: `⟨t, −(J t)⟩ = −⟨t, J t⟩ > 0`. So the indefinite-preconditioned flow `U̇ = −J∇L` can increase the loss — the dynamical companion to `precond_not_reparam` (it is genuinely new dynamics, and specifically *not* descent). Cites `indefinite_precond_not_descent`.

## imports
| Theory       |
|--------------|
| KreinPrecond |

## goal
| Statement |
|-----------|
| inner t (J t) < 0 ⟹ (∃g. 0 < inner g (- (J g))) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | inner t (J t) < 0 ⟹ (∃g. 0 < inner g (- (J g))) | the timelike vector itself is a gradient at which the preconditioned step ascends the loss | — | (rule indefinite_precond_not_descent) | method |
