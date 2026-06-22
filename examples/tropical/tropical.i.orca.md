<!--
  i-orca surface for the TROPICAL GEOMETRY OF DEEP NEURAL NETWORKS -- an entry in
  i-orca's "canonical proofs from other authors" track (the second after
  ../watermark/, Aaronson's LLM watermark).

  Primary source: Zhang, Naitzat & Lim, "Tropical Geometry of Deep Neural Networks",
  Proc. ICML 2018, PMLR 80:5824-5832 -- in particular Thm 5.4 (a ReLU network IS a
  tropical rational map), Def 2.4 (tropical rational function), and the Newton-polytope
  region machinery (Def 3.2 / Cor 3.4). Surrounding literature: Pachter & Sturmfels,
  "Tropical Geometry of Statistical Models", PNAS 101(46):16132-16137, 2004 (polytope
  propagation = geometric sum-product); Maragos, Charisopoulos & Theodosis, "Tropical
  Geometry and Machine Learning", Proc. IEEE 109(5):728-755, 2021 (max-plus /
  morphological networks, residuation).

  As in ../watermark/ and ../provenance/, the heavy content lives in the kernel-checked
  Isabelle theories here (TropicalSemiring, TropicalPoly, ReLUNet, MaxPlus, Newton);
  each theorem below is STATED in i-orca form and discharged by `(rule <lemma>)` against
  its lemma, resolved through `## imports`. We deliberately do NOT list the cited lemma
  in `## context` (the compiler lowers context rows to local `assumes`, which would turn
  the cite into a vacuous P => P).

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID, fraction 1.000.
    - Kernel check: built INSIDE the `Tropical` session (this directory's ROOT):
          ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/tropical \
            -o quick_and_dirty Tropical
      The standalone `i-orca check` builds each theorem under a plain HOL parent and
      cannot load this project-local session -- an import-resolution limit, not a math
      failure (same caveat as the watermark / provenance / complexity corpora).

  Map to the sources:
    SEMIRING (max-plus)     -> TropicalDistributivity, TropicalAdditionIdempotent,
                               TropicalMultiplicativeIdentity
    TROPICAL POLYNOMIALS    -> TropicalMonomialConvex, MaxOfConvexIsConvex,
                               TropicalPolynomialConvex, TropicalPolynomialScaleClosed
    ReLU NETS = TROP RAT'L  -> AffineIsTropicalRational, ReluOfAffineIsTropicalRational,
      (Zhang-Naitzat-Lim       TropicalRationalClosedUnderSum, TropicalRationalClosedUnderReLU,
       Theorem 5.4)            OneHiddenLayerIsTropicalRational, TropicalRationalIsContinuous
    MAX-PLUS RESIDUATION    -> MaxPlusResiduationFeasible, MaxPlusResiduationGreatest
      (Maragos et al.)
    POLYTOPE PROPAGATION     -> TropicalProductIsPointwiseSum, MonomialCountSubmultiplicative,
      (Pachter-Sturmfels;       NewtonSupportIsMinkowskiSum
       Cor 3.4)
    WORKED EXAMPLE           -> AbsValueNetworkComputesAbs, AbsValueNetworkIsTropicalRational
      (a concrete ReLU net)
-->

# theorem TropicalDistributivity
> The load-bearing semiring law: tropical multiplication (a ⊙ b = a + b) distributes over tropical addition (a ⊕ b = max a b). This single identity — `a + max b c = max (a+c) (b+c)` — is what lets a sum-of-maxes (a ReLU network) be rewritten as a max-of-sums (a tropical polynomial). Cites `tmul_tadd_distrib_left`.

## imports
| Theory           |
|------------------|
| TropicalSemiring |

## goal
| Statement |
|-----------|
| tmul a (tadd b c) = tadd (tmul a b) (tmul a c) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | tmul a (tadd b c) = tadd (tmul a b) (tmul a c) | adding a constant commutes with max | — | (rule tmul_tadd_distrib_left) | method |


# theorem TropicalAdditionIdempotent
> Tropical addition is idempotent: `a ⊕ a = a` (max a a = a). The additive monoid is a semilattice — there are no additive inverses, the structural reason a tropical semiring is not a ring. Cites `tadd_idem`.

## imports
| Theory           |
|------------------|
| TropicalSemiring |

## goal
| Statement |
|-----------|
| tadd a a = a |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | tadd a a = a | max of a value with itself is the value | — | (rule tadd_idem) | method |


# theorem TropicalMultiplicativeIdentity
> The tropical multiplicative identity is 0: `0 ⊙ a = a` (0 + a = a). (The additive identity is −∞, adjoined separately.) Cites `tmul_left_id`.

## imports
| Theory           |
|------------------|
| TropicalSemiring |

## goal
| Statement |
|-----------|
| tmul 0 a = a |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | tmul 0 a = a | 0 is the identity of addition | — | (rule tmul_left_id) | method |


# theorem TropicalMonomialConvex
> A tropical monomial is an affine function `⟨a,x⟩ + c`, which is convex (indeed affine). The geometric atom of the theory. Cites `convex_on_affine`.

## imports
| Theory       |
|--------------|
| TropicalPoly |

## goal
| Statement |
|-----------|
| convex_on UNIV (λx. inner a x + c) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | convex_on UNIV (λx. inner a x + c) | an affine function satisfies the convexity inequality with equality | — | (rule convex_on_affine) | method |


# theorem MaxOfConvexIsConvex
> Tropical addition preserves convexity: the pointwise max of two convex functions is convex. (No such lemma is in the Isabelle library; the substrate proves it directly.) This is why tropical polynomials — iterated maxes of affine pieces — are convex. Cites `convex_on_max`.

## imports
| Theory       |
|--------------|
| TropicalPoly |

## goal
| Statement |
|-----------|
| convex_on A f ⟹ convex_on A g ⟹ convex_on A (λx. max (f x) (g x)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | convex_on A f ⟹ convex_on A g ⟹ convex_on A (λx. max (f x) (g x)) | each piece is bounded by the max at both endpoints, so the convex combination is too | — | (rule convex_on_max) | method |


# theorem TropicalPolynomialConvex
> The geometric heart: every tropical polynomial is a convex function. By induction over the generators — affine monomials are convex, and convexity is preserved by tropical product (+) and tropical sum (max). Tropical polynomials are exactly the convex piecewise-linear functions. Cites `troppoly_convex`.

## imports
| Theory       |
|--------------|
| TropicalPoly |

## goal
| Statement |
|-----------|
| troppoly f ⟹ convex_on UNIV f |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troppoly f ⟹ convex_on UNIV f | induct over the tropical-polynomial generators; each preserves convexity | — | (rule troppoly_convex) | method |


# theorem TropicalPolynomialScaleClosed
> Tropical polynomials are closed under non-negative scaling: a non-negative multiple of a tropical polynomial is a tropical polynomial (it stays a max of affine pieces). Cites `troppoly_scale_nonneg`.

## imports
| Theory       |
|--------------|
| TropicalPoly |

## goal
| Statement |
|-----------|
| troppoly f ⟹ 0 ≤ c ⟹ troppoly (λx. c * f x) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troppoly f ⟹ 0 ≤ c ⟹ troppoly (λx. c * f x) | scaling distributes through +, and through max when the factor is non-negative | — | (rule troppoly_scale_nonneg) | method |


# theorem AffineIsTropicalRational
> An affine map (a linear layer) is a tropical rational function — a tropical monomial, hence a degenerate tropical quotient. Cites `troprat_affine`.

## imports
| Theory  |
|---------|
| ReLUNet |

## goal
| Statement |
|-----------|
| troprat (λx. inner a x + c) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troprat (λx. inner a x + c) | an affine function is a tropical polynomial minus zero | — | (rule troprat_affine) | method |


# theorem ReluOfAffineIsTropicalRational
> ReLU of an affine pre-activation — a single neuron — is a tropical rational function, because `relu y = max y 0` is itself a tropical polynomial. The basic computational unit of a network lives in the tropical-rational class. Cites `troprat_relu_affine`.

## imports
| Theory  |
|---------|
| ReLUNet |

## goal
| Statement |
|-----------|
| troprat (λx. relu (inner a x + c)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troprat (λx. relu (inner a x + c)) | relu is max with 0, a tropical polynomial; compose with the affine map | — | (rule troprat_relu_affine) | method |


# theorem TropicalRationalClosedUnderSum
> The tropical rational functions are closed under addition: `(g1−h1) + (g2−h2) = (g1+g2) − (h1+h2)`, a difference of tropical polynomials. A network can add neuron outputs and stay tropical rational. Cites `troprat_add`.

## imports
| Theory  |
|---------|
| ReLUNet |

## goal
| Statement |
|-----------|
| troprat f ⟹ troprat g ⟹ troprat (λx. f x + g x) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troprat f ⟹ troprat g ⟹ troprat (λx. f x + g x) | add the numerators and the denominators of the two tropical quotients | — | (rule troprat_add) | method |


# theorem TropicalRationalClosedUnderReLU
> The tropical rational functions are closed under ReLU post-composition: `relu (g − h) = max g h − h`, again a difference of tropical polynomials. Stacking a ReLU on a tropical-rational pre-activation keeps it tropical rational — the inductive step of Theorem 5.4. Cites `troprat_relu`.

## imports
| Theory  |
|---------|
| ReLUNet |

## goal
| Statement |
|-----------|
| troprat f ⟹ troprat (λx. relu (f x)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troprat f ⟹ troprat (λx. relu (f x)) | relu(g−h) = max g h − h, a difference of tropical polynomials | — | (rule troprat_relu) | method |


# theorem OneHiddenLayerIsTropicalRational
> Theorem 5.4, worked instance. A one-hidden-layer scalar ReLU network — `x ↦ ∑ₖ vₖ · relu(⟨aₖ,x⟩ + bₖ) + c` — is a tropical rational function. Built from the closure results: ReLU-of-affine neurons, real scaling, a finite sum, and a constant shift. Cites `troprat_one_hidden_layer`.

## imports
| Theory  |
|---------|
| ReLUNet |

## goal
| Statement |
|-----------|
| finite K ⟹ troprat (λx. (∑k∈K. v k * relu (inner (a k) x + b k)) + c) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite K ⟹ troprat (λx. (∑k∈K. v k * relu (inner (a k) x + b k)) + c) | each scaled neuron is tropical rational; sum over the finite hidden layer and add the bias | — | (rule troprat_one_hidden_layer) | method |


# theorem TropicalRationalIsContinuous
> Every tropical rational function is continuous — these are exactly the continuous piecewise-linear functions a ReLU network realises. Cites `troprat_continuous`.

## imports
| Theory  |
|---------|
| ReLUNet |

## goal
| Statement |
|-----------|
| troprat f ⟹ continuous_on UNIV (f::'a::real_inner ⇒ real) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troprat f ⟹ continuous_on UNIV (f::'a::real_inner ⇒ real) | each generator is continuous; differences of continuous functions are continuous | — | (rule troprat_continuous) | method |


# theorem MaxPlusResiduationFeasible
> Max-plus residuation (Maragos et al.; classical Cuninghame-Green). The max-plus inequality `A ⊙ x ≤ b` always has a greatest subsolution `x̂ⱼ = minᵢ (bᵢ − Aᵢⱼ)`. This is the feasibility half: `x̂` is a subsolution, `(A ⊙ x̂)ᵢ ≤ bᵢ`. Cites `mpres_feasible`.

## imports
| Theory  |
|---------|
| MaxPlus |

## goal
| Statement |
|-----------|
| finite I ⟹ finite J ⟹ J ≠ {} ⟹ i ∈ I ⟹ mpmul A J (mpres A I b) i ≤ b i |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ finite J ⟹ J ≠ {} ⟹ i ∈ I ⟹ mpmul A J (mpres A I b) i ≤ b i | each term Aᵢⱼ + x̂ⱼ is at most bᵢ, so their max is too | — | (rule mpres_feasible) | method |


# theorem MaxPlusResiduationGreatest
> The maximality half of the Galois connection: every subsolution `x` of `A ⊙ x ≤ b` is dominated by the residuated vector `x̂`. Together with feasibility this is the adjunction underlying morphological-network analysis and max-plus equation solving. Cites `mpres_greatest'`.

## imports
| Theory  |
|---------|
| MaxPlus |

## goal
| Statement |
|-----------|
| finite I ⟹ finite J ⟹ I ≠ {} ⟹ (∀i∈I. mpmul A J x i ≤ b i) ⟹ j ∈ J ⟹ x j ≤ mpres A I b j |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ finite J ⟹ I ≠ {} ⟹ (∀i∈I. mpmul A J x i ≤ b i) ⟹ j ∈ J ⟹ x j ≤ mpres A I b j | feasibility forces xⱼ ≤ bᵢ − Aᵢⱼ for every i, hence xⱼ ≤ the min | — | (rule mpres_greatest') | method |


# theorem TropicalProductIsPointwiseSum
> Pachter-Sturmfels polytope propagation. Representing a one-variable tropical polynomial as its finite set of monomials, the tropical PRODUCT of two polynomials is the pointwise SUM of the functions: `tpoly (P ⊗ Q) = tpoly P + tpoly Q`. This is the sum-product / Viterbi recursion run on Newton polytopes. Cites `tpoly_tprod`.

## imports
| Theory |
|--------|
| Newton |

## goal
| Statement |
|-----------|
| finite P ⟹ finite Q ⟹ P ≠ {} ⟹ Q ≠ {} ⟹ tpoly (tprod P Q) x = tpoly P x + tpoly Q x |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite P ⟹ finite Q ⟹ P ≠ {} ⟹ Q ≠ {} ⟹ tpoly (tprod P Q) x = tpoly P x + tpoly Q x | max over the product of monomial sums splits into the sum of the two maxima | — | (rule tpoly_tprod) | method |


# theorem MonomialCountSubmultiplicative
> The number of monomials (Newton-polytope lattice points, an upper proxy for linear regions) is submultiplicative under tropical product: `card (P ⊗ Q) ≤ card P · card Q`. The combinatorial mechanism behind the linear-region bounds (Cor 3.4). Cites `tprod_card_le`.

## imports
| Theory |
|--------|
| Newton |

## goal
| Statement |
|-----------|
| finite P ⟹ finite Q ⟹ card (tprod P Q) ≤ card P * card Q |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite P ⟹ finite Q ⟹ card (tprod P Q) ≤ card P * card Q | the product monomials are the image of P × Q, so their count is at most the cardinality of the product | — | (rule tprod_card_le) | method |


# theorem NewtonSupportIsMinkowskiSum
> The Newton polytope of a tropical product is the Minkowski sum of the factors' Newton polytopes: at the level of slope supports, `fst(P ⊗ Q)` is the sumset `fst P ⊕ fst Q`. The zonotope/vertex-count picture behind the region bounds. Cites `tprod_slope_sumset`.

## imports
| Theory |
|--------|
| Newton |

## goal
| Statement |
|-----------|
| fst ` tprod P Q = (λ(a, b). a + b) ` (fst ` P × fst ` Q) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | fst ` tprod P Q = (λ(a, b). a + b) ` (fst ` P × fst ` Q) | the slope of a product monomial is the sum of the factor slopes | — | (rule tprod_slope_sumset) | method |


# theorem AbsValueNetworkComputesAbs
> Worked example. The two-neuron ReLU network `x ↦ relu x + relu (−x)` computes the absolute value `|x|`. A concrete network whose function is, by the next theorem, exactly a tropical polynomial. Cites `relu_plus_relu_neg`.

## imports
| Theory   |
|----------|
| Examples |

## goal
| Statement |
|-----------|
| relu x + relu (- x) = abs x |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | relu x + relu (- x) = abs x | one neuron keeps the positive part, the other the negative part; their sum is the absolute value | — | (rule relu_plus_relu_neg) | method |


# theorem AbsValueNetworkIsTropicalRational
> Theorem 5.4, in miniature and fully concrete. The two-neuron network `x ↦ relu x + relu (−x)` is a tropical rational function — indeed the tropical polynomial `max x (−x) = x ⊕ (−x)`, a max of the two monomials `x` and `−x`. Cites `abs_network_troprat`.

## imports
| Theory   |
|----------|
| Examples |

## goal
| Statement |
|-----------|
| troprat (λx::real. relu x + relu (- x)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | troprat (λx::real. relu x + relu (- x)) | the network equals abs, which is the tropical polynomial max x (−x) | — | (rule abs_network_troprat) | method |


<!-- ============================================================================
     HEAD/TAIL DECODE CERTIFICATE (HeadTail.thy) — a fieldrun contribution, not from Zhang–Naitzat–Lim.
     An LLM decode argmax_v <x,U_v> is the tropical polynomial max_v (logit v). Splitting the vocabulary into a
     compact HEAD (the Zipf-frequent winning monomials) and an open-class TAIL, these theorems state EXACTLY what
     fieldrun measured (lo3a/tropical_rank.py + pr_core_residual_gate.py): the compact head certifiably reproduces the
     decode WHEN its tropical value dominates the tail (~65% of real-model decodes), and the tail is the explicit
     irreducible residue (~35%). It is the exact-decode sibling of the bounded-perturbation PO-T3 margin
     (../provable_opt/decode_margin_certified): there a δ-bounded change can't flip a >2δ margin; here the head can't
     be beaten when it out-values the whole tail.
     ============================================================================ -->

# theorem DecodePartition
> The decode value splits over the head/tail partition: the tropical sum (⊕ = max) over `H ∪ T` is the tropical sum of the head value and the tail value, `max (decode L H) (decode L T)`. The single max-plus fact behind localizing the forge tax to a named program region. Cites `decode_partition`.

## imports
| Theory   |
|----------|
| HeadTail |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L (H ∪ T) = tadd (decode L H) (decode L T) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L (H ∪ T) = tadd (decode L H) (decode L T) | Max over a union of finite nonempty sets is the max of the two Maxes | — | (rule decode_partition) | method |


# theorem HeadCertifiesDecode
> HEAD CERTIFICATE. When the head's tropical value dominates the tail's (`decode L T ≤ decode L H`), the FULL decode equals the head decode — the compact head reproduces the model's argmax exactly, with no read of the tail. Cites `head_certifies_decode`.

## imports
| Theory   |
|----------|
| HeadTail |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L T ≤ decode L H ⟹ decode L (H ∪ T) = decode L H |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L T ≤ decode L H ⟹ decode L (H ∪ T) = decode L H | the union-Max is max of the two; domination collapses it to the head Max | — | (rule head_certifies_decode) | method |


# theorem HeadArgmaxInHead
> Under the same domination, the decode's argmaximiser lies IN the head: some head token attains the full decode value and is ≥ every candidate in `H ∪ T`. So the certified decode is a head token — the tail is provably never read. Cites `head_argmax_in_head`.

## imports
| Theory   |
|----------|
| HeadTail |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L T ≤ decode L H ⟹ (∃h∈H. L h = decode L (H ∪ T) ∧ (∀v∈H ∪ T. L v ≤ L h)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L T ≤ decode L H ⟹ (∃h∈H. L h = decode L (H ∪ T) ∧ (∀v∈H ∪ T. L v ≤ L h)) | a head token attaining the head Max attains the full Max and dominates every candidate | — | (rule head_argmax_in_head) | method |


# theorem TailIsResidue
> TAIL RESIDUE. When the head does NOT dominate (`decode L H < decode L T`), the decode lies in the open-class tail: a tail token attains the full decode and strictly beats every head token. This is the explicit, uncertified ~35% — the irreducible open-class residue the compact head cannot reach. Cites `tail_is_residue`.

## imports
| Theory   |
|----------|
| HeadTail |

## goal
| Statement |
|-----------|
| finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L H < decode L T ⟹ (∃t∈T. L t = decode L (H ∪ T) ∧ (∀h∈H. L h < L t)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite H ⟹ finite T ⟹ H ≠ {} ⟹ T ≠ {} ⟹ decode L H < decode L T ⟹ (∃t∈T. L t = decode L (H ∪ T) ∧ (∀h∈H. L h < L t)) | a tail token attaining the tail Max attains the full Max and strictly beats every head token | — | (rule tail_is_residue) | method |


<!-- ============================================================================
     DECODE CAPACITY (DecodeCapacity.thy) — the decision-side Welch sibling; a fieldrun contribution.
     Confident decoding forces separated frames: if tokens v and w are each gamma-margin-decodable somewhere
     in the unit ball, then ||U_v - U_w|| >= gamma (bias-free — it cancels across the two witnesses). Hence the
     gamma-decodable set (and any certifiable HEAD, cf. HeadTail) is a gamma-code in R^d, of cardinality at most
     the packing number (1 + 2 rho / gamma)^d. This is the formal "structure is the hard limit": no frame tuning
     or rule allocation yields more than a bounded number of cleanly-separable decodes without raising the
     effective dimension (= tau* = min(exp H, d), the exponent of the packing bound). Sibling of the Welch bound.
     ============================================================================ -->

# theorem MarginPairSeparation
> CORE. If token `v` is `γ`-margin-decodable at `rv` and `w` at `rw` (both in the unit ball), their proposition directions are `γ`-separated: `γ ≤ ‖U v − U w‖`. The bias cancels (add the two witness inequalities; the cross term is `⟨rv − rw, U v − U w⟩`, bounded by Cauchy–Schwarz and `‖rv − rw‖ ≤ 2`). Cites `margin_pair_separation`.

## imports
| Theory         |
|----------------|
| DecodeCapacity |

## goal
| Statement |
|-----------|
| gdecodes U b γ v rv ⟹ gdecodes U b γ w rw ⟹ norm rv ≤ 1 ⟹ norm rw ≤ 1 ⟹ v ≠ w ⟹ γ ≤ norm (U v - U w) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gdecodes U b γ v rv ⟹ gdecodes U b γ w rw ⟹ norm rv ≤ 1 ⟹ norm rw ≤ 1 ⟹ v ≠ w ⟹ γ ≤ norm (U v - U w) | adding the two margin witnesses cancels the bias; Cauchy–Schwarz with ‖rv−rw‖≤2 gives the separation | — | (rule margin_pair_separation) | method |


# theorem DecodeCapacitySeparated
> The `γ`-decodable set is a `γ`-separated code: any two tokens that each win by margin `≥ γ` somewhere in the unit ball have frames at least `γ` apart, `γ ≤ dist(U v, U w)`. Cardinality is therefore bounded by the `γ`-packing number of the frame ball — the decision-side sibling of the Welch bound. Cites `decode_capacity_separated`.

## imports
| Theory         |
|----------------|
| DecodeCapacity |

## goal
| Statement |
|-----------|
| v ∈ gdecodable U b γ ⟹ w ∈ gdecodable U b γ ⟹ v ≠ w ⟹ γ ≤ dist (U v) (U w) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | v ∈ gdecodable U b γ ⟹ w ∈ gdecodable U b γ ⟹ v ≠ w ⟹ γ ≤ dist (U v) (U w) | each token supplies a unit-ball witness; apply the core separation pairwise | — | (rule decode_capacity_separated) | method |


# theorem HeadCapacity
> The certifiable HEAD is capacity-bounded. Any set `S` of `γ`-decodable tokens (in particular a HeadTail head that dominates its tail) is a `γ`-code: `∀ v,w ∈ S. v ≠ w ⟹ γ ≤ dist(U v, U w)`. So `|S|` ≤ the `γ`-packing number `(1 + 2ρ/γ)^d` — bounding the head bridges DecodeCapacity to HeadTail. Cites `head_capacity`.

## imports
| Theory         |
|----------------|
| DecodeCapacity |

## goal
| Statement |
|-----------|
| S ⊆ gdecodable U b γ ⟹ (∀v∈S. ∀w∈S. v ≠ w ⟶ γ ≤ dist (U v) (U w)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | S ⊆ gdecodable U b γ ⟹ (∀v∈S. ∀w∈S. v ≠ w ⟶ γ ≤ dist (U v) (U w)) | every pair in the head is γ-decodable, so the pairwise separation applies | — | (rule head_capacity) | method |
