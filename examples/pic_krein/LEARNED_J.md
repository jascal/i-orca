# Adaptive / learned fundamental symmetry `J`

Making the Krein fundamental symmetry `J` itself optimizable, rather than fixed. Kernel anchors:
`KreinWelch.Js_involution` (the parametrization is valid) and `KreinPrecond.descends_all_iff_psd` (the
constraint that governs everything below). Companion: [`SCHEME_A.md`](SCHEME_A.md).

## What "learning `J`" is, geometrically

A fundamental symmetry is `J = Jᵀ`, `J² = I`, signature `(p,q)`. At fixed `q` it is determined by its
negative subspace `H₋` (dim `q`) via `J = I − 2P`, `P` = orthogonal projector onto `H₋`. So:

- **Continuous part:** learning `J` at fixed `q` = optimizing `H₋ ∈ Gr(q,d)` (a Grassmannian).
- **Discrete part:** choosing `q` (the timelike dimension = the "suppression budget") = model selection.

## Parametrizations

1. **Coordinate signature `s`** (kernel: `Js_involution`). `J = diag(s)`, learn `s`. A **rigid** signature
   `s_b ∈ {±1}` (`s_b·s_b = 1`) gives a genuine involution `Js(Js x) = x` — kernel-proved. The practical
   form is a **soft signature** `s_b ∈ [−1,1]` (e.g. `s_b = tanh θ_b`): smooth, unconstrained, with the
   exact involution recovered only at `|s_b| = 1`; for `|s_b| < 1` the direction is "partially timelike"
   (`Js(Js x)_b = s_b² x_b`, a contraction). The `J_γ = P₊ + γP₋` annealing schedule of `SCHEME_A.md` is
   the special case of a single global `γ`.
2. **Projector / Grassmannian.** `P = W(WᵀW)⁻¹Wᵀ` for `W ∈ ℝ^{d×q}`, `J = I − 2P`; learn `W`
   (gauge-invariant), with Riemannian / Cayley updates on `Gr(q,d)`. The basis-free chart.

## The dichotomy that governs it (kernel: `descends_all_iff_psd`)

> A learned preconditioner descends for **all** gradients **iff** it is PSD.

Contrapositive (with `precond_not_reparam`): a genuinely indefinite learned `J` is **neither**
always-descent **nor** a reparametrization. Spelled out via curvature:

- The curvature-adaptive `J` that *helps minimization* is the **saddle-free-Newton** preconditioner
  `|H|⁻¹` (absolute Hessian) — which is **PSD**, i.e. ordinary second-order whitening, **not Krein**.
- The **sign-of-curvature** `J = sign(H)` is the saddle-**seeking** opposite — it ascends
  negative-curvature directions (genuinely Krein, but not a minimizer; the previous-turn result).

So **"adaptive indefinite `J` for faster minimization" is a contradiction**: any adaptivity that
preserves descent removes the indefiniteness. Learn `J` only where indefiniteness is the *goal* (min–max
spread, basin escape), not a means to minimize the loss.

## Two well-posed regimes for learning `J`

**A — Scheme B: `J` in the forward pass, learned by ordinary descent.** `J` enters the read-out (or QK);
standard cross-entropy trains it — no bilevel, no saddle issue. *But* it is absorbable (trivial) if the
frame is free, so it must be **tied** (shared across heads, or QK↔decode tied, or frame frozen) to be
non-trivial. With tying, `J` is a genuine model parameter and the soft signature `s = tanh θ` is the
smooth handle. Cleanest learned-`J`; cost: the forward pass is no longer Euclidean (you give up Scheme
A's "no forward change", but `KreinDecode`'s definitization keeps the decode-side guarantees).

**B — Scheme A: `J` in the preconditioner, learn `H₋`.** The learnable object is *which subspace to push
apart* (the max-player's subspace in the `SCHEME_A.md` min–max). Optimize `H₋ ∈ Gr(q,d)`. Learning `J`
to minimize the *final* loss is **bilevel/meta** (differentiate through the inner loop) — and the
dichotomy says it can't make the indefinite flow descend anyway, so the meta-objective must target the
min–max equilibrium, not raw loss.

## Choosing `q` (the signature / suppression budget)

- **Analytic:** the inertia of a signed data statistic (count of negative eigenvalues past a threshold) —
  the conversion recipe from the lossless-conversion analysis.
- **Emergent:** from a trained soft signature, `q = #{b : s_b < 0}`.
- **Swept:** as a hyperparameter.

## Verification-intact

- *Scheme A, learned `H₋`*: forward stays Euclidean → the full decode-side corpus applies to the current
  frame at every step (S1 holds, S2 monitored, S3 holds), exactly as fixed-`J` Scheme A.
- *Scheme B, learned `J`*: forward sees `J`, but by `KreinDecode` definitization the decode is metric-free
  so margins / head-tail / capacity-in-the-majorant (`margin_pair_separation_k`) still apply to the
  `J`-frame.

## Honest status

- **[proved]** parametrization validity (`Js_involution`) and the dichotomy (`descends_all_iff_psd`).
- **[open/empirical]** whether a learned `J` helps at all (§6.1: no frame knob yet beats plain SGD;
  learned preconditioners/metrics are a known-hard meta-learning regime).
- **[unimplemented]** the Grassmannian / bilevel machinery — standard but not built here.
