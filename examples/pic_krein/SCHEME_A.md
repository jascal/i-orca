# Scheme A — indefinite frame preconditioning: dynamics and a verification-intact training recipe

Scheme A injects the Krein fundamental symmetry `J` into the **frame update only** — the forward pass,
loss, and training data stay Euclidean. Kernel results: `KreinPrecond.thy`
(`gram_form_nonneg`, `indefinite_not_gram_form`, `precond_not_reparam`, `psd_precond_descends`,
`indefinite_precond_not_descent`). This note records the corrected dynamics and the only sound ways to
use the knob.

## The dynamics, stated honestly

The preconditioned flow `U̇ = −J ∇_U L` is **natural-gradient descent in an indefinite parameter
metric** — and an indefinite metric is not Riemannian, so the descent guarantee fails:

- **Not a descent flow.** `dL/dt = −⟨∇L, J ∇L⟩` is a sign-indefinite quadratic form. For a timelike
  gradient (`⟨g, J g⟩ < 0`) it is **positive** — the loss increases. (`indefinite_precond_not_descent`;
  contrast `psd_precond_descends` for the PSD/Euclidean case.)
- **Minima are repelled.** *Isotropic core (kernel-checked):* at a whitened minimum (`H = I`) the actual
  Scheme-A update multiplies a timelike axis by `1 + η` (`kstep_grows_on_timelike`, `kstep_norm_grows`)
  — geometric divergence away from the minimum — and the flow Jacobian `−J` has eigenvalue `+1` on the
  whole timelike eigenspace (`flow_unstable_on_timelike`), so `H₋` (dim `q`) is the unstable manifold.
  *General SPD `H` (stated, reduces to the core):* the linearization `−J H` is similar (via `H^{1/2}`) to
  the symmetric `−H^{1/2} J H^{1/2}`, which by Sylvester's law of inertia has the inertia of `−J` — `q`
  **positive** eigenvalues, a `q`-dim unstable manifold. (The general eigenvalue count needs the spectral
  theorem + Sylvester, beyond this HOL-Analysis session; the isotropic instance is the kernel-checked
  part.) Either way the flow is **saddle-seeking**, not minimizing: same critical points as SGD, but it
  destabilizes true minima and stabilizes critical points whose Morse index matches the signature.
- **Consequence.** Run on the *full* loss, `U̇ = −J∇L` will not minimize it and will degrade the decode
  (NLL rises, frame norm can explode along timelike directions). This is why §6.1's "no frame knob beats
  plain SGD" is a *symptom*, not just "haven't found the right `J`": a pure indefinite flow cannot be a
  loss-minimizer. **It must be used as a min–max, or transiently.**

This does **not** invalidate the non-triviality result — Scheme A *is* genuinely new dynamics
(`precond_not_reparam`). It just means the timelike subspace has to point at something you actually want
to maximize.

## Recipe 1 — signature-realized min–max (the principled use)

Split the objective into a part to **minimize** (data fit) and a part to **maximize** (push features
apart), and route them through the two subspaces:

```
L_fit   = NLL(L; t)  +  λ_m · ReLU(γ* − m_worst)        # descend (data terms)
L_push  = a chosen "spread" objective on the frame       # ASCEND (e.g. inter-feature separation)

# update (gradient descent–ascent, GDA):
U  ←  U  −  η_fit · ∇_U L_fit  +  η_push · P₋ ∇_U L_push
#            └ descend everywhere ┘   └ ascend, restricted to the timelike subspace K₋ ┘
```

- The equilibrium is a genuine saddle of `L_fit − L_push`: **fit the data while maximizing spread inside
  the suppression subspace** `K₋` — a meaningful target, not the degenerate saddle the naive full-loss
  flow seeks.
- This is the rigorous form of "push features apart rather than pull together": the *push-apart* term is
  the one carrying the ascent sign, by construction — not an accident of which loss term the timelike
  gradient happens to hit. (Note: ascending the standard `FP = mean ρ²` term would *increase*
  correlation, the opposite of intended — so the spread objective must be chosen and routed
  deliberately, e.g. maximize pairwise majorant distance, or maximize margin to confusable competitors.)
- **Caveat (GDA is not free):** descent–ascent can cycle rather than converge. Use the standard
  stabilizers — extragradient / optimistic GDA, a regularizer on the max player, or unequal step sizes
  (`η_push ≪ η_fit`). Treat convergence as empirical.

## Recipe 2 — transient escape, then anneal `J → I`

Use the instability as a feature early (to leave a poor initial basin), then revert to Euclidean descent
so the final phase converges:

```
J_γ = P₊ + γ · P₋ ,   schedule γ : −1  →  +1
#   γ = −1 : full reflection (indefinite, escape phase)
#   γ =  0 : P₊ (timelike frozen)
#   γ = +1 : identity (pure Euclidean descent, convergence phase)
U  ←  U  −  η · J_γ(t) ∇_U L
```

The preconditioner is genuinely indefinite only while `γ < 0`; once `γ ≥ 0` it is PSD, so the closing
phase is a real descent that lands in a minimum. Anneal on a schedule or trigger on a plateau.

## The two recipes at a glance

| | Recipe 1 — signature min–max | Recipe 2 — transient escape + anneal |
|---|---|---|
| **use case** | grow a *persistent* push-apart structure in `K₋` while fitting | *escape* a poor initial basin, then converge normally |
| **`J` over training** | fixed indefinite signature throughout | annealed `J_γ = P₊ + γP₋`, `γ: −1 → +1` |
| **what's optimized** | a genuine saddle of `L_fit − L_push` (min–max equilibrium) | the ordinary minimum of `L_fit` (once `γ ≥ 0`) |
| **convergence** | GDA — may **cycle**; needs extragradient / optimistic GDA / `η_push ≪ η_fit` | plain descent in the closing phase; converges as usual |
| **monitoring** | certified-margin mass **S2** (ascent can lower it); GDA gap | S2 only during the `γ < 0` phase |
| **when safer** | when you *want* the spread structure kept at the optimum | when you only want better minima (no persistent indefinite structure) |
| **both need** | majorant-norm guard (`O(p,q)` non-compactness) + best-fit checkpoint | majorant-norm guard during escape |

## Keeping PIC verification intact

The forward pass never sees `J`, so **every decode-side theorem applies to the current frame at every
step** (head/tail, margin certificate, capacity, irreducibility — all of `KreinDecode` + the proved
corpus). What changes per step is the frame `U`; `J` only shapes the trajectory. Concretely, against the
§6 soundness invariants:

| invariant (PIC_SPEC §6) | status under Scheme A |
|---|---|
| **S1** decode soundness (valid Euclidean decoder) | preserved by construction (forward is Euclidean) |
| **S2** certified-margin mass non-decreasing | **NOT automatic** — ascent moves can transiently lower it; **monitor**, and rely on annealing / best-checkpoint so the *final* frame satisfies it |
| **S3** frame admissibility `FP ≥ Welch` | holds for any real frame (structural) |

Practical guards:
- **Majorant-norm clip/projection** on each `U_v` — controls the `O(p,q)` non-compactness / norm
  explosion (the numerical face of the `q`-dim instability).
- **Best-fit checkpointing** — the trajectory is non-monotone, so keep the lowest-NLL frame seen, not
  the last.
- **Monitor** NLL, certified-margin mass (S2), `FP/Welch`, and the off-diagonal Gram distribution; the
  test is whether spread-ascent yields better packing/margins at *equal* NLL than a strong Euclidean
  baseline (SGD/AdamW). Prior (§6.1): SGD is hard to beat.

## Summary

`U̇ = −J∇L` on the full loss is saddle-seeking and repelled from minima (`indefinite_precond_not_descent`
+ the Sylvester instability), so it is not a training rule on its own. Made into a **min–max** (fit
descended in `K₊`, a deliberately chosen spread objective ascended in `K₋`) or used **transiently with
`J → I` annealing**, it becomes a principled "retrain-the-frame" knob whose final frame is fully covered
by the proved decode-side corpus. Whether it beats plain SGD is open and empirical.
