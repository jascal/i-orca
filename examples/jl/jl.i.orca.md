<!--
  i-orca surface for the JOHNSON-LINDENSTRAUSS lemma -- the fourth entry in i-orca's
  "canonical proofs from other authors" track (after watermark, tropical, superposition).

  Source: W. B. Johnson & J. Lindenstrauss, "Extensions of Lipschitz mappings into a
  Hilbert space", Contemporary Mathematics 26 (1984) 189-206. The lemma: n points in a
  high-dimensional Euclidean space embed into O(log n / eps^2) dimensions with all
  pairwise distances preserved up to a factor 1 +/- eps, via a random projection.

  We formalise the three structural pillars of the standard (random-projection) proof:

    EXPECTATION -- a random projection preserves squared norm in expectation
                   (JLProjection.thy, the second-moment identity);
    DIMENSION   -- a target dimension k > ln N / c kills the union bound, giving the
                   O(log n / eps^2) bound (JLDimension.thy);
    EXISTENCE   -- the probabilistic method: few rare bad events imply a good projection
                   exists (JLExistence.thy).

  The Gaussian concentration of a single coordinate (the chi-squared tail that bounds the
  per-pair failure probability) is the META input, supplied as a hypothesis; everything
  structural around it is kernel-checked. As in the sibling corpora, heavy content lives
  in the Isabelle theories here and each theorem below is discharged by `(rule <lemma>)`.

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID, fraction 1.000.
    - Kernel check: built INSIDE the `JL` session (this directory's ROOT):
          ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/jl \
            -o quick_and_dirty JL
      (standalone `i-orca check` cannot load the project-local session -- same caveat as
      the other corpora.)

  Map to the proof:
    EXPECTATION    -> ExpectationLinearOverSum, ProjectionUnbiased
    DIMENSION      -> DimensionUnionBound, LogarithmicDimension
    EXISTENCE      -> ProbabilisticMethod, GoodProjectionExists
    WORKED EXAMPLE -> ExampleGoodProjectionExists
-->

# theorem ExpectationLinearOverSum
> A linear expectation functional commutes with finite sums: `E[∑ₐ Fₐ] = ∑ₐ E[Fₐ]`. The workhorse for pushing the expectation through the expanded square below. Cites `expectation_sum'`.

## imports
| Theory       |
|--------------|
| JLProjection |

## goal
| Statement |
|-----------|
| lin_exp Exp ⟹ finite A ⟹ Exp (λs. ∑a∈A. F a s) = (∑a∈A. Exp (F a)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | lin_exp Exp ⟹ finite A ⟹ Exp (λs. ∑a∈A. F a s) = (∑a∈A. Exp (F a)) | additivity, lifted over a finite sum by induction | — | (rule expectation_sum') | method |


# theorem ProjectionUnbiased
> The expectation half of Johnson–Lindenstrauss (the "distortion-free in expectation" core, parallel to the watermark's unbiasedness). For coordinate variables that are uncorrelated with unit mean-square, the expected squared length of the random projection equals the squared length: `E[(∑ⱼ xⱼ gⱼ)²] = ∑ⱼ xⱼ²`. Cites `projection_unbiased'`.

## imports
| Theory       |
|--------------|
| JLProjection |

## goal
| Statement |
|-----------|
| finite J ⟹ lin_exp Exp ⟹ (∀j∈J. ∀l∈J. Exp (λs. g j s * g l s) = (if j = l then 1 else 0)) ⟹ Exp (λs. (∑j∈J. x j * g j s)\<^sup>2) = (∑j∈J. (x j)\<^sup>2) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite J ⟹ lin_exp Exp ⟹ (∀j∈J. ∀l∈J. Exp (λs. g j s * g l s) = (if j = l then 1 else 0)) ⟹ Exp (λs. (∑j∈J. x j * g j s)\<^sup>2) = (∑j∈J. (x j)\<^sup>2) | expand the square, push E through, and collapse by the orthonormal second moments | — | (rule projection_unbiased') | method |


# theorem DimensionUnionBound
> The dimension inequality driving the union bound below 1: once the target dimension `k` exceeds `ln N / c`, the total failure bound `N · exp(−c k)` is less than 1. Cites `jl_dimension`.

## imports
| Theory      |
|-------------|
| JLDimension |

## goal
| Statement |
|-----------|
| 0 < N ⟹ 0 < c ⟹ ln N / c < k ⟹ N * exp (- c * k) < (1::real) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < N ⟹ 0 < c ⟹ ln N / c < k ⟹ N * exp (- c * k) < (1::real) | k beyond ln N / c makes exp(-c k) drop below 1/N | — | (rule jl_dimension) | method |


# theorem LogarithmicDimension
> The famous bound: a target dimension `k > 16·ln(n)/ε²` drives the `n²`-pair union bound below 1 (with per-pair concentration constant `c = ε²/8`) — the `O(log n / ε²)` Johnson–Lindenstrauss dimension. Cites `jl_log_dimension`.

## imports
| Theory      |
|-------------|
| JLDimension |

## goal
| Statement |
|-----------|
| 2 ≤ n ⟹ 0 < eps ⟹ (16 * ln (real n)) / eps\<^sup>2 < k ⟹ real (n * n) * exp (- (eps\<^sup>2 / 8) * k) < 1 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 2 ≤ n ⟹ 0 < eps ⟹ (16 * ln (real n)) / eps\<^sup>2 < k ⟹ real (n * n) * exp (- (eps\<^sup>2 / 8) * k) < 1 | substitute N = n², c = ε²/8 into the union-bound inequality | — | (rule jl_log_dimension) | method |


# theorem ProbabilisticMethod
> The probabilistic method (finite form): if the bad events jointly cover strictly less than the whole sample space (the sum of their sizes is below the total), then a point avoiding all of them exists. The combinatorial heart of "a good projection exists". Cites `probabilistic_method'`.

## imports
| Theory      |
|-------------|
| JLExistence |

## goal
| Statement |
|-----------|
| finite Omega ⟹ finite I ⟹ (∀i∈I. bad i ⊆ Omega) ⟹ (∑i∈I. card (bad i)) < card Omega ⟹ (∃w∈Omega. ∀i∈I. w ∉ bad i) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite Omega ⟹ finite I ⟹ (∀i∈I. bad i ⊆ Omega) ⟹ (∑i∈I. card (bad i)) < card Omega ⟹ (∃w∈Omega. ∀i∈I. w ∉ bad i) | the union of the bad sets is smaller than Omega, so its complement is nonempty | — | (rule probabilistic_method') | method |


# theorem GoodProjectionExists
> The assembled Johnson–Lindenstrauss existence: combine the per-pair concentration bound (`card(bad p) ≤ q·card Ω`) with the small constraint count (`card P · q < 1`, from the dimension bound) — by the probabilistic method, a projection preserving every pair exists. Cites `jl_good_projection_exists'`.

## imports
| Theory      |
|-------------|
| JLExistence |

## goal
| Statement |
|-----------|
| finite Omega ⟹ Omega ≠ {} ⟹ finite P ⟹ (∀p∈P. bad p ⊆ Omega) ⟹ (∀p∈P. real (card (bad p)) ≤ q * real (card Omega)) ⟹ real (card P) * q < 1 ⟹ (∃R∈Omega. ∀p∈P. R ∉ bad p) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite Omega ⟹ Omega ≠ {} ⟹ finite P ⟹ (∀p∈P. bad p ⊆ Omega) ⟹ (∀p∈P. real (card (bad p)) ≤ q * real (card Omega)) ⟹ real (card P) * q < 1 ⟹ (∃R∈Omega. ∀p∈P. R ∉ bad p) | the total bad mass is below the whole space, so a good projection survives | — | (rule jl_good_projection_exists') | method |


# theorem ExampleGoodProjectionExists
> A concrete instance of the existence pillar: four candidate projections `{0,1,2,3}`, two constraints, each violated only by one projection (`bad i = {i}`). Only two of the four are ever bad, so a projection avoiding both constraints exists (2 or 3) — the union-bound argument in miniature. Cites `example_good_projection_exists`.

## imports
| Theory   |
|----------|
| Examples |

## goal
| Statement |
|-----------|
| ∃w∈{0,1,2,3::nat}. ∀i∈{0,1::nat}. w ∉ {i} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∃w∈{0,1,2,3::nat}. ∀i∈{0,1::nat}. w ∉ {i} | two bad projections out of four leave a good one standing | — | (rule example_good_projection_exists) | method |
