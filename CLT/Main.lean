import SYK.CLT.Lemmas.CLTComponents
import SYK.CLT.Lemmas.GaussianConcentration
import SYK.Model.GaussianDisorder
import SYK.Model.FiniteDimensionalGibbs
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Moments.Variance

/-!
# Central limit theorem for the SYK model

The setting uses an arbitrary nonempty finite-dimensional matrix Majorana
system, the shared Gaussian Hamiltonian, and normalized trace. The main
statements correspond to `thm:partition-clt` and `cor:free-energy-clt`.

As requested, inverse temperature is real and the high-temperature condition
is `|β| < βq`. This supersedes the planned nonnegative-temperature restriction
for these declarations. The standardized CLT excludes `β = 0`; the relative
and logarithmic CLTs include its degenerate Gaussian limit.

Proofs marked `sorry` are placeholders, not formal proofs of the manuscript.
The almost-sure free-energy law of large numbers is outside this module's
present scope.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SYK.CLT

local instance (N q : ℕ) : IsProbabilityMeasure (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
  infer_instance

/-! ## Finite models -/

section FiniteModel

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The manuscript's `Z_N(z;G) = tr exp(-z H_N(G))`, with trace divided
by the representation dimension. In the standard representation this
dimension is `2^(N/2)`. No irreducibility assumption is imposed. -/
noncomputable def partitionFunction (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (z : ℂ)
    (g : CouplingSpace P.N P.q) : ℂ :=
  normalizedTrace (gibbsOperator z (normalizedHamiltonian P M g))

/-- Real partition function at real inverse temperature. The imaginary part
vanishes and this real part is strictly positive, as stated below. -/
noncomputable def realPartitionFunction (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ)
    (g : CouplingSpace P.N P.q) : ℝ :=
  (partitionFunction P M (β : ℂ) g).re

@[simp]
theorem partitionFunction_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g : CouplingSpace P.N P.q) : partitionFunction P M 0 g = 1 := by
  simp [partitionFunction]

/-- Agreement with the shared partition function, which uses ordinary trace. -/
theorem partitionFunction_eq_trace_div_card (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (z : ℂ)
    (g : CouplingSpace P.N P.q) :
    partitionFunction P M z g =
      SYK.partitionFunction z (normalizedHamiltonian P M g) / (Fintype.card d : ℂ) :=
  rfl

theorem partitionFunction_im_eq_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ)
    (g : CouplingSpace P.N P.q) :
    (partitionFunction P M (β : ℂ) g).im = 0 := by
  sorry

theorem realPartitionFunction_pos (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ)
    (g : CouplingSpace P.N P.q) : 0 < realPartitionFunction P M β g := by
  sorry

end FiniteModel

/-! ## Large-system setting -/

/-- A family of general matrix Majorana systems at fixed even order `q ≥ 4`.
The sizes are even, at least `q`, and tend to infinity. Universally quantifying
over such families includes the full even-size limit and every diverging
even-size subsequence. Each size has its own Gaussian coupling space;
distributional convergence does not require a common probability space. -/
structure Setting (q : ℕ) where
  /-- The interaction order is even. -/
  q_even : Even q
  /-- The CLT regime has interaction order at least four. -/
  q_ge_four : 4 ≤ q
  /-- Number of Majorana generators in each model. -/
  N : ℕ → ℕ
  /-- Each model has even size. -/
  N_even : ∀ n, Even (N n)
  /-- Each size supports a `q`-body interaction. -/
  q_le_N : ∀ n, q ≤ N n
  /-- The system sizes tend to infinity. -/
  N_tendsto : Tendsto N atTop atTop
  /-- Matrix basis index type, allowed to vary with system size. -/
  d : ℕ → Type
  /-- Each representation is finite dimensional. -/
  fintype : ∀ n, Fintype (d n)
  /-- Decidable equality for matrix multiplication. -/
  decidableEq : ∀ n, DecidableEq (d n)
  /-- Each representation has positive dimension. -/
  nonempty : ∀ n, Nonempty (d n)
  /-- The Majorana generators with the shared adjoint and CAR conventions. -/
  majorana : ∀ n,
    letI := fintype n
    letI := decidableEq n
    MajoranaSystem (N n) (Matrix (d n) (d n) ℂ)

attribute [instance] Setting.fintype Setting.decidableEq Setting.nonempty

namespace Setting

variable {q : ℕ} (S : Setting q)

/-- Parameters passed to the shared SYK model. -/
def params (n : ℕ) : Params where
  N := S.N n
  q := q
  q_even := S.q_even
  q_pos := lt_of_lt_of_le (by decide : 0 < 4) S.q_ge_four
  q_le_N := S.q_le_N n

/-- `Z_N(β;G)`, with Gaussian coefficient variance `(q-1)!/N^(q-1)`. -/
noncomputable def Z (β : ℝ) (n : ℕ) : CouplingSpace (S.N n) q → ℝ :=
  realPartitionFunction (S.params n) (S.majorana n) β

/-- Disorder expectation `E Z_N(β)`. -/
noncomputable def meanZ (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, S.Z β n g ∂standardGaussianMeasure (S.N n) q

/-- Relative partition function `Y_N = Z_N / E Z_N`. -/
noncomputable def Y (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) : ℝ :=
  S.Z β n g / S.meanZ β n

/-- Disorder expectation `E log Z_N(β)`, rather than `log E Z_N(β)`. -/
noncomputable def meanLogZ (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, Real.log (S.Z β n g) ∂standardGaussianMeasure (S.N n) q

/-- The common CLT scaling `N^(q/2-1)`; `q/2` is exact since `q` is even. -/
def fluctuationScale (n : ℕ) : ℝ := (S.N n : ℝ) ^ (q / 2 - 1)

noncomputable def relativeFluctuation (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ℝ :=
  S.fluctuationScale n * (S.Y β n g - 1)

noncomputable def logFluctuation (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ℝ :=
  S.fluctuationScale n * (Real.log (S.Z β n g) - S.meanLogZ β n)

/-- Variance with respect to Gaussian disorder, not spectral variance. -/
noncomputable def varianceZ (β : ℝ) (n : ℕ) : ℝ :=
  variance (S.Z β n) (standardGaussianMeasure (S.N n) q)

noncomputable def standardizedFluctuation (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ℝ :=
  (S.Z β n g - S.meanZ β n) / Real.sqrt (S.varianceZ β n)

/-- The annealed free-energy density defining the limiting function `ℓ_q`. -/
noncomputable def annealedFreeEnergy (β : ℝ) (n : ℕ) : ℝ :=
  Real.log (S.meanZ β n) / (S.N n : ℝ)

/-- Finite Gaussian models have the moments needed for these centerings. -/
theorem partition_moments (β : ℝ) (n : ℕ) :
    MemLp (S.Z β n) 2 (standardGaussianMeasure (S.N n) q) ∧
      Integrable (fun g ↦ Real.log (S.Z β n g)) (standardGaussianMeasure (S.N n) q) ∧
      0 < S.meanZ β n := by
  sorry

end Setting

/-! ## Main results -/

/-- The common limiting variance `ρ²(β) = (q!/2) β² (ℓ_q'(β))²`.
It is allowed to vanish, in particular at `β = 0`. -/
noncomputable def limitVariance (q : ℕ) (ℓ : ℝ → ℝ) (β : ℝ) : ℝ≥0 :=
  ⟨(q.factorial : ℝ) / 2 * β ^ 2 * (deriv ℓ β) ^ 2, by positivity⟩

/-- `thm:partition-clt` and `cor:free-energy-clt`, with one common temperature
radius and annealed limit for every general matrix Majorana family.

The limit is the identity random variable on `ℝ` with law
`gaussianReal 0 (limitVariance q ℓ β)`. Thus the conclusion expresses weak
convergence of probability laws, including the Dirac law at zero variance.
The annealed limit identifies `ℓ`, so the variance is not an arbitrary
parameter. Positivity is explicit wherever standardization is used.

The proof placeholders cover the annealed input, Gaussian chaos estimates,
classical CLT, and transfer to the centered logarithm. -/
theorem partition_and_log_partition_clt (q : ℕ) (_hq : Even q) (_h4 : 4 ≤ q) :
    ∃ βq : ℝ, 0 < βq ∧ ∃ ℓ : ℝ → ℝ,
      DifferentiableOn ℝ ℓ (Set.Ioo (-βq) βq) ∧
      ∀ (S : Setting q) (β : ℝ), |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q ℓ β)) ∧
        (β ≠ 0 →
          0 < limitVariance q ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
          TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
            (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1)) := by
  sorry

/-- The partition-function part of `thm:partition-clt`. The joint theorem
above additionally supplies the standardized CLT at nonzero temperature. -/
theorem partition_clt (q : ℕ) (hq : Even q) (h4 : 4 ≤ q) :
    ∃ βq : ℝ, 0 < βq ∧ ∃ ℓ : ℝ → ℝ,
      DifferentiableOn ℝ ℓ (Set.Ioo (-βq) βq) ∧
      ∀ (S : Setting q) (β : ℝ), |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q ℓ β)) := by
  obtain ⟨βq, hβq, ℓ, hℓ, h⟩ := partition_and_log_partition_clt q hq h4
  refine ⟨βq, hβq, ℓ, hℓ, ?_⟩
  intro S β hβ
  exact ⟨(h S β hβ).1, (h S β hβ).2.1⟩

/-- The centered log-partition CLT of `cor:free-energy-clt`.
The joint theorem supplies the same radius and variance for both CLTs. -/
theorem log_partition_clt (q : ℕ) (hq : Even q) (h4 : 4 ≤ q) :
    ∃ βq : ℝ, 0 < βq ∧ ∃ ℓ : ℝ → ℝ,
      DifferentiableOn ℝ ℓ (Set.Ioo (-βq) βq) ∧
      ∀ (S : Setting q) (β : ℝ), |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q ℓ β)) := by
  obtain ⟨βq, hβq, ℓ, hℓ, h⟩ := partition_and_log_partition_clt q hq h4
  refine ⟨βq, hβq, ℓ, hℓ, ?_⟩
  intro S β hβ
  exact ⟨(h S β hβ).1, (h S β hβ).2.2.1⟩

end SYK.CLT
