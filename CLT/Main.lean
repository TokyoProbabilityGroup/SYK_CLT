import SYK.Annealed_FE.main_result
import SYK.Annealed_FE.main_result
import SYK.Model.GaussianDisorder
import SYK.Model.FiniteDimensionalGibbs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.Lemmas
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
The only explicit analytic input is `AnnealedInput`, the annealed proposition
recorded in `Annealed_FE/main_result.lean`. The CLT proof remains incomplete
while the Gaussian chaos and logarithmic-transfer arguments are unproved.
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

@[simp]
theorem realPartitionFunction_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g : CouplingSpace P.N P.q) : realPartitionFunction P M 0 g = 1 := by
  simp [realPartitionFunction]

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
  have hH : star ((β : ℂ) • normalizedHamiltonian P M g) =
      (β : ℂ) • normalizedHamiltonian P M g := by
    simp [normalizedHamiltonian_self_adjoint]
  have h := SYK.partitionFunction_im_eq_zero (1 : ℝ≥0) hH
  simpa [partitionFunction, normalizedTrace, SYK.partitionFunction,
    gibbsOperator, smul_smul, Complex.div_natCast_im] using
    congrArg (fun x : ℝ ↦ x / (Fintype.card d : ℝ)) h
  have hH : star ((β : ℂ) • normalizedHamiltonian P M g) =
      (β : ℂ) • normalizedHamiltonian P M g := by
    simp [normalizedHamiltonian_self_adjoint]
  have h := SYK.partitionFunction_im_eq_zero (1 : ℝ≥0) hH
  simpa [partitionFunction, normalizedTrace, SYK.partitionFunction,
    gibbsOperator, smul_smul, Complex.div_natCast_im] using
    congrArg (fun x : ℝ ↦ x / (Fintype.card d : ℝ)) h

theorem realPartitionFunction_pos (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ)
    (g : CouplingSpace P.N P.q) : 0 < realPartitionFunction P M β g := by
  have hH : star ((β : ℂ) • normalizedHamiltonian P M g) =
      (β : ℂ) • normalizedHamiltonian P M g := by
    simp [normalizedHamiltonian_self_adjoint]
  have h := SYK.partitionFunction_pos (1 : ℝ≥0) hH
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
  simpa [realPartitionFunction, partitionFunction, normalizedTrace,
    SYK.partitionFunction, gibbsOperator, smul_smul, Complex.div_natCast_re] using
    div_pos h hd
  have hH : star ((β : ℂ) • normalizedHamiltonian P M g) =
      (β : ℂ) • normalizedHamiltonian P M g := by
    simp [normalizedHamiltonian_self_adjoint]
  have h := SYK.partitionFunction_pos (1 : ℝ≥0) hH
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
  simpa [realPartitionFunction, partitionFunction, normalizedTrace,
    SYK.partitionFunction, gibbsOperator, smul_smul, Complex.div_natCast_re] using
    div_pos h hd

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

/-- At `β = 0`, the partition function is constant and its disorder variance
is zero. Thus its standardized fluctuation is not a standard normal. -/
@[simp]
theorem varianceZ_zero (n : ℕ) : S.varianceZ 0 n = 0 := by
  have hZ : S.Z 0 n = fun _ ↦ (1 : ℝ) := by
    funext g
    exact realPartitionFunction_zero (S.params n) (S.majorana n) g
  rw [varianceZ, hZ]
  calc
    variance (fun _ ↦ (1 : ℝ)) _ = variance (fun _ ↦ 1 + 0) _ := by
      congr 1
      funext g
      norm_num
    _ = variance (fun _ ↦ (0 : ℝ)) _ :=
      variance_const_add (by fun_prop) 1
    _ = 0 := variance_zero _

noncomputable def standardizedFluctuation (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ℝ :=
  (S.Z β n g - S.meanZ β n) / Real.sqrt (S.varianceZ β n)

/-- The annealed free-energy density defining the limiting function `ℓ_q`. -/
noncomputable def annealedFreeEnergy (β : ℝ) (n : ℕ) : ℝ :=
  Real.log (S.meanZ β n) / (S.N n : ℝ)

/-- At `β = 0` the denominator of the standardized
fluctuation vanishes, so its standard Gaussian limit must exclude zero. -/
@[simp]
theorem varianceZ_zero (n : ℕ) : S.varianceZ 0 n = 0 := by
  have hz : S.Z 0 n = fun _ ↦ (1 : ℝ) := by
    funext g
    exact realPartitionFunction_zero (S.params n) (S.majorana n) g
  simp [varianceZ, hz, variance, evariance]

/-- Finite Gaussian models have the moments needed for these centerings. -/
theorem partition_moments (β : ℝ) (n : ℕ) :
    MemLp (S.Z β n) 2 (standardGaussianMeasure (S.N n) q) ∧
      Integrable (fun g ↦ Real.log (S.Z β n g)) (standardGaussianMeasure (S.N n) q) ∧
      0 < S.meanZ β n := by
  sorry

end Setting

/-! ## Main results -/

/-- The annealed proposition for the Gaussian families in this module. -/
abbrev AnnealedInput (q : ℕ) :=
  AnnealedFE.AnnealedFreeEnergyLimit q (Setting q) Setting.N Setting.meanZ

/-- Annealed pressure convergence follows from the permitted input. -/
theorem annealedFreeEnergy_tendsto {q : ℕ} (hFE : AnnealedInput q)
    (S : Setting q) {β : ℝ} (hβ : |β| < hFE.βFE) :
    Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) :=
  (hFE.pressure_limit S).tendsto_at (abs_lt.mp hβ)

/-- Convergence of the normalized beta derivative from the proposition. -/
theorem annealedDerivative_tendsto {q : ℕ} (hFE : AnnealedInput q)
    (S : Setting q) {β : ℝ} (hβ : |β| < hFE.βFE) :
    Tendsto (fun n ↦ deriv (fun b ↦ Real.log (S.meanZ b n)) β / (S.N n : ℝ))
      atTop (𝓝 (deriv hFE.ℓ β)) :=
  (hFE.derivative_limit S).tendsto_at (abs_lt.mp hβ)

/-- The normalized coefficient `A_N/N` tends to `β ℓ_q'(β)/2`. -/
theorem secondChaosCoefficient_tendsto {q : ℕ} (hFE : AnnealedInput q)
    (S : Setting q) {β : ℝ} (hβ : |β| < hFE.βFE) :
    Tendsto (fun n ↦ (β / 2 * deriv (fun b ↦ Real.log (S.meanZ b n)) β) /
      (S.N n : ℝ)) atTop (𝓝 (β / 2 * deriv hFE.ℓ β)) := by
  simpa only [mul_div_assoc] using
    (annealedDerivative_tendsto hFE S hβ).const_mul (β / 2)

/-- The common limiting variance `ρ²(β) = (q!/2) β² (ℓ_q'(β))²`.
It is allowed to vanish, in particular at `β = 0`. -/
noncomputable def limitVariance (q : ℕ) (ℓ : ℝ → ℝ) (β : ℝ) : ℝ≥0 :=
  ⟨(q.factorial : ℝ) / 2 * β ^ 2 * (deriv ℓ β) ^ 2, by positivity⟩

/-- The derivative expansion implies the corrected sign conclusion
`β ℓ_q'(β)>0` at sufficiently small nonzero `β`. -/
theorem exists_small_temperature_sign {q : ℕ} (hq : 0 < q)
    (hFE : AnnealedInput q) :
    ∃ r : ℝ, 0 < r ∧ r ≤ hFE.βFE ∧
      ∀ β : ℝ, |β| < r → β ≠ 0 → 0 < β * deriv hFE.ℓ β := by
  have hqinv : 0 < (q : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hq)
  have ho := hFE.derivative_expansion.trans_isLittleO
    (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by decide : 1 < 3))
  have hb := ho.bound (half_pos hqinv)
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨min δ hFE.βFE, lt_min hδ hFE.βFE_pos, min_le_right _ _, ?_⟩
  intro β hβ hβ0
  have hdist : dist β 0 < δ := by
    simpa [Real.dist_eq] using lt_of_lt_of_le hβ (min_le_left δ hFE.βFE)
  have h := hbound hdist
  simp only [Real.norm_eq_abs, div_eq_mul_inv] at h
  rcases lt_or_gt_of_ne hβ0 with hneg | hpos
  · rw [abs_of_neg hneg] at h
    have hu := (abs_le.mp h).2
    exact mul_pos_of_neg_of_neg hneg (by nlinarith [mul_neg_of_neg_of_pos hneg hqinv])
  · rw [abs_of_pos hpos] at h
    have hl := (abs_le.mp h).1
    exact mul_pos hpos (by nlinarith [mul_pos hpos hqinv])

/-- The limiting variance is positive at the small nonzero temperatures
selected by the annealed derivative expansion. -/
theorem exists_small_temperature_variance_pos {q : ℕ} (hq : 0 < q)
    (hFE : AnnealedInput q) :
    ∃ r : ℝ, 0 < r ∧ r ≤ hFE.βFE ∧
      ∀ β : ℝ, |β| < r → β ≠ 0 → 0 < limitVariance q hFE.ℓ β := by
  obtain ⟨r, hr, hle, hsign⟩ := exists_small_temperature_sign hq hFE
  refine ⟨r, hr, hle, ?_⟩
  intro β hβ hβ0
  have hd : deriv hFE.ℓ β ≠ 0 := by
    intro hd
    simpa [hd] using hsign β hβ hβ0
  change (0 : ℝ) < (q.factorial : ℝ) / 2 * β ^ 2 * (deriv hFE.ℓ β) ^ 2
  exact mul_pos
    (mul_pos (div_pos (Nat.cast_pos.mpr q.factorial_pos) (by norm_num))
      (sq_pos_of_ne_zero hβ0)) (sq_pos_of_ne_zero hd)

/-- `thm:partition-clt` and `cor:free-energy-clt`, with one common temperature
radius and annealed limit for every general matrix Majorana family.

The limit is the identity random variable on `ℝ` with law
`gaussianReal 0 (limitVariance q ℓ β)`. Thus the conclusion expresses weak
convergence of probability laws, including the Dirac law at zero variance.
The limiting function is the one supplied by the annealed proposition.
Positivity is a conclusion wherever standardization is used.

The proof placeholders cover the annealed input, Gaussian chaos estimates,
classical CLT, and transfer to the centered logarithm. -/
theorem partition_and_log_partition_clt (q : ℕ) (_hq : Even q) (_h4 : 4 ≤ q)
    (hFE : AnnealedInput q) :
    ∃ βq : ℝ, 0 < βq ∧ βq ≤ hFE.βFE ∧
      ∀ (S : Setting q) (β : ℝ), |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        (β ≠ 0 →
          0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
          0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
          TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
            (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1)) := by
  sorry

/-- The partition-function part of `thm:partition-clt`. The joint theorem
above additionally supplies the standardized CLT at nonzero temperature. -/
theorem partition_clt (q : ℕ) (hq : Even q) (h4 : 4 ≤ q)
    (hFE : AnnealedInput q) :
    ∃ βq : ℝ, 0 < βq ∧ βq ≤ hFE.βFE ∧
      ∀ (S : Setting q) (β : ℝ), |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        (β ≠ 0 →
          0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
          TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
            (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1)) := by
  obtain ⟨βq, hβq, hle, h⟩ := partition_and_log_partition_clt q hq h4 hFE
  refine ⟨βq, hβq, hle, ?_⟩
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        (β ≠ 0 →
          0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
          TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
            (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1)) := by
  obtain ⟨βq, hβq, hle, h⟩ := partition_and_log_partition_clt q hq h4 hFE
  refine ⟨βq, hβq, hle, ?_⟩
  intro S β hβ
  exact ⟨(h S β hβ).1, (h S β hβ).2.1, (h S β hβ).2.2.2⟩
  exact ⟨(h S β hβ).1, (h S β hβ).2.1, (h S β hβ).2.2.2⟩

/-- The centered log-partition CLT of `cor:free-energy-clt`.
The joint theorem supplies the same radius and variance for both CLTs. -/
theorem log_partition_clt (q : ℕ) (hq : Even q) (h4 : 4 ≤ q)
    (hFE : AnnealedInput q) :
    ∃ βq : ℝ, 0 < βq ∧ βq ≤ hFE.βFE ∧
theorem log_partition_clt (q : ℕ) (hq : Even q) (h4 : 4 ≤ q)
    (hFE : AnnealedInput q) :
    ∃ βq : ℝ, 0 < βq ∧ βq ≤ hFE.βFE ∧
      ∀ (S : Setting q) (β : ℝ), |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) := by
  obtain ⟨βq, hβq, hle, h⟩ := partition_and_log_partition_clt q hq h4 hFE
  refine ⟨βq, hβq, hle, ?_⟩
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) := by
  obtain ⟨βq, hβq, hle, h⟩ := partition_and_log_partition_clt q hq h4 hFE
  refine ⟨βq, hβq, hle, ?_⟩
  intro S β hβ
  exact ⟨(h S β hβ).1, (h S β hβ).2.2.1⟩

end SYK.CLT
