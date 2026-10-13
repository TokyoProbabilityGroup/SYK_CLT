module

public import SYK.CLT.FiniteModel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Normed -- shake: keep (Matrix.Norms.Operator scope)

public section

/-!
# Setting and annealed input for the SYK central limit theorem

The setting uses an arbitrary nonempty finite-dimensional matrix Majorana
system, the shared Gaussian Hamiltonian, and normalized trace. The main
statements in `SYK/CLT/Main.lean` correspond to `thm:partition-clt` and
`thm:free-energy-clt`.

Inverse temperature is real, and the main CLT statements use
`|β| < βq` together with `β ≠ 0`. The relative, standardized, and
logarithmic CLTs all exclude zero inverse temperature; finite-model
zero-inverse-temperature identities remain available separately.

The explicit annealed input is `AnnealedInput`, containing the assertions of
`prop:annealed-free-energy` for the given family in the CLT manuscript.
The proposition itself is assumed. The Gaussian chaos and
logarithmic-transfer arguments are proved in the supporting lemma modules
and assembled in `SYK/CLT/Main.lean`.
The almost-sure free-energy law of large numbers is outside this module's
present scope.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
open scoped Matrix.Norms.Operator

namespace SYK.CLT

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
@[expose] def params (n : ℕ) : Params where
  N := S.N n
  q := q
  q_even := S.q_even
  q_pos := lt_of_lt_of_le (by decide : 0 < 4) S.q_ge_four
  q_le_N := S.q_le_N n

/-- `Z_N(β;G)`, with Gaussian coefficient variance `(q-1)!/N^(q-1)`. -/
@[expose] noncomputable def Z (β : ℝ) (n : ℕ) : CouplingSpace (S.N n) q → ℝ :=
  realPartitionFunction (S.params n) (S.majorana n) β

theorem Z_ge_one (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    1 ≤ S.Z β n g :=
  realPartitionFunction_ge_one (S.params n) (S.majorana n) β g


theorem log_Z_nonneg (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    0 ≤ Real.log (S.Z β n g) :=
  Real.log_nonneg (S.Z_ge_one β n g)

/-- Disorder expectation `E Z_N(β)`. -/
@[expose] noncomputable def meanZ (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, S.Z β n g ∂standardGaussianMeasure (S.N n) q

/-- Relative partition function `Y_N = Z_N / E Z_N`. -/
@[expose] noncomputable def Y (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) : ℝ :=
  S.Z β n g / S.meanZ β n

/-- Disorder expectation `E log Z_N(β)`, rather than `log E Z_N(β)`. -/
@[expose] noncomputable def meanLogZ (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, Real.log (S.Z β n g) ∂standardGaussianMeasure (S.N n) q

/-- The common CLT scaling `N^(q/2-1)`; `q/2` is exact since `q` is even. -/
@[expose] def fluctuationScale (n : ℕ) : ℝ := (S.N n : ℝ) ^ (q / 2 - 1)

/-- Scaled relative fluctuation `N^(q/2-1) (Y_N - 1)`. -/
@[expose] noncomputable def relativeFluctuation (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ℝ :=
  S.fluctuationScale n * (S.Y β n g - 1)

/-- Scaled centered logarithmic fluctuation `N^(q/2-1) (log Z_N - E log Z_N)`. -/
@[expose] noncomputable def logFluctuation (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ℝ :=
  S.fluctuationScale n * (Real.log (S.Z β n g) - S.meanLogZ β n)

/-- Variance with respect to Gaussian disorder, not spectral variance. -/
@[expose] noncomputable def varianceZ (β : ℝ) (n : ℕ) : ℝ :=
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

@[simp]
theorem meanZ_zero (n : ℕ) : S.meanZ 0 n = 1 := by
  simp [meanZ, Z]

@[simp]
theorem Y_zero (n : ℕ) (g : CouplingSpace (S.N n) q) : S.Y 0 n g = 1 := by
  simp [Y, Z]

@[simp]
theorem meanLogZ_zero (n : ℕ) : S.meanLogZ 0 n = 0 := by
  simp [meanLogZ, Z]

@[simp]
theorem relativeFluctuation_zero (n : ℕ) (g : CouplingSpace (S.N n) q) :
    S.relativeFluctuation 0 n g = 0 := by
  simp [relativeFluctuation]

@[simp]
theorem logFluctuation_zero (n : ℕ) (g : CouplingSpace (S.N n) q) :
    S.logFluctuation 0 n g = 0 := by
  simp [logFluctuation, Z]

/-- The centered partition function divided by its disorder standard deviation. -/
@[expose] noncomputable def standardizedFluctuation (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ℝ :=
  (S.Z β n g - S.meanZ β n) / Real.sqrt (S.varianceZ β n)

/-- The annealed free-energy density defining the limiting function `ℓ_q`. -/
@[expose] noncomputable def annealedFreeEnergy (β : ℝ) (n : ℕ) : ℝ :=
  Real.log (S.meanZ β n) / (S.N n : ℝ)

/-- Apply the finite-model moment theorem to a member of the family. -/
theorem partition_moments (β : ℝ) (n : ℕ) :
    MemLp (S.Z β n) 2 (standardGaussianMeasure (S.N n) q) ∧
      Integrable (fun g ↦ Real.log (S.Z β n g)) (standardGaussianMeasure (S.N n) q) ∧
      0 < S.meanZ β n :=
  realPartitionFunction_moments (S.params n) (S.majorana n) β

/-- Normalization preserves the second moment. -/
theorem Y_memLp (β : ℝ) (n : ℕ) :
    MemLp (S.Y β n) 2 (standardGaussianMeasure (S.N n) q) := by
  change MemLp (fun g ↦ S.Z β n g / S.meanZ β n) 2 _
  simpa only [div_eq_mul_inv, mul_comm] using
    ((S.partition_moments β n).1.const_mul (S.meanZ β n)⁻¹)

theorem Y_integrable (β : ℝ) (n : ℕ) :
    Integrable (S.Y β n) (standardGaussianMeasure (S.N n) q) :=
  (S.Y_memLp β n).integrable (by norm_num)

theorem Y_pos (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    0 < S.Y β n g :=
  div_pos (lt_of_lt_of_le zero_lt_one (S.Z_ge_one β n g))
    (S.partition_moments β n).2.2

/-- The normalization in `eq:Y_N` has expectation one. -/
theorem integral_Y (β : ℝ) (n : ℕ) :
    (∫ g, S.Y β n g ∂standardGaussianMeasure (S.N n) q) = 1 := by
  change (∫ g, S.Z β n g / S.meanZ β n ∂standardGaussianMeasure (S.N n) q) = 1
  rw [integral_div]
  exact div_self (ne_of_gt (S.partition_moments β n).2.2)

theorem meanZ_ge_one (β : ℝ) (n : ℕ) : 1 ≤ S.meanZ β n := by
  have hZint := (S.partition_moments β n).1.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  calc
    (1 : ℝ) = ∫ _g : CouplingSpace (S.N n) q, (1 : ℝ)
        ∂standardGaussianMeasure (S.N n) q := by simp
    _ ≤ S.meanZ β n := integral_mono (integrable_const _) hZint (S.Z_ge_one β n)

theorem log_meanZ_nonneg (β : ℝ) (n : ℕ) : 0 ≤ Real.log (S.meanZ β n) :=
  Real.log_nonneg (S.meanZ_ge_one β n)

theorem log_Y_eq (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    Real.log (S.Y β n g) = Real.log (S.Z β n g) - Real.log (S.meanZ β n) :=
  Real.log_div (ne_of_gt (lt_of_lt_of_le zero_lt_one (S.Z_ge_one β n g)))
    (ne_of_gt (S.partition_moments β n).2.2)

theorem log_Y_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g ↦ Real.log (S.Y β n g))
      (standardGaussianMeasure (S.N n) q) := by
  simp_rw [S.log_Y_eq β n]
  exact (S.partition_moments β n).2.1.sub (integrable_const _)

theorem integral_log_Y (β : ℝ) (n : ℕ) :
    (∫ g, Real.log (S.Y β n g) ∂standardGaussianMeasure (S.N n) q) =
      S.meanLogZ β n - Real.log (S.meanZ β n) := by
  simp_rw [S.log_Y_eq β n]
  rw [integral_sub (S.partition_moments β n).2.1 (integrable_const _)]
  simp [meanLogZ]

/-- The two logarithmic centerings agree in `thm:free-energy-clt`. -/
theorem centered_log_Y_eq (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    Real.log (S.Y β n g) -
        (∫ x, Real.log (S.Y β n x) ∂standardGaussianMeasure (S.N n) q) =
      Real.log (S.Z β n g) - S.meanLogZ β n := by
  rw [S.log_Y_eq, S.integral_log_Y]
  ring

/-- Pointwise input for the small-event estimate in `thm:free-energy-clt`. -/
theorem neg_log_Y_le_log_meanZ (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    -Real.log (S.Y β n g) ≤ Real.log (S.meanZ β n) := by
  rw [S.log_Y_eq]
  linarith [S.log_Z_nonneg β n g]

end Setting

/-! ## Main results -/

/-- `prop:annealed-free-energy` for one Gaussian SYK model family.
This structure receives the proposition's assertions as an explicit input:
an even convex `C¹` limit, locally uniform pressure and derivative convergence
on the whole real line, and the sign at every nonzero inverse temperature.
The proposition itself and construction of this input are not proved here. -/
structure AnnealedInput (q : ℕ) (S : Setting q) where
  /-- The limiting annealed pressure `ℓ_q`. -/
  ℓ : ℝ → ℝ
  /-- `ℓ_q` is even. -/
  even : ∀ β : ℝ, ℓ (-β) = ℓ β
  /-- `ℓ_q` is convex on the real line. -/
  convex : ConvexOn ℝ Set.univ ℓ
  /-- `ℓ_q` is continuously differentiable. -/
  contDiff_one : ContDiff ℝ 1 ℓ
  /-- The annealed free energies converge to `ℓ_q` locally uniformly on `ℝ`. -/
  pressure_limit : TendstoLocallyUniformlyOn
    (fun n β ↦ S.annealedFreeEnergy β n) ℓ atTop Set.univ
  /-- The normalized derivatives of `log E Z` converge to `ℓ_q'` locally uniformly on `ℝ`. -/
  derivative_limit : TendstoLocallyUniformlyOn
    (fun n β ↦ deriv (fun b ↦ Real.log (S.meanZ b n)) β / (S.N n : ℝ))
    (deriv ℓ) atTop Set.univ
  /-- `β ℓ_q'(β) > 0` for every nonzero inverse temperature `β`. -/
  sign : ∀ β : ℝ, β ≠ 0 → 0 < β * deriv ℓ β

/-- Annealed pressure convergence follows from the permitted input. -/
theorem annealedFreeEnergy_tendsto {q : ℕ} {S : Setting q}
    (hFE : AnnealedInput q S) (β : ℝ) :
    Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) :=
  hFE.pressure_limit.tendsto_at (Set.mem_univ β)

/-- Convergence of the normalized beta derivative from the proposition. -/
theorem annealedDerivative_tendsto {q : ℕ} {S : Setting q}
    (hFE : AnnealedInput q S) (β : ℝ) :
    Tendsto (fun n ↦ deriv (fun b ↦ Real.log (S.meanZ b n)) β / (S.N n : ℝ))
      atTop (𝓝 (deriv hFE.ℓ β)) :=
  hFE.derivative_limit.tendsto_at (Set.mem_univ β)

/-- The normalized coefficient `A_N/N` tends to `β ℓ_q'(β)/2`. -/
theorem secondChaosCoefficient_tendsto {q : ℕ} {S : Setting q}
    (hFE : AnnealedInput q S) (β : ℝ) :
    Tendsto (fun n ↦ (β / 2 * deriv (fun b ↦ Real.log (S.meanZ b n)) β) /
      (S.N n : ℝ)) atTop (𝓝 (β / 2 * deriv hFE.ℓ β)) := by
  simpa only [mul_div_assoc] using
    (annealedDerivative_tendsto hFE β).const_mul (β / 2)

/-- The common limiting variance `ρ²(β) = (q!/2) β² (ℓ_q'(β))²`.
It is allowed to vanish, in particular at `β = 0`. -/
@[expose] noncomputable def limitVariance (q : ℕ) (ℓ : ℝ → ℝ) (β : ℝ) : ℝ≥0 :=
  ⟨(q.factorial : ℝ) / 2 * β ^ 2 * (deriv ℓ β) ^ 2, by positivity⟩

/-- Under `prop:annealed-free-energy`, the limiting variance is positive at every
nonzero real inverse temperature. -/
theorem limitVariance_pos_of_ne_zero {q : ℕ} {S : Setting q}
    (hFE : AnnealedInput q S) (β : ℝ) (hβ0 : β ≠ 0) :
    0 < limitVariance q hFE.ℓ β := by
  have hd : deriv hFE.ℓ β ≠ 0 := by
    intro hd
    simpa [hd] using hFE.sign β hβ0
  change (0 : ℝ) < (q.factorial : ℝ) / 2 * β ^ 2 * (deriv hFE.ℓ β) ^ 2
  exact mul_pos
    (mul_pos (div_pos (Nat.cast_pos.mpr q.factorial_pos) (by norm_num))
      (sq_pos_of_ne_zero hβ0)) (sq_pos_of_ne_zero hd)

end SYK.CLT
