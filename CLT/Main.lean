import SYK.Model.StandardRepresentation
import SYK.Model.GaussianDisorder
import SYK.Model.FiniteDimensionalGibbs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

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
The explicit annealed input is `AnnealedInput`, modeled on
`prop:annealed-free-energy` in the CLT manuscript. The CLT proof remains incomplete
while the Gaussian chaos and logarithmic-transfer arguments are unproved.
The almost-sure free-energy law of large numbers is outside this module's
present scope.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
open scoped Matrix.Norms.Operator

namespace SYK.CLT

local instance (N q : ℕ) : IsProbabilityMeasure (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
  infer_instance

/-! ## Finite models -/

section FiniteModel

variable {d : Type*} [Fintype d] [DecidableEq d]

private theorem trace_exp_eq_sum {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    Matrix.trace (NormedSpace.exp A) =
      ∑ i, (Real.exp (hA.eigenvalues i) : ℂ) := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)
  have hAeq : A = (U : Matrix d d ℂ) * D * star (U : Matrix d d ℂ) := by
    simpa only [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hUinv : (U : Matrix d d ℂ)⁻¹ = star (U : Matrix d d ℂ) :=
    Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self U)
  calc
    Matrix.trace (NormedSpace.exp A) =
        Matrix.trace (NormedSpace.exp ((U : Matrix d d ℂ) * D * (U : Matrix d d ℂ)⁻¹)) := by
          rw [hUinv, ← hAeq]
    _ = Matrix.trace ((U : Matrix d d ℂ) * NormedSpace.exp D * (U : Matrix d d ℂ)⁻¹) := by
          rw [Matrix.exp_conj _ _ Unitary.isUnit_coe]
    _ = Matrix.trace (NormedSpace.exp D) := by
          rw [hUinv, Matrix.trace_mul_comm, ← mul_assoc,
            Unitary.coe_star_mul_self, one_mul]
    _ = _ := by simp [D, Matrix.exp_diagonal, Matrix.trace_diagonal,
      ← Complex.exp_eq_exp_ℂ]

private theorem trace_exp_re_ge_card {A : Matrix d d ℂ}
    (hA : A.IsHermitian) (htr : Matrix.trace A = 0) :
    (Fintype.card d : ℝ) ≤ (Matrix.trace (NormedSpace.exp A)).re := by
  have hsum : (∑ i, hA.eigenvalues i) = 0 := by
    have ht := hA.trace_eq_sum_eigenvalues
    rw [htr] at ht
    have := congrArg Complex.re ht
    simpa using this.symm
  rw [trace_exp_eq_sum hA]
  simp only [Complex.re_sum, Complex.ofReal_re]
  calc
    (Fintype.card d : ℝ) = ∑ _i : d, (1 : ℝ) := by simp
    _ = ∑ i, (hA.eigenvalues i + 1) := by
      rw [Finset.sum_add_distrib, hsum]
      simp
    _ ≤ ∑ i, Real.exp (hA.eigenvalues i) := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.add_one_le_exp _

private theorem trace_exp_re_le_card_exp_norm {A : Matrix d d ℂ}
    (hA : A.IsHermitian) :
    (Matrix.trace (NormedSpace.exp A)).re ≤
      (Fintype.card d : ℝ) * Real.exp (‖A‖ * ‖(1 : Matrix d d ℂ)‖) := by
  rw [trace_exp_eq_sum hA]
  simp only [Complex.re_sum, Complex.ofReal_re]
  calc
    (∑ i, Real.exp (hA.eigenvalues i)) ≤
        ∑ _i : d, Real.exp (‖A‖ * ‖(1 : Matrix d d ℂ)‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Real.exp_le_exp.mpr
      have hmem := hA.eigenvalues_mem_spectrum_real i
      have hnorm := spectrum.norm_le_norm_mul_of_mem hmem
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)
    _ = (Fintype.card d : ℝ) * Real.exp (‖A‖ * ‖(1 : Matrix d d ℂ)‖) := by simp

/-- Every interaction of positive even degree has zero matrix trace in any
finite-dimensional Majorana representation. -/
theorem interactionOperator_trace_eq_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ))
    (s : InteractionIndex P.N P.q) :
    Matrix.trace (M.interactionOperator s) = 0 := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [s.2]; exact P.q_pos)
  have hanti := M.interactionOperator_mul_generator_of_mem P.q_even s i hi
  have hconj : M.ψ i * M.interactionOperator s * M.ψ i =
      -M.interactionOperator s := by
    rw [mul_assoc, hanti, mul_neg, ← mul_assoc, M.majorana_sq, one_mul]
  have hcycle : Matrix.trace (M.ψ i * M.interactionOperator s * M.ψ i) =
      Matrix.trace (M.interactionOperator s) := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, M.majorana_sq, one_mul]
  have htrace : Matrix.trace (M.interactionOperator s) =
      -Matrix.trace (M.interactionOperator s) := by
    calc
      _ = Matrix.trace (M.ψ i * M.interactionOperator s * M.ψ i) := hcycle.symm
      _ = Matrix.trace (-M.interactionOperator s) := congrArg Matrix.trace hconj
      _ = _ := Matrix.trace_neg _
  exact CharZero.eq_neg_self_iff.mp htrace

/-- The Gaussian Hamiltonian is trace zero for every coupling vector. -/
theorem normalizedHamiltonian_trace_eq_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g : CouplingSpace P.N P.q) :
    Matrix.trace (normalizedHamiltonian P M g) = 0 := by
  classical
  simp [normalizedHamiltonian, hamiltonian, Matrix.trace_sum,
    Matrix.trace_smul, interactionOperator_trace_eq_zero P M]

variable [Nonempty d]

/-- The Hamiltonian also has zero dimension-normalized trace. -/
theorem normalizedHamiltonian_normalizedTrace_eq_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g : CouplingSpace P.N P.q) :
    normalizedTrace (normalizedHamiltonian P M g) = 0 := by
  simp only [normalizedTrace, normalizedHamiltonian_trace_eq_zero, zero_div]

private noncomputable def normalizedHamiltonianLinear (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) :
    CouplingSpace P.N P.q →L[ℝ] Matrix d d ℂ :=
  ({ toFun := normalizedHamiltonian P M
     map_add' := normalizedHamiltonian_add P M
     map_smul' := normalizedHamiltonian_smul P M } :
      CouplingSpace P.N P.q →ₗ[ℝ] Matrix d d ℂ).toContinuousLinearMap

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

/-- Jensen's lower bound for the dimension-normalized SYK partition function. -/
theorem realPartitionFunction_ge_one (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ)
    (g : CouplingSpace P.N P.q) :
    1 ≤ realPartitionFunction P M β g := by
  let A : Matrix d d ℂ := (β : ℂ) • -normalizedHamiltonian P M g
  have hA : A.IsHermitian := by
    change star A = A
    simp [A, normalizedHamiltonian_self_adjoint]
  have htr : Matrix.trace A = 0 := by
    simp [A, normalizedHamiltonian_trace_eq_zero P M g]
  have h := trace_exp_re_ge_card hA htr
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
  have hdiv : 1 ≤ (Matrix.trace (NormedSpace.exp A)).re / (Fintype.card d : ℝ) :=
    (le_div_iff₀ hd).mpr (by simpa using h)
  simpa [realPartitionFunction, partitionFunction, normalizedTrace,
    gibbsOperator, A, Complex.div_natCast_re] using hdiv

private theorem exists_realPartitionFunction_exp_bound (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : CouplingSpace P.N P.q,
      realPartitionFunction P M β g ≤ Real.exp (C * ‖g‖) := by
  obtain ⟨C, hC, hbound⟩ := (normalizedHamiltonianLinear P M).bound
  let K := |β| * C * ‖(1 : Matrix d d ℂ)‖
  refine ⟨K, by positivity, ?_⟩
  intro g
  let A : Matrix d d ℂ := (β : ℂ) • -normalizedHamiltonian P M g
  have hA : A.IsHermitian := by
    change star A = A
    simp [A, normalizedHamiltonian_self_adjoint]
  have h := trace_exp_re_le_card_exp_norm hA
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
  have hZ : realPartitionFunction P M β g ≤
      Real.exp (‖A‖ * ‖(1 : Matrix d d ℂ)‖) := by
    have hdiv : (Matrix.trace (NormedSpace.exp A)).re / (Fintype.card d : ℝ) ≤
        Real.exp (‖A‖ * ‖(1 : Matrix d d ℂ)‖) := by
      apply (div_le_iff₀ hd).mpr
      simpa [mul_comm] using h
    simpa [realPartitionFunction, partitionFunction, normalizedTrace,
      gibbsOperator, A, Complex.div_natCast_re] using hdiv
  apply hZ.trans (Real.exp_le_exp.mpr ?_)
  have hlinear : ‖normalizedHamiltonian P M g‖ ≤ C * ‖g‖ := by
    convert hbound g using 1
    rfl
  calc
    ‖A‖ * ‖(1 : Matrix d d ℂ)‖ =
        |β| * ‖normalizedHamiltonian P M g‖ * ‖(1 : Matrix d d ℂ)‖ := by
          simp [A, norm_smul]
    _ ≤ |β| * (C * ‖g‖) * ‖(1 : Matrix d d ℂ)‖ := by gcongr
    _ = K * ‖g‖ := by ring

/-- Specializing the existing definition gives the trace normalization in
`subsec:SYK-model`; this does not assert representation independence. -/
theorem partitionFunction_standard (P : Params) (hN : Even P.N) (z : ℂ)
    (g : CouplingSpace P.N P.q) :
    partitionFunction P (standardMajoranaSystem P.N hN) z g =
      ((2 : ℂ) ^ (P.N / 2))⁻¹ *
        SYK.partitionFunction z
          (normalizedHamiltonian P (standardMajoranaSystem P.N hN) g) := by
  rw [partitionFunction_eq_trace_div_card, standardBasis_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_comm]

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

theorem Z_ge_one (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    1 ≤ S.Z β n g :=
  realPartitionFunction_ge_one (S.params n) (S.majorana n) β g

private theorem Z_continuous (β : ℝ) (n : ℕ) : Continuous (S.Z β n) := by
  unfold Z realPartitionFunction partitionFunction normalizedTrace gibbsOperator
  have hH : Continuous (normalizedHamiltonian (S.params n) (S.majorana n)) := by
    convert (normalizedHamiltonianLinear (S.params n) (S.majorana n)).continuous using 1
    funext g
    rfl
  fun_prop

theorem log_Z_nonneg (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    0 ≤ Real.log (S.Z β n g) :=
  Real.log_nonneg (S.Z_ge_one β n g)

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
  let μ := standardGaussianMeasure (S.N n) q
  obtain ⟨C, hC, hbound⟩ :=
    exists_realPartitionFunction_exp_bound (S.params n) (S.majorana n) β
  have hcont : Continuous (S.Z β n) := S.Z_continuous β n
  have hsq : Integrable (fun g ↦ (S.Z β n g) ^ 2) μ := by
    have hexp : Integrable (fun g : CouplingSpace (S.N n) q ↦
        Real.exp ((2 * C) * ‖g‖)) μ :=
      GaussianConcentration.integrable_exp_mul_norm (2 * C)
    apply hexp.mono' (hcont.pow 2).aestronglyMeasurable
    filter_upwards [] with g
    have hZ0 : 0 ≤ S.Z β n g :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (S.Z_ge_one β n g)
    have hb : S.Z β n g ≤ Real.exp (C * ‖g‖) := hbound g
    have hpow : (S.Z β n g) ^ 2 ≤ Real.exp ((2 * C) * ‖g‖) := by
      calc
        _ ≤ (Real.exp (C * ‖g‖)) ^ 2 :=
          pow_le_pow_left₀ hZ0 hb 2
        _ = Real.exp ((2 * C) * ‖g‖) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
    simpa [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S.Z β n g))] using hpow
  have hlp : MemLp (S.Z β n) 2 μ :=
    (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hsq
  have hnorm : Integrable (fun g : CouplingSpace (S.N n) q ↦ ‖g‖) μ := by
    have hexp := GaussianConcentration.integrable_exp_mul_norm (ι := InteractionIndex (S.N n) q) 1
    apply hexp.mono' (by fun_prop)
    filter_upwards [] with g
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), one_mul]
    linarith [Real.add_one_le_exp ‖g‖]
  have hlog : Integrable (fun g ↦ Real.log (S.Z β n g)) μ := by
    apply (hnorm.const_mul C).mono'
      ((Real.measurable_log.comp hcont.measurable).aestronglyMeasurable)
    filter_upwards [] with g
    have hlog0 := S.log_Z_nonneg β n g
    have hlogC : Real.log (S.Z β n g) ≤ C * ‖g‖ :=
      (Real.log_le_iff_le_exp (lt_of_lt_of_le (by norm_num) (S.Z_ge_one β n g))).2
        (by exact hbound g)
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (mul_nonneg hC (norm_nonneg _))] using hlogC
  have hmean : 0 < S.meanZ β n := by
    have hZint : Integrable (S.Z β n) μ := hlp.integrable (by norm_num)
    have hone : (1 : ℝ) ≤ S.meanZ β n := by
      change (1 : ℝ) ≤ ∫ g, S.Z β n g ∂μ
      calc
        (1 : ℝ) = ∫ _g, (1 : ℝ) ∂μ := by simp [μ]
        _ ≤ ∫ g, S.Z β n g ∂μ :=
          integral_mono (integrable_const _) hZint (S.Z_ge_one β n)
    linarith
  exact ⟨hlp, hlog, hmean⟩

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

/-- The normalization in `subsec:SYK-model` has expectation one. -/
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

/-- The two logarithmic centerings agree in `cor:free-energy-clt`. -/
theorem centered_log_Y_eq (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    Real.log (S.Y β n g) -
        (∫ x, Real.log (S.Y β n x) ∂standardGaussianMeasure (S.N n) q) =
      Real.log (S.Z β n g) - S.meanLogZ β n := by
  rw [S.log_Y_eq, S.integral_log_Y]
  ring

/-- Pointwise input for the small-event estimate in `cor:free-energy-clt`. -/
theorem neg_log_Y_le_log_meanZ (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    -Real.log (S.Y β n g) ≤ Real.log (S.meanZ β n) := by
  rw [S.log_Y_eq]
  linarith [S.log_Z_nonneg β n g]

end Setting

/-! ## Main results -/

/-- `prop:annealed-free-energy` for one Gaussian SYK model family.
The small-temperature expansions follow from the stated global error bounds. -/
structure AnnealedInput (q : ℕ) (S : Setting q) where
  ℓ : ℝ → ℝ
  even : ∀ β : ℝ, ℓ (-β) = ℓ β
  convex : ConvexOn ℝ Set.univ ℓ
  contDiff_one : ContDiff ℝ 1 ℓ
  pressure_limit : TendstoLocallyUniformlyOn
    (fun n β ↦ S.annealedFreeEnergy β n) ℓ atTop Set.univ
  derivative_limit : TendstoLocallyUniformlyOn
    (fun n β ↦ deriv (fun b ↦ Real.log (S.meanZ b n)) β / (S.N n : ℝ))
    (deriv ℓ) atTop Set.univ
  derivative_pos : ∀ β : ℝ, 0 < β → 0 < deriv ℓ β
  derivative_le : ∀ β : ℝ, 0 < β → deriv ℓ β ≤ β / (q : ℝ)
  derivative_error_nonneg : ∀ β : ℝ, 0 < β →
    0 ≤ β / (q : ℝ) - deriv ℓ β
  derivative_error_le : ∀ β : ℝ, 0 < β →
    β / (q : ℝ) - deriv ℓ β ≤ β ^ 3 / 3
  pressure_error_nonneg : ∀ β : ℝ,
    0 ≤ β ^ 2 / (2 * (q : ℝ)) - ℓ β
  pressure_error_le : ∀ β : ℝ,
    β ^ 2 / (2 * (q : ℝ)) - ℓ β ≤ β ^ 4 / 12
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
noncomputable def limitVariance (q : ℕ) (ℓ : ℝ → ℝ) (β : ℝ) : ℝ≥0 :=
  ⟨(q.factorial : ℝ) / 2 * β ^ 2 * (deriv ℓ β) ^ 2, by positivity⟩

/-- Proposition 4.2 gives the sign at every nonzero temperature. -/
theorem exists_small_temperature_sign {q : ℕ} {S : Setting q}
    (hFE : AnnealedInput q S) :
    ∃ r : ℝ, 0 < r ∧
      ∀ β : ℝ, |β| < r → β ≠ 0 → 0 < β * deriv hFE.ℓ β := by
  exact ⟨1, by norm_num, fun β _ hβ0 ↦ hFE.sign β hβ0⟩

/-- The limiting variance is positive at the small nonzero temperatures
selected by Proposition 4.2. -/
theorem exists_small_temperature_variance_pos {q : ℕ} {S : Setting q}
    (hFE : AnnealedInput q S) :
    ∃ r : ℝ, 0 < r ∧
      ∀ β : ℝ, |β| < r → β ≠ 0 → 0 < limitVariance q hFE.ℓ β := by
  obtain ⟨r, hr, hsign⟩ := exists_small_temperature_sign hFE
  refine ⟨r, hr, ?_⟩
  intro β hβ hβ0
  have hd : deriv hFE.ℓ β ≠ 0 := by
    intro hd
    simpa [hd] using hsign β hβ hβ0
  change (0 : ℝ) < (q.factorial : ℝ) / 2 * β ^ 2 * (deriv hFE.ℓ β) ^ 2
  exact mul_pos
    (mul_pos (div_pos (Nat.cast_pos.mpr q.factorial_pos) (by norm_num))
      (sq_pos_of_ne_zero hβ0)) (sq_pos_of_ne_zero hd)

/-- `thm:partition-clt` and `cor:free-energy-clt` for one matrix Majorana family.

The limit is the identity random variable on `ℝ` with law
`gaussianReal 0 (limitVariance q ℓ β)`. Thus the conclusion expresses weak
convergence of probability laws, including the Dirac law at zero variance.
The limiting function is the one supplied by the annealed proposition.
Positivity is a conclusion wherever standardization is used.

The proof placeholders cover the annealed input, Gaussian chaos estimates,
classical CLT, and transfer to the centered logarithm. -/
theorem partition_and_log_partition_clt (q : ℕ) (_hq : Even q) (_h4 : 4 ≤ q)
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        (β ≠ 0 →
          0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
          TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
            (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1)) := by
  sorry

/-- The partition-function part of `thm:partition-clt`. The joint theorem
above additionally supplies the standardized CLT at nonzero temperature. -/
theorem partition_clt (q : ℕ) (hq : Even q) (h4 : 4 ≤ q)
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        (β ≠ 0 →
          0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
          TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
            (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1)) := by
  obtain ⟨βq, hβq, h⟩ := partition_and_log_partition_clt q hq h4 S hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  exact ⟨(h β hβ).1, (h β hβ).2.1, (h β hβ).2.2.2⟩

/-- The centered log-partition CLT of `cor:free-energy-clt`.
The joint theorem supplies the same radius and variance for both CLTs. -/
theorem log_partition_clt (q : ℕ) (hq : Even q) (h4 : 4 ≤ q)
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) := by
  obtain ⟨βq, hβq, h⟩ := partition_and_log_partition_clt q hq h4 S hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  exact ⟨(h β hβ).1, (h β hβ).2.2.1⟩

end SYK.CLT
