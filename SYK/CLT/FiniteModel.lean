import SYK.Model.GaussianDisorder
import SYK.Model.FiniteDimensionalGibbs
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Finite Gaussian Majorana models

Dimension-normalized partition functions, trace bounds, and Gaussian moments
for an arbitrary nonempty finite matrix Majorana representation. These results
use `Params` and `MajoranaSystem`, without an asymptotic family or annealed input.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal Matrix.Norms.Operator

namespace SYK.CLT

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

/-- Strict form of the trace-exponential bound for a nonzero traceless
Hermitian matrix. -/
private theorem trace_exp_re_gt_card {A : Matrix d d ℂ}
    (hA : A.IsHermitian) (htr : Matrix.trace A = 0) (hne : A ≠ 0) :
    (Fintype.card d : ℝ) < (Matrix.trace (NormedSpace.exp A)).re := by
  classical
  have hsum : (∑ i, hA.eigenvalues i) = 0 := by
    have ht := hA.trace_eq_sum_eigenvalues
    rw [htr] at ht
    have := congrArg Complex.re ht
    simpa using this.symm
  have hex : ∃ i : d, hA.eigenvalues i ≠ 0 := by
    by_contra h
    push Not at h
    apply hne ((hA.eigenvalues_eq_zero_iff).mp ?_)
    funext i
    exact h i
  rw [trace_exp_eq_sum hA]
  simp only [Complex.re_sum, Complex.ofReal_re]
  calc
    (Fintype.card d : ℝ) = ∑ _i : d, (1 : ℝ) := by simp
    _ = ∑ i, (hA.eigenvalues i + 1) := by
      rw [Finset.sum_add_distrib, hsum]
      simp
    _ < ∑ i, Real.exp (hA.eigenvalues i) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact Real.add_one_le_exp _
      · obtain ⟨i, hi⟩ := hex
        exact ⟨i, Finset.mem_univ i, Real.add_one_lt_exp hi⟩

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

/-- A single nonzero Gaussian coupling gives a nonzero Hamiltonian. -/
theorem normalizedHamiltonian_single_ne_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ))
    (s : InteractionIndex P.N P.q) :
    normalizedHamiltonian P M (WithLp.toLp 2 (Pi.single s (1 : ℝ))) ≠ 0 := by
  classical
  have hscale : couplingScale P ≠ 0 := by
    have hN : (0 : ℝ) < P.N := by
      exact_mod_cast lt_of_lt_of_le P.q_pos P.q_le_N
    have hs : 0 < couplingScale P ^ 2 := by
      rw [couplingScale_sq]
      positivity
    nlinarith
  have hM : M.interactionOperator s ≠ 0 := by
    intro h
    have hsq := M.interactionOperator_sq P.q_even s
    rw [h] at hsq
    have hh : (0 : Matrix d d ℂ) = 1 := by simpa only [zero_mul] using hsq
    exact (zero_ne_one : (0 : Matrix d d ℂ) ≠ 1) hh
  unfold normalizedHamiltonian hamiltonian
  simp [Pi.single_apply, hscale, hM]

/-- The Hamiltonian also has zero dimension-normalized trace. -/
theorem normalizedHamiltonian_normalizedTrace_eq_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g : CouplingSpace P.N P.q) :
    normalizedTrace (normalizedHamiltonian P M g) = 0 := by
  simp only [normalizedTrace, normalizedHamiltonian_trace_eq_zero, zero_div]

noncomputable def normalizedHamiltonianLinear (P : Params)
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

/-- The lower bound is strict when the Hamiltonian and inverse temperature
are nonzero. -/
theorem realPartitionFunction_gt_one_of_hamiltonian_ne_zero (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ) (hβ : β ≠ 0)
    (g : CouplingSpace P.N P.q)
    (hH : normalizedHamiltonian P M g ≠ 0) :
    1 < realPartitionFunction P M β g := by
  let A : Matrix d d ℂ := (β : ℂ) • -normalizedHamiltonian P M g
  have hA : A.IsHermitian := by
    change star A = A
    simp [A, normalizedHamiltonian_self_adjoint]
  have htr : Matrix.trace A = 0 := by
    simp [A, normalizedHamiltonian_trace_eq_zero P M g]
  have hAne : A ≠ 0 := by
    exact smul_ne_zero (by exact_mod_cast hβ) (neg_ne_zero.mpr hH)
  have h := trace_exp_re_gt_card hA htr hAne
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
  have hdiv : 1 < (Matrix.trace (NormedSpace.exp A)).re / (Fintype.card d : ℝ) :=
    (lt_div_iff₀ hd).mpr (by simpa using h)
  simpa [realPartitionFunction, partitionFunction, normalizedTrace,
    gibbsOperator, A, Complex.div_natCast_re] using hdiv

/-- A single interaction already makes the finite-size partition function
strictly larger than its value at zero coupling. -/
theorem realPartitionFunction_single_gt_one (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ) (hβ : β ≠ 0)
    (s : InteractionIndex P.N P.q) :
    1 < realPartitionFunction P M β
      (WithLp.toLp 2 (Pi.single s (1 : ℝ))) := by
  exact realPartitionFunction_gt_one_of_hamiltonian_ne_zero P M β hβ _
    (normalizedHamiltonian_single_ne_zero P M s)

@[simp]
theorem realPartitionFunction_zero_coupling (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ) :
    realPartitionFunction P M β 0 = 1 := by
  simp [realPartitionFunction, partitionFunction, normalizedTrace, gibbsOperator]

theorem exists_realPartitionFunction_exp_bound (P : Params)
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

theorem realPartitionFunction_continuous (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ) :
    Continuous (realPartitionFunction P M β) := by
  unfold realPartitionFunction partitionFunction normalizedTrace gibbsOperator
  have hH : Continuous (normalizedHamiltonian P M) := by
    convert (normalizedHamiltonianLinear P M).continuous using 1
    funext g
    rfl
  fun_prop

/-- Finite Gaussian models have the moments needed for these centerings. -/
theorem realPartitionFunction_moments (P : Params)
    (M : MajoranaSystem P.N (Matrix d d ℂ)) (β : ℝ) :
    MemLp (realPartitionFunction P M β) 2 (standardGaussianMeasure P.N P.q) ∧
      Integrable (fun g ↦ Real.log (realPartitionFunction P M β g))
        (standardGaussianMeasure P.N P.q) ∧
      0 < (∫ g, realPartitionFunction P M β g ∂standardGaussianMeasure P.N P.q) := by
  let μ := standardGaussianMeasure P.N P.q
  obtain ⟨C, hC, hbound⟩ :=
    exists_realPartitionFunction_exp_bound P M β
  have hcont : Continuous (realPartitionFunction P M β) := realPartitionFunction_continuous P M β
  have hsq : Integrable (fun g ↦ (realPartitionFunction P M β g) ^ 2) μ := by
    have hexp : Integrable (fun g : CouplingSpace P.N P.q ↦
        Real.exp ((2 * C) * ‖g‖)) μ :=
      GaussianConcentration.integrable_exp_mul_norm (2 * C)
    apply hexp.mono' (hcont.pow 2).aestronglyMeasurable
    filter_upwards [] with g
    have hZ0 : 0 ≤ realPartitionFunction P M β g :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (realPartitionFunction_ge_one P M β g)
    have hb : realPartitionFunction P M β g ≤ Real.exp (C * ‖g‖) := hbound g
    have hpow : (realPartitionFunction P M β g) ^ 2 ≤ Real.exp ((2 * C) * ‖g‖) := by
      calc
        _ ≤ (Real.exp (C * ‖g‖)) ^ 2 :=
          pow_le_pow_left₀ hZ0 hb 2
        _ = Real.exp ((2 * C) * ‖g‖) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
    simpa [Pi.pow_apply, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (realPartitionFunction P M β g))] using hpow
  have hlp : MemLp (realPartitionFunction P M β) 2 μ :=
    (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hsq
  have hnorm : Integrable (fun g : CouplingSpace P.N P.q ↦ ‖g‖) μ := by
    have hexp := GaussianConcentration.integrable_exp_mul_norm (ι := InteractionIndex P.N P.q) 1
    apply hexp.mono' (by fun_prop)
    filter_upwards [] with g
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), one_mul]
    linarith [Real.add_one_le_exp ‖g‖]
  have hlog : Integrable (fun g ↦ Real.log (realPartitionFunction P M β g)) μ := by
    apply (hnorm.const_mul C).mono'
      ((Real.measurable_log.comp hcont.measurable).aestronglyMeasurable)
    filter_upwards [] with g
    have hlog0 := Real.log_nonneg (realPartitionFunction_ge_one P M β g)
    have hlogC : Real.log (realPartitionFunction P M β g) ≤ C * ‖g‖ :=
      (Real.log_le_iff_le_exp
        (lt_of_lt_of_le zero_lt_one (realPartitionFunction_ge_one P M β g))).2
        (by exact hbound g)
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (mul_nonneg hC (norm_nonneg _))] using hlogC
  have hmean : 0 < (∫ g, realPartitionFunction P M β g ∂standardGaussianMeasure P.N P.q) := by
    have hZint : Integrable (realPartitionFunction P M β) μ := hlp.integrable (by norm_num)
    have hone : (1 : ℝ) ≤
        (∫ g, realPartitionFunction P M β g ∂standardGaussianMeasure P.N P.q) := by
      change (1 : ℝ) ≤ ∫ g, realPartitionFunction P M β g ∂μ
      calc
        (1 : ℝ) = ∫ _g, (1 : ℝ) ∂μ := by simp [μ]
        _ ≤ ∫ g, realPartitionFunction P M β g ∂μ :=
          integral_mono (integrable_const _) hZint (realPartitionFunction_ge_one P M β)
    linarith
  exact ⟨hlp, hlog, hmean⟩

end FiniteModel

end SYK.CLT
