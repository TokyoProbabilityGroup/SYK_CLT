import SYK.Probability.GaussianConcentration.Lipschitz
import SYK.Model.GaussianDisorder
import SYK.SuperConcentration.MajoranaBound

/-!
# Superconcentration of the SYK log-partition function

This public module uses the standard Hamiltonian from
`SYK.Model.GaussianDisorder` and proves its Lipschitz and Gaussian concentration
bounds in the standard Gaussian coordinates. Algebraic prerequisites live in
`SYK.SuperConcentration.MajoranaBound`; shared finite-dimensional Gibbs states and trace
calculus live in `SYK.Model.FiniteDimensionalGibbs`.
-/

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped MatrixOrder
open scoped Matrix.Norms.Operator
open MeasureTheory
open ProbabilityTheory

namespace SYK

open GaussianConcentration

/-- The real logarithm of the partition function. -/
noncomputable def logPartition
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (J : CouplingSpace P.N P.q) : ℝ :=
  Real.log
    (partitionFunction (β : ℂ)
      (normalizedHamiltonian P M J)).re

theorem hasDerivAt_logPartition_line
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (J V : CouplingSpace P.N P.q) (s : ℝ) :
    let Hs := normalizedHamiltonian P M (J + s • V)
    let Bs := -(β : ℂ) • normalizedHamiltonian P M V
    HasDerivAt (fun r : ℝ ↦ logPartition P β M (J + r • V))
      ((Matrix.trace (Bs * gibbsOperator (β : ℂ) Hs)).re /
        (partitionFunction (β : ℂ) Hs).re) s := by
  dsimp only
  let A : Matrix d d ℂ :=
    -(β : ℂ) • normalizedHamiltonian P M J
  let B : Matrix d d ℂ :=
    -(β : ℂ) • normalizedHamiltonian P M V
  have hexp (r : ℝ) :
      -(β : ℂ) •
          normalizedHamiltonian P M (J + r • V) =
        A + r • B := by
    rw [normalizedHamiltonian_affine]
    dsimp [A, B]
    module
  have hexp' (r : ℝ) :
      -((β : ℂ) •
          normalizedHamiltonian P M (J + r • V)) =
        A + r • B := by
    rw [← neg_smul]
    exact hexp r
  have htrace := hasDerivAt_trace_exp_affine A B s
  have hre := (hasDerivAt_const s Complex.reCLM).clm_apply htrace
  have hpos : 0 < (partitionFunction (β : ℂ)
      (normalizedHamiltonian P M (J + s • V))).re :=
    partitionFunction_pos β (normalizedHamiltonian_self_adjoint P M _)
  have hpos' : 0 < Complex.reCLM
      (Matrix.trace (NormedSpace.exp (A + s • B))) := by
    have h := hpos
    rw [partitionFunction, gibbsOperator, hexp s] at h
    simpa using h
  have hlog := hre.log (ne_of_gt hpos')
  convert hlog using 1
  · funext r
    simp only [logPartition, partitionFunction, gibbsOperator,
      Complex.reCLM_apply]
    rw [hexp r]
  · simp only [B, partitionFunction, gibbsOperator, Complex.reCLM_apply]
    rw [hexp s]
    simp [B, smul_smul, smul_neg]

/--
The finite-volume squared upper bound supplied by the
SYK sum-of-squares estimate.
-/
private noncomputable def exactLipschitzSq (P : Params) (β : NNReal) : ℝ :=
  ((β : ℝ) * couplingScale P) ^ 2 *
    ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ))

private theorem exactLipschitzSq_nonneg (P : Params) (β : NNReal) :
    0 ≤ exactLipschitzSq P β := by
  exact mul_nonneg (sq_nonneg _)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The simplified Lipschitz constant obtained from the finite-volume bound. -/
noncomputable def logPartitionLipschitzConstant
    (P : Params) (β : NNReal) : ℝ≥0 :=
  Real.toNNReal (|(β : ℝ)| / Real.sqrt (P.q : ℝ))

/--
The normalization constant absorbs the sum-of-squares SYK bound:
`couplingScale · √(C(N,q-1)/q) ≤ 1 / √q`.
-/
theorem couplingScale_mul_sqrt_choose_le
    (P : Params) :
    couplingScale P *
        Real.sqrt ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ)) ≤
      1 / Real.sqrt (P.q : ℝ) := by
  unfold couplingScale
  ring_nf
  norm_num
  suffices hfactorial :
      Real.sqrt ((P.q - 1).factorial * P.N.choose (P.q - 1)) ≤
        Real.sqrt (P.N ^ (P.q - 1)) by
    field_simp at *
    rw [div_le_div_iff₀]
    · rw [Real.sqrt_mul (by positivity)] at hfactorial
      nlinarith [show 0 ≤ Real.sqrt P.q by positivity]
    · exact mul_pos
        (Real.sqrt_pos.mpr
          (pow_pos (Nat.cast_pos.mpr (by linarith [P.q_pos, P.q_le_N])) _))
        (Real.sqrt_pos.mpr
          (Nat.cast_pos.mpr (by linarith [P.q_pos, P.q_le_N])))
    · exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr P.q_pos)
  refine Real.sqrt_le_sqrt ?_
  rw_mod_cast [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow _ _

/--
The finite-volume squared directional estimate, before simplifying the
binomial coefficient and normalization.
-/
theorem abs_beta_expectation_normHam_sq_le_exact
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ)
    (V : CouplingSpace P.N P.q) :
    |(β : ℝ) * (expectation ρ (normalizedHamiltonian P M V)).re| ^ 2
      ≤ (((β : ℝ) * couplingScale P) ^ 2 *
        ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ))) * ‖V‖ ^ 2 := by
  set c := couplingScale P
  set S := ∑ I : InteractionIndex P.N P.q,
    V I * (expectation ρ (M.interactionOperator I)).re
  set Q := (Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ)
  have hlinear' :
      (expectation ρ (normalizedHamiltonian P M V)).re =
        c * ∑ I : InteractionIndex P.N P.q,
          V I * (expectation ρ (M.interactionOperator I)).re := by
    classical
    unfold normalizedHamiltonian expectation
    simp only [hamiltonian]
    rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hlinear :
      (expectation ρ (normalizedHamiltonian P M V)).re = c * S := by
    simpa only [S] using hlinear'
  have hcs : S ^ 2 ≤
      (∑ I : InteractionIndex P.N P.q, V I ^ 2) *
        (∑ I : InteractionIndex P.N P.q,
          (expectation ρ (M.interactionOperator I)).re ^ 2) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hexpect :
      (∑ I : InteractionIndex P.N P.q,
          (expectation ρ (M.interactionOperator I)).re ^ 2) ≤ Q := by
    have h := syk_sum_sq_expectation_le P.q_pos P.q_even M ρ hρ
    refine le_trans ?_ h
    exact Finset.sum_le_sum fun i _ => by
      simp [Complex.normSq, Complex.sq_norm]
      nlinarith only
  have hdot : S ^ 2 ≤ ‖V‖ ^ 2 * Q := by
    have hsum_nonneg : 0 ≤ ∑ I : InteractionIndex P.N P.q, V I ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hexpect hsum_nonneg
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt hsum_nonneg]
    exact le_trans hcs hmul
  have hscaled := mul_le_mul_of_nonneg_left hdot (sq_nonneg ((β : ℝ) * c))
  rw [hlinear, sq_abs]
  dsimp only [c, Q] at hscaled ⊢
  nlinarith only [hscaled]

/-- The exact finite-volume directional bound in unsquared form. -/
private theorem abs_beta_expectation_normHam_le_exact
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ)
    (V : CouplingSpace P.N P.q) :
    |(β : ℝ) * (expectation ρ (normalizedHamiltonian P M V)).re|
      ≤ Real.sqrt (exactLipschitzSq P β) * ‖V‖ := by
  have hsq := abs_beta_expectation_normHam_sq_le_exact P β M ρ hρ V
  calc
    |(β : ℝ) * (expectation ρ (normalizedHamiltonian P M V)).re| =
        Real.sqrt
          (|(β : ℝ) * (expectation ρ (normalizedHamiltonian P M V)).re| ^ 2) := by
            rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (exactLipschitzSq P β * ‖V‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (exactLipschitzSq P β) * ‖V‖ := by
      rw [Real.sqrt_mul (exactLipschitzSq_nonneg P β), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg V)]

private theorem sqrt_exactLipschitzSq
    (P : Params) (β : NNReal) :
    Real.sqrt (exactLipschitzSq P β) =
      |(β : ℝ)| * couplingScale P *
        Real.sqrt ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ)) := by
  rw [exactLipschitzSq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_mul]
  have hscale : 0 ≤ couplingScale P := by
    exact couplingScale_nonneg P
  rw [abs_of_nonneg hscale]

/--
Cauchy–Schwarz combined with the SYK sum-of-squares bound controls the
directional gradient of the normalized SYK energy by the simplified constant.
-/
theorem abs_beta_expectation_normHam_le
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ)
    (V : CouplingSpace P.N P.q) :
    |(β : ℝ) * (expectation ρ (normalizedHamiltonian P M V)).re|
      ≤ (|(β : ℝ)| / Real.sqrt (P.q : ℝ)) * ‖V‖ := by
  refine le_trans (abs_beta_expectation_normHam_le_exact P β M ρ hρ V) ?_
  rw [sqrt_exactLipschitzSq P β]
  have hscale := mul_le_mul_of_nonneg_left
    (couplingScale_mul_sqrt_choose_le P) (abs_nonneg (β : ℝ))
  have := mul_le_mul_of_nonneg_right hscale (norm_nonneg V)
  convert this using 1 <;> ring

/--
The directional derivative of `logPartition` along `V`, expressed as a
thermal expectation of the (normalized) SYK energy.
-/
theorem logPartition_line_deriv_eq
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (J V : CouplingSpace P.N P.q) (s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ logPartition P β M (J + r • V))
      (-(β : ℝ) * (expectation
        (thermalDensity β
          (normalizedHamiltonian P M (J + s • V)))
        (normalizedHamiltonian P M V)).re) s := by
  convert hasDerivAt_logPartition_line P β M J V s using 1
  unfold expectation thermalDensity
  simp [Matrix.trace_smul]
  ring_nf
  rw [Matrix.trace_mul_comm]

/-- The SYK log-partition function is Lipschitz with the stated constant. -/
theorem logPartition_lipschitz
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ)) :
    LipschitzWith (logPartitionLipschitzConstant P β)
      (logPartition P β M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  set V : CouplingSpace P.N P.q := x - y
  set g : ℝ → ℝ := fun r => logPartition P β M (y + r • V)
  have hderiv (r : ℝ) :
      |deriv g r| ≤
        (|(β : ℝ)| / Real.sqrt (P.q : ℝ)) * ‖V‖ := by
    let ρ := thermalDensity β
      (normalizedHamiltonian P M (y + r • V))
    have hρ : IsDensityMatrix ρ :=
      thermalDensity_isDensityMatrix β
        (normalizedHamiltonian_self_adjoint P M _)
    have hbound := abs_beta_expectation_normHam_le P β M ρ hρ V
    have hderiv_eq :
        deriv g r =
          -(β : ℝ) * (expectation ρ (normalizedHamiltonian P M V)).re := by
      exact (logPartition_line_deriv_eq P β M y V r).deriv
    rw [hderiv_eq]
    simpa only [abs_mul, abs_neg] using hbound
  have hmvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1, g 1 - g 0 = deriv g c := by
    have hslope := exists_deriv_eq_slope g zero_lt_one
    have hcontinuous : ContinuousOn g (Set.Icc 0 1) :=
      continuousOn_of_forall_continuousAt fun r _ =>
        (logPartition_line_deriv_eq P β M y V r).differentiableAt.continuousAt
    have hdifferentiable : DifferentiableOn ℝ g (Set.Ioo 0 1) :=
      fun r _ =>
        (logPartition_line_deriv_eq P β M y V r).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope_eq⟩ := hslope hcontinuous hdifferentiable
    refine ⟨c, hc, ?_⟩
    norm_num at hslope_eq
    linarith
  obtain ⟨c, _hc, hslope⟩ := hmvt
  have hends :
      g 1 = logPartition P β M x ∧
        g 0 = logPartition P β M y := by
    constructor <;> simp [g, V]
  have hconstant_nonneg :
      0 ≤ |(β : ℝ)| / Real.sqrt (P.q : ℝ) := by
    positivity
  rw [dist_eq_norm, Real.norm_eq_abs, ← hends.1, ← hends.2, hslope]
  rw [logPartitionLipschitzConstant, Real.coe_toNNReal _ hconstant_nonneg]
  refine le_trans (hderiv c) ?_
  rw [dist_eq_norm]

/-- At zero inverse temperature the log-partition function is constant. -/
theorem logPartition_eq_log_card_of_beta_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (hβ : β = 0) (J : CouplingSpace P.N P.q) :
    logPartition P β M J = Real.log (Fintype.card d : ℝ) := by
  simp [logPartition, hβ]

/-- At zero inverse temperature every positive-deviation tail event is empty. -/
theorem logPartition_tail_of_beta_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (hβ : β = 0) (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P β M J -
          ∫ K, logPartition P β M K
            ∂standardGaussianMeasure P.N P.q| > t} = 0 := by
  let a : ℝ := Real.log (Fintype.card d : ℝ)
  have hconst : ∀ J : CouplingSpace P.N P.q, logPartition P β M J = a :=
    fun J => logPartition_eq_log_card_of_beta_zero P β M hβ J
  have hintegral :
      ∫ K, logPartition P β M K ∂standardGaussianMeasure P.N P.q = a := by
    simp only [hconst]
    simp
  have hset :
      {J : CouplingSpace P.N P.q | |logPartition P β M J -
          ∫ K, logPartition P β M K
            ∂standardGaussianMeasure P.N P.q| > t} = ∅ := by
    ext J
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [hconst J, hintegral]
    simpa using ht.le
  rw [hset]
  simp

/-- The common Lipschitz constant and exponent identity for the three Gaussian tails. -/
private theorem logPartition_tail_parameters
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (hβ : (β : ℝ) ≠ 0) :
    let L : ℝ := |(β : ℝ)| / Real.sqrt (P.q : ℝ)
    0 < L ∧ LipschitzWith L.toNNReal (logPartition P β M) ∧
      ∀ t : ℝ, -t ^ 2 / (2 * L ^ 2) =
        -(P.q : ℝ) * t ^ 2 / (2 * (β : ℝ) ^ 2) := by
  have hq : 0 < (P.q : ℝ) := by exact_mod_cast P.q_pos
  have hsqrt : 0 < Real.sqrt (P.q : ℝ) := Real.sqrt_pos.2 hq
  refine ⟨div_pos (abs_pos.mpr hβ) hsqrt, logPartition_lipschitz P β M, ?_⟩
  intro t
  have hq0 : (P.q : ℝ) ≠ 0 := ne_of_gt hq
  have hβ0 : (β : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  rw [div_pow, sq_abs, Real.sq_sqrt hq.le]
  field_simp

/--
The upper-tail concentration estimate for the product standard Gaussian
coupling measure, with the SYK Lipschitz bound proved internally.
-/
theorem logPartition_upper_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (hβ : (β : ℝ) ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | logPartition P β M J -
          ∫ K, logPartition P β M K
            ∂standardGaussianMeasure P.N P.q > t} ≤
      ENNReal.ofReal
        (Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * (β : ℝ) ^ 2))) := by
  let L : ℝ := |(β : ℝ)| / Real.sqrt (P.q : ℝ)
  obtain ⟨hL, hLip, hexponent⟩ := logPartition_tail_parameters P β M hβ
  have htail :=
    product_standardGaussian_upper_tail
      (ι := InteractionIndex P.N P.q) (logPartition P β M) L t hL ht hLip
  rwa [hexponent t] at htail

/--
The lower-tail concentration estimate for the product standard Gaussian
coupling measure, with the SYK Lipschitz bound proved internally.
-/
theorem logPartition_lower_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (hβ : (β : ℝ) ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | (∫ K, logPartition P β M K
            ∂standardGaussianMeasure P.N P.q) - logPartition P β M J > t} ≤
      ENNReal.ofReal
        (Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * (β : ℝ) ^ 2))) := by
  let L : ℝ := |(β : ℝ)| / Real.sqrt (P.q : ℝ)
  obtain ⟨hL, hLip, hexponent⟩ := logPartition_tail_parameters P β M hβ
  have htail :=
    product_standardGaussian_lower_tail
      (ι := InteractionIndex P.N P.q) (logPartition P β M) L t hL ht hLip
  rwa [hexponent t] at htail

/--
The two-sided superconcentration estimate for the product standard Gaussian
coupling measure, with the SYK Lipschitz bound proved internally.
-/
theorem logPartition_two_sided_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (hβ : (β : ℝ) ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P β M J -
          ∫ K, logPartition P β M K
            ∂standardGaussianMeasure P.N P.q| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * (β : ℝ) ^ 2))) := by
  let L : ℝ := |(β : ℝ)| / Real.sqrt (P.q : ℝ)
  obtain ⟨hL, hLip, hexponent⟩ := logPartition_tail_parameters P β M hβ
  have htail :=
    euclidean_lipschitz_gaussian_concentration
      (ι := InteractionIndex P.N P.q) (logPartition P β M) L t hL ht hLip
  rwa [hexponent t] at htail

/-- Sub-Gaussian MGF with parameter β²/q, including β = 0. -/
theorem logPartition_hasSubgaussianMGF
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ)) :
    HasSubgaussianMGF
      (fun J => logPartition P β M J -
        ∫ K, logPartition P β M K ∂standardGaussianMeasure P.N P.q)
      (Real.toNNReal ((β : ℝ) ^ 2 / (P.q : ℝ)))
      (standardGaussianMeasure P.N P.q) := by
  have hsq : (|(β : ℝ)| / Real.sqrt (P.q : ℝ)) ^ 2 =
      (β : ℝ) ^ 2 / (P.q : ℝ) := by
    rw [div_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h := product_standardGaussian_hasSubgaussianMGF
    (logPartition P β M) (|(β : ℝ)| / Real.sqrt (P.q : ℝ))
    (by positivity) (logPartition_lipschitz P β M)
  simpa only [standardGaussianMeasure_eq_onEuclidean, hsq] using h

/-- At β = 0 the centered log-partition function vanishes pointwise. -/
theorem logPartition_centered_of_beta_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (β : NNReal) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (hβ : β = 0) (J : CouplingSpace P.N P.q) :
    logPartition P β M J -
      ∫ K, logPartition P β M K ∂standardGaussianMeasure P.N P.q = 0 := by
  simp only [logPartition_eq_log_card_of_beta_zero P β M hβ]
  simp

end SYK
