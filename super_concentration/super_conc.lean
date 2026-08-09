import SYK.super_concentration.Gaussian_concentration.gaussian_concentration
import SYK.super_concentration.gibbs

/-!
# Superconcentration of the SYK log-partition function

This public module defines the normalized Hamiltonian and proves its
Lipschitz and Gaussian concentration bounds. Algebraic prerequisites live in
`SYK.super_concentration.core`; Gibbs and trace calculus live in
`SYK.super_concentration.gibbs`.
-/

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped MatrixOrder
open scoped Matrix.Norms.Operator
open MeasureTheory
open ProbabilityTheory

namespace SYK

/-- The normalization multiplying each Gaussian coupling. -/
noncomputable def couplingScale (P : Params) (𝒥 : ℝ) : ℝ :=
  𝒥 * Real.sqrt ((P.q - 1).factorial / (P.N : ℝ) ^ (P.q - 1))

/-- The normalized SYK Hamiltonian. -/
noncomputable def normalizedHamiltonian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) : Matrix d d ℂ :=
  hamiltonian P M (fun I => couplingScale P 𝒥 * J I)

/-- The real logarithm of the real part of the partition function. -/
noncomputable def logPartition
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) : ℝ :=
  Real.log
    (partitionFunction P.inverseTemperature
      (normalizedHamiltonian P M 𝒥 J)).re

private theorem normalizedHamiltonian_affine
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J V : CouplingSpace P.N P.q) (s : ℝ) :
    normalizedHamiltonian P M 𝒥 (J + s • V) =
      normalizedHamiltonian P M 𝒥 J +
        s • normalizedHamiltonian P M 𝒥 V := by
  classical
  simp only [normalizedHamiltonian, hamiltonian]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _hI
  change (((couplingScale P 𝒥 * (J I + s * V I) : ℝ) : ℂ) * phase P.q) •
      M.psiProduct I =
    ((((couplingScale P 𝒥 * J I : ℝ) : ℂ) * phase P.q) • M.psiProduct I) +
      s • ((((couplingScale P 𝒥 * V I : ℝ) : ℂ) * phase P.q) • M.psiProduct I)
  rw [← smul_assoc, ← add_smul]
  congr 1
  rw [Complex.real_smul]
  push_cast
  ring

private theorem normalizedHamiltonian_self_adjoint
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) :
    star (normalizedHamiltonian P M 𝒥 J) =
      normalizedHamiltonian P M 𝒥 J := by
  exact hamiltonian_self_adjoint P M _

private theorem hasDerivAt_logPartition_line
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J V : CouplingSpace P.N P.q) (s : ℝ) :
    let Hs := normalizedHamiltonian P M 𝒥 (J + s • V)
    let Bs := -((P.β : ℂ)) • normalizedHamiltonian P M 𝒥 V
    HasDerivAt (fun r : ℝ ↦ logPartition P M 𝒥 (J + r • V))
      ((Matrix.trace (Bs * gibbsOperator P.inverseTemperature Hs)).re /
        (partitionFunction P.inverseTemperature Hs).re) s := by
  dsimp only
  let A : Matrix d d ℂ :=
    -((P.β : ℂ)) • normalizedHamiltonian P M 𝒥 J
  let B : Matrix d d ℂ :=
    -((P.β : ℂ)) • normalizedHamiltonian P M 𝒥 V
  have hexp (r : ℝ) :
      -(((P.inverseTemperature : ℝ) : ℂ)) •
          normalizedHamiltonian P M 𝒥 (J + r • V) =
        A + r • B := by
    rw [P.coe_inverseTemperature, normalizedHamiltonian_affine]
    dsimp [A, B]
    module
  have hexp' (r : ℝ) :
      -((((P.inverseTemperature : ℝ) : ℂ)) •
          normalizedHamiltonian P M 𝒥 (J + r • V)) =
        A + r • B := by
    rw [← neg_smul]
    exact hexp r
  have htrace := hasDerivAt_trace_exp_affine A B s
  have hre := (hasDerivAt_const s Complex.reCLM).clm_apply htrace
  have hpos : 0 < (partitionFunction P.inverseTemperature
      (normalizedHamiltonian P M 𝒥 (J + s • V))).re :=
    partitionFunction_pos _ (normalizedHamiltonian_self_adjoint P M 𝒥 _)
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
The directional derivative of `logPartition` along `V`, expressed as a
thermal expectation of the (normalized) SYK energy.
-/
private theorem logPartition_line_deriv_eq
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J V : CouplingSpace P.N P.q) (s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ logPartition P M 𝒥 (J + r • V))
      (-P.β * (expectation
        (thermalDensity P.inverseTemperature
          (normalizedHamiltonian P M 𝒥 (J + s • V)))
        (normalizedHamiltonian P M 𝒥 V)).re) s := by
  convert hasDerivAt_logPartition_line P M 𝒥 J V s using 1;
  unfold expectation thermalDensity; simp +decide [ Matrix.trace_smul ] ; ring_nf;
  rw [ Matrix.trace_mul_comm ]

/-!
## Sharp finite-volume reduction

The following declarations isolate the only model-specific input needed for the
sharp bound: a uniform estimate on the squared Majorana moments of the thermal
state.  In particular, this section does not replace that estimate by the
weaker arbitrary-density-matrix bound `syk_sum_sq_expectation_le`.
-/

/-- The exact squared Lipschitz scale resulting from a Majorana moment bound
`sum_I |m_I|^2 <= C * N^(q/2)`. -/
noncomputable def superConcentrationScale
    (P : Params) (coupling C : ℝ) : ℝ≥0 :=
  Real.toNNReal
    ((P.β * couplingScale P coupling) ^ 2 * C *
      (P.N : ℝ) ^ (P.q / 2))

private theorem coe_superConcentrationScale
    (P : Params) (coupling C : ℝ) (hC : 0 ≤ C) :
    (superConcentrationScale P coupling C : ℝ) =
      (P.β * couplingScale P coupling) ^ 2 * C *
        (P.N : ℝ) ^ (P.q / 2) := by
  rw [superConcentrationScale, Real.coe_toNNReal]
  positivity

/-- A squared directional estimate obtained from a supplied Majorana moment
bound.  The density matrix may depend on the base coupling; the hypothesis is
kept pointwise so that only a thermal-state estimate can be supplied later. -/
private theorem abs_beta_expectation_normHam_sq_le_superConcentration
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (coupling C : ℝ) (hC : 0 ≤ C)
    (ρ : Matrix d d ℂ) (_hρ : IsDensityMatrix ρ)
    (hMoment :
      ∑ I : InteractionIndex P.N P.q,
          ‖expectation ρ (M.interactionOperator I)‖ ^ 2 ≤
        C * (P.N : ℝ) ^ (P.q / 2))
    (V : CouplingSpace P.N P.q) :
    |P.β * (expectation ρ (normalizedHamiltonian P M coupling V)).re| ^ 2 ≤
      (superConcentrationScale P coupling C : ℝ) * ‖V‖ ^ 2 := by
  set c := couplingScale P coupling
  set S := ∑ I : InteractionIndex P.N P.q,
    V I * (expectation ρ (M.interactionOperator I)).re
  have hlinear' :
      (expectation ρ (normalizedHamiltonian P M coupling V)).re =
        c * ∑ I : InteractionIndex P.N P.q,
          V I * (expectation ρ (M.interactionOperator I)).re := by
    unfold normalizedHamiltonian expectation
    simp +decide [hamiltonian, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _]
    simp +decide [phase, MajoranaSystem.interactionOperator]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hlinear :
      (expectation ρ (normalizedHamiltonian P M coupling V)).re = c * S := by
    simpa only [S] using hlinear'
  have hcs : S ^ 2 ≤
      (∑ I : InteractionIndex P.N P.q, V I ^ 2) *
        (∑ I : InteractionIndex P.N P.q,
          (expectation ρ (M.interactionOperator I)).re ^ 2) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hreMoment :
      (∑ I : InteractionIndex P.N P.q,
          (expectation ρ (M.interactionOperator I)).re ^ 2) ≤
        C * (P.N : ℝ) ^ (P.q / 2) := by
    refine le_trans ?_ hMoment
    exact Finset.sum_le_sum fun i _ => by
      simp +decide [Complex.normSq, Complex.sq_norm]
      nlinarith only
  have hsum_nonneg : 0 ≤ ∑ I : InteractionIndex P.N P.q, V I ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdot :
      S ^ 2 ≤ ‖V‖ ^ 2 * (C * (P.N : ℝ) ^ (P.q / 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hreMoment hsum_nonneg
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt hsum_nonneg]
    exact le_trans hcs hmul
  have hscaled := mul_le_mul_of_nonneg_left hdot (sq_nonneg (P.β * c))
  rw [hlinear, sq_abs, coe_superConcentrationScale P coupling C hC]
  nlinarith only [hscaled]

/-- The sharp Lipschitz estimate, conditional only on the uniform thermal
Majorana moment estimate singled out in the blueprint. -/
private theorem logPartition_lipschitz_superConcentration
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (coupling C : ℝ) (hC : 0 ≤ C)
    (hMoment : ∀ J : CouplingSpace P.N P.q,
      ∑ I : InteractionIndex P.N P.q,
          ‖expectation
            (thermalDensity P.inverseTemperature
              (normalizedHamiltonian P M coupling J))
            (M.interactionOperator I)‖ ^ 2 ≤
        C * (P.N : ℝ) ^ (P.q / 2)) :
    LipschitzWith (superConcentrationScale P coupling C).sqrt
      (logPartition P M coupling) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  set V : CouplingSpace P.N P.q := x - y
  set f : ℝ → ℝ := fun r => logPartition P M coupling (y + r • V)
  have hderiv (r : ℝ) :
      |deriv f r| ≤
        Real.sqrt (superConcentrationScale P coupling C : ℝ) * ‖V‖ := by
    have hρ := thermalDensity_isDensityMatrix P.inverseTemperature
      (normalizedHamiltonian_self_adjoint P M coupling (y + r • V))
    have hsq := abs_beta_expectation_normHam_sq_le_superConcentration
      P M coupling C hC _ hρ (hMoment (y + r • V)) V
    have hderivEq : deriv f r =
        -P.β * (expectation
          (thermalDensity P.inverseTemperature
            (normalizedHamiltonian P M coupling (y + r • V)))
          (normalizedHamiltonian P M coupling V)).re := by
      exact (logPartition_line_deriv_eq P M coupling y V r).deriv
    rw [hderivEq]
    calc
      |-P.β *
          (expectation
            (thermalDensity P.inverseTemperature
              (normalizedHamiltonian P M coupling (y + r • V)))
            (normalizedHamiltonian P M coupling V)).re| =
          Real.sqrt
            (|P.β *
              (expectation
                (thermalDensity P.inverseTemperature
                  (normalizedHamiltonian P M coupling (y + r • V)))
                (normalizedHamiltonian P M coupling V)).re| ^ 2) := by
            rw [show -P.β *
                (expectation
                  (thermalDensity P.inverseTemperature
                    (normalizedHamiltonian P M coupling (y + r • V)))
                  (normalizedHamiltonian P M coupling V)).re =
              -(P.β *
                (expectation
                  (thermalDensity P.inverseTemperature
                    (normalizedHamiltonian P M coupling (y + r • V)))
                  (normalizedHamiltonian P M coupling V)).re) by ring,
              abs_neg, Real.sqrt_sq (abs_nonneg _)]
      _ ≤ Real.sqrt
          ((superConcentrationScale P coupling C : ℝ) * ‖V‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (superConcentrationScale P coupling C : ℝ) * ‖V‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
          abs_of_nonneg (norm_nonneg V)]
  have hmvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1, f 1 - f 0 = deriv f c := by
    have h := exists_deriv_eq_slope f zero_lt_one
    exact h
      (continuousOn_of_forall_continuousAt fun r _ =>
        (logPartition_line_deriv_eq P M coupling y V r).differentiableAt.continuousAt)
      (fun r _ =>
        (logPartition_line_deriv_eq P M coupling y V r).differentiableAt.differentiableWithinAt)
      |> fun ⟨c, hc₁, hc₂⟩ => ⟨c, hc₁, by norm_num at hc₂; linarith⟩
  obtain ⟨c, _hc, hslope⟩ := hmvt
  have hends : f 1 = logPartition P M coupling x ∧
      f 0 = logPartition P M coupling y := by
    constructor <;> simp [f, V]
  rw [dist_eq_norm, Real.norm_eq_abs, ← hends.1, ← hends.2, hslope]
  rw [Real.coe_sqrt]
  refine le_trans (hderiv c) ?_
  rw [dist_eq_norm]

/-- For an empty state space the log-partition function is identically zero. -/
private theorem logPartition_eq_zero_of_isEmpty
    {d : Type*} [Fintype d] [DecidableEq d] [IsEmpty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) :
    logPartition P M 𝒥 J = 0 := by
  unfold logPartition; simp +decide [ partitionFunction ] ;

/-- The two-sided Gaussian tail estimate at any scale dominating the exact
finite-volume Majorana moment bound. -/
private theorem logPartition_two_sided_tail_standardGaussian_of_core_bound
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 C : ℝ)
    (hCbound : (Nat.choose P.N (P.q - 1) : ℝ) / P.q ≤
      C * (P.N : ℝ) ^ (P.q / 2))
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P M 𝒥 J -
          ∫ K, logPartition P M 𝒥 K
            ∂standardGaussianMeasure P.N P.q| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-t ^ 2 /
            (2 * (superConcentrationScale P 𝒥 C : ℝ)))) := by
  rcases isEmpty_or_nonempty d with hd | hd
  · have hconst : ∀ K : CouplingSpace P.N P.q,
        logPartition P M 𝒥 K = 0 :=
      fun K => logPartition_eq_zero_of_isEmpty P M 𝒥 K
    have hset :
        {J : CouplingSpace P.N P.q | |logPartition P M 𝒥 J -
            ∫ K, logPartition P M 𝒥 K
              ∂standardGaussianMeasure P.N P.q| > t} = ∅ := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_lt]
      simp only [hconst, integral_zero, sub_zero, abs_zero]
      exact ht.le
    rw [hset]
    simp
  · have hMoment (J : CouplingSpace P.N P.q) :
        ∑ I : InteractionIndex P.N P.q,
            ‖expectation
              (thermalDensity P.inverseTemperature
                (normalizedHamiltonian P M 𝒥 J))
              (M.interactionOperator I)‖ ^ 2 ≤
          C * (P.N : ℝ) ^ (P.q / 2) := by
      have hρ := thermalDensity_isDensityMatrix P.inverseTemperature
        (normalizedHamiltonian_self_adjoint P M 𝒥 J)
      exact le_trans
        (syk_sum_sq_expectation_le P.q_pos P.q_even M _ hρ) hCbound
    have hN : 0 < (P.N : ℝ) := by
      exact_mod_cast lt_of_lt_of_le P.q_pos P.q_le_N
    have hNpow : 0 < (P.N : ℝ) ^ (P.q / 2) := pow_pos hN _
    have hC : 0 ≤ C := by
      have hbound := hMoment 0
      have hsum : 0 ≤ ∑ I : InteractionIndex P.N P.q,
          ‖expectation
            (thermalDensity P.inverseTemperature
              (normalizedHamiltonian P M 𝒥 0))
            (M.interactionOperator I)‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hprod : 0 ≤ C * (P.N : ℝ) ^ (P.q / 2) :=
        le_trans hsum hbound
      nlinarith
    have hLipNN :=
      logPartition_lipschitz_superConcentration P M 𝒥 C hC hMoment
    by_cases hscaleZero : superConcentrationScale P 𝒥 C = 0
    · have hLipZero : LipschitzWith 0 (logPartition P M 𝒥) := by
        simpa [hscaleZero] using hLipNN
      have hconst : ∀ J K : CouplingSpace P.N P.q,
          logPartition P M 𝒥 J = logPartition P M 𝒥 K :=
        (LipschitzWith.zero_iff (logPartition P M 𝒥)).mp hLipZero
      have hintegral :
          ∫ K, logPartition P M 𝒥 K
              ∂standardGaussianMeasure P.N P.q =
            logPartition P M 𝒥 0 := by
        simp only [hconst _ 0]
        simp
      have hset :
          {J : CouplingSpace P.N P.q | |logPartition P M 𝒥 J -
              ∫ K, logPartition P M 𝒥 K
                ∂standardGaussianMeasure P.N P.q| > t} = ∅ := by
        ext J
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_lt]
        rw [hconst J 0, hintegral, sub_self, abs_zero]
        exact ht.le
      rw [hset]
      simp
    · have hscale : 0 < (superConcentrationScale P 𝒥 C : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hscaleZero)
      have hsqrt :
          0 < Real.sqrt (superConcentrationScale P 𝒥 C : ℝ) :=
        Real.sqrt_pos.2 hscale
      have hLip : LipschitzWith
          (Real.sqrt (superConcentrationScale P 𝒥 C : ℝ)).toNNReal
          (logPartition P M 𝒥) := by
        have hsqrtCoe :
            (Real.sqrt (superConcentrationScale P 𝒥 C : ℝ)).toNNReal =
              (superConcentrationScale P 𝒥 C).sqrt := by
          apply NNReal.eq
          simp [hsqrt.le]
        rw [hsqrtCoe]
        exact hLipNN
      have htail := gaussian_lipschitz_concentration P.N P.q
        (logPartition P M 𝒥)
        (Real.sqrt (superConcentrationScale P 𝒥 C : ℝ)) t
        hsqrt ht hLip
      rwa [Real.sq_sqrt hscale.le] at htail

/-- There is a finite-volume scale for which the sharp two-sided Gaussian
tail estimate holds at every positive deviation level. -/
theorem logPartition_two_sided_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      standardGaussianMeasure P.N P.q
          {J | |logPartition P M 𝒥 J -
            ∫ K, logPartition P M 𝒥 K
              ∂standardGaussianMeasure P.N P.q| > t} ≤
        ENNReal.ofReal
          (2 * Real.exp
            (-t ^ 2 /
              (2 * (superConcentrationScale P 𝒥 C : ℝ)))) := by
  let Q : ℝ := (Nat.choose P.N (P.q - 1) : ℝ) / P.q
  let R : ℝ := (P.N : ℝ) ^ (P.q / 2)
  have hN : 0 < (P.N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le P.q_pos P.q_le_N
  have hR : 0 < R := by
    exact pow_pos hN _
  let C : ℝ := Q / R
  refine ⟨C, ?_⟩
  intro t ht
  apply logPartition_two_sided_tail_standardGaussian_of_core_bound
    P M 𝒥 C
  · change Q ≤ C * R
    have hcancel : Q / R * R = Q := by
      field_simp
    dsimp [C]
    exact hcancel.ge
  · exact ht

end SYK
