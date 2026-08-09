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

theorem normalizedHamiltonian_affine
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

theorem normalizedHamiltonian_self_adjoint
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) :
    star (normalizedHamiltonian P M 𝒥 J) =
      normalizedHamiltonian P M 𝒥 J := by
  exact hamiltonian_self_adjoint P M _

theorem hasDerivAt_logPartition_line
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
The square of the exact finite-volume Lipschitz constant supplied by the
SYK sum-of-squares estimate.
-/
noncomputable def exactLipschitzSq (P : Params) (𝒥 : ℝ) : ℝ :=
  (P.β * couplingScale P 𝒥) ^ 2 *
    ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ))

theorem exactLipschitzSq_nonneg (P : Params) (𝒥 : ℝ) :
    0 ≤ exactLipschitzSq P 𝒥 := by
  exact mul_nonneg (sq_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The simplified Lipschitz constant obtained from the finite-volume bound. -/
noncomputable def simpleLipschitzConstant (P : Params) (𝒥 : ℝ) : ℝ≥0 :=
  Real.toNNReal (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ))

/--
The two-sided superconcentration estimate for the product standard Gaussian
coupling measure. The SYK gradient estimate is supplied in the reusable
`hLip` hypothesis.
-/
theorem logPartition_two_sided_tail
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
    (hLip : LipschitzWith (simpleLipschitzConstant P 𝒥)
      (logPartition P M 𝒥))
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P M 𝒥 J -
          ∫ K, logPartition P M 𝒥 K
            ∂standardGaussianMeasure P.N P.q| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2))) := by
  have hq : 0 < (P.q : ℝ) := by exact_mod_cast P.q_pos
  have hsqrt : 0 < Real.sqrt (P.q : ℝ) := Real.sqrt_pos.2 hq
  let L : ℝ := |P.β| * 𝒥 / Real.sqrt (P.q : ℝ)
  have hL : 0 < L := div_pos (mul_pos (abs_pos.mpr hβ) h𝒥) hsqrt
  have hLip' : LipschitzWith L.toNNReal (logPartition P M 𝒥) := by
    simpa [L, simpleLipschitzConstant] using hLip
  have htail :=
    gaussian_lipschitz_concentration P.N P.q
      (logPartition P M 𝒥) L t hL ht hLip'
  have hq0 : (P.q : ℝ) ≠ 0 := ne_of_gt hq
  have hsqrt0 : Real.sqrt (P.q : ℝ) ≠ 0 := ne_of_gt hsqrt
  have hβ0 : P.β ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  have h𝒥0 : 𝒥 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h𝒥)
  have hsqrt_sq : Real.sqrt (P.q : ℝ) ^ 2 = (P.q : ℝ) :=
    Real.sq_sqrt hq.le
  have hLsq : L ^ 2 = P.β ^ 2 * 𝒥 ^ 2 / (P.q : ℝ) := by
    dsimp [L]
    rw [div_pow, mul_pow, sq_abs, hsqrt_sq]
  have hexponent :
      -t ^ 2 / (2 * L ^ 2) =
        -(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2) := by
    rw [hLsq]
    field_simp
  rwa [hexponent] at htail

/--
The normalization constant absorbs the sum-of-squares SYK bound:
`couplingScale · √(C(N,q-1)/q) ≤ 𝒥 / √q`.
-/
theorem couplingScale_mul_sqrt_choose_le
    (P : Params) (𝒥 : ℝ) (h𝒥 : 0 ≤ 𝒥) :
    couplingScale P 𝒥 *
        Real.sqrt ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ)) ≤
      𝒥 / Real.sqrt (P.q : ℝ) := by
  unfold couplingScale; ring_nf; norm_num [ h𝒥 ] ;
  -- Cancel out the common terms $\mathcal{J}$ and $\sqrt{q}$ from both sides.
  suffices h_suff : Real.sqrt ((P.q - 1).factorial * (P.N.choose (P.q - 1))) ≤ Real.sqrt (P.N ^ (P.q - 1)) by
    field_simp at *;
    rw [ div_le_div_iff₀ ];
    · rw [ Real.sqrt_mul <| by positivity ] at h_suff ; nlinarith [ show 0 ≤ 𝒥 * Real.sqrt P.q by positivity ];
    · exact mul_pos ( Real.sqrt_pos.mpr ( pow_pos ( Nat.cast_pos.mpr ( by linarith [ P.q_pos, P.q_le_N ] ) ) _ ) ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith [ P.q_pos, P.q_le_N ] ) ) );
    · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr P.q_pos );
  refine Real.sqrt_le_sqrt ?_;
  rw_mod_cast [ ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow _ _;

/--
The exact finite-volume squared directional estimate, before simplifying the
binomial coefficient and normalization.
-/
theorem abs_beta_expectation_normHam_sq_le_exact
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ)
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ)
    (V : CouplingSpace P.N P.q) :
    |P.β * (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re| ^ 2
      ≤ exactLipschitzSq P 𝒥 * ‖V‖ ^ 2 := by
  set c := couplingScale P 𝒥
  set S := ∑ I : InteractionIndex P.N P.q,
    V I * (expectation ρ (M.interactionOperator I)).re
  set Q := (Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ)
  have hlinear' :
      (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re =
        c * ∑ I : InteractionIndex P.N P.q,
          V I * (expectation ρ (M.interactionOperator I)).re := by
    unfold normalizedHamiltonian expectation
    simp +decide [hamiltonian, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _]
    simp +decide [phase, MajoranaSystem.interactionOperator]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hlinear :
      (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re = c * S := by
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
      simp +decide [Complex.normSq, Complex.sq_norm]
      nlinarith only
  have hdot : S ^ 2 ≤ ‖V‖ ^ 2 * Q := by
    have hsum_nonneg : 0 ≤ ∑ I : InteractionIndex P.N P.q, V I ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hexpect hsum_nonneg
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt hsum_nonneg]
    exact le_trans hcs hmul
  have hscaled := mul_le_mul_of_nonneg_left hdot (sq_nonneg (P.β * c))
  rw [hlinear]
  rw [sq_abs]
  change (P.β * (c * S)) ^ 2 ≤ (P.β * c) ^ 2 * Q * ‖V‖ ^ 2
  nlinarith only [hscaled]

/-- The exact finite-volume directional bound in unsquared form. -/
theorem abs_beta_expectation_normHam_le_exact
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ)
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ)
    (V : CouplingSpace P.N P.q) :
    |P.β * (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re|
      ≤ Real.sqrt (exactLipschitzSq P 𝒥) * ‖V‖ := by
  have hsq := abs_beta_expectation_normHam_sq_le_exact P M 𝒥 ρ hρ V
  calc
    |P.β * (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re| =
        Real.sqrt
          (|P.β * (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re| ^ 2) := by
            rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (exactLipschitzSq P 𝒥 * ‖V‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (exactLipschitzSq P 𝒥) * ‖V‖ := by
      rw [Real.sqrt_mul (exactLipschitzSq_nonneg P 𝒥), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg V)]

theorem sqrt_exactLipschitzSq
    (P : Params) (𝒥 : ℝ) (h𝒥 : 0 ≤ 𝒥) :
    Real.sqrt (exactLipschitzSq P 𝒥) =
      |P.β| * couplingScale P 𝒥 *
        Real.sqrt ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ)) := by
  have hc : 0 ≤ couplingScale P 𝒥 := by
    unfold couplingScale
    exact mul_nonneg h𝒥 (Real.sqrt_nonneg _)
  rw [exactLipschitzSq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_mul]
  rw [abs_of_nonneg hc]

/--
Cauchy–Schwarz combined with the SYK sum-of-squares bound controls the
directional gradient of the normalized SYK energy by the simplified constant.
-/
theorem abs_beta_expectation_normHam_le
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 ≤ 𝒥)
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ)
    (V : CouplingSpace P.N P.q) :
    |P.β * (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re|
      ≤ (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ)) * ‖V‖ := by
  refine le_trans (abs_beta_expectation_normHam_le_exact P M 𝒥 ρ hρ V) ?_
  rw [sqrt_exactLipschitzSq P 𝒥 h𝒥]
  have hscale := mul_le_mul_of_nonneg_left
    (couplingScale_mul_sqrt_choose_le P 𝒥 h𝒥) (abs_nonneg P.β)
  have := mul_le_mul_of_nonneg_right hscale (norm_nonneg V)
  convert this using 1 <;> ring

/--
The directional derivative of `logPartition` along `V`, expressed as a
thermal expectation of the (normalized) SYK energy.
-/
theorem logPartition_line_deriv_eq
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

/-- The SYK log-partition function is Lipschitz with the stated constant. -/
theorem logPartition_lipschitz
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 ≤ 𝒥) :
    LipschitzWith (simpleLipschitzConstant P 𝒥)
      (logPartition P M 𝒥) := by
  apply LipschitzWith.of_dist_le_mul;
  intro x y;
  -- Let $V := x - y$ and $g := fun r : ℝ => logPartition P M 𝒥 (y + r • V)$.
  set V : CouplingSpace P.N P.q := x - y
  set g : ℝ → ℝ := fun r => logPartition P M 𝒥 (y + r • V);
  -- By the properties of the derivative and the Lipschitz constant, we have:
  have h_deriv_bound : ∀ r : ℝ, |deriv g r| ≤ (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ)) * ‖V‖ := by
    intro r
    have h_deriv : deriv g r = -P.β * (expectation (thermalDensity P.inverseTemperature (normalizedHamiltonian P M 𝒥 (y + r • V))) (normalizedHamiltonian P M 𝒥 V)).re := by
      convert HasDerivAt.deriv ( logPartition_line_deriv_eq P M 𝒥 y V r ) using 1;
    have := abs_beta_expectation_normHam_le P M 𝒥 h𝒥 ( thermalDensity P.inverseTemperature ( normalizedHamiltonian P M 𝒥 ( y + r • V ) ) ) ( thermalDensity_isDensityMatrix P.inverseTemperature ( normalizedHamiltonian_self_adjoint P M 𝒥 _ ) ) V; simp_all +decide [ abs_mul, abs_neg ] ;
  -- By the Mean Value Theorem, there exists some $c \in (0, 1)$ such that $g(1) - g(0) = g'(c)$.
  have h_mvt : ∃ c ∈ Set.Ioo 0 1, g 1 - g 0 = deriv g c := by
    have := exists_deriv_eq_slope g zero_lt_one;
    exact this ( continuousOn_of_forall_continuousAt fun r hr => by exact DifferentiableAt.continuousAt <| by exact ( logPartition_line_deriv_eq P M 𝒥 y V r |> HasDerivAt.differentiableAt ) ) ( fun r hr => by exact DifferentiableAt.differentiableWithinAt <| by exact ( logPartition_line_deriv_eq P M 𝒥 y V r |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by norm_num at hc₂; linarith ⟩;
  simp +zetaDelta at *;
  obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt; rw [ dist_eq_norm ] ; rw [ simpleLipschitzConstant ] ; simp +decide [ hc₂ ] ;
  exact le_trans ( h_deriv_bound c ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( norm_nonneg _ ) ) |> le_trans <| by rw [ dist_eq_norm ] ;

/-- For an empty state space the log-partition function is identically zero. -/
theorem logPartition_eq_zero_of_isEmpty
    {d : Type*} [Fintype d] [DecidableEq d] [IsEmpty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) :
    logPartition P M 𝒥 J = 0 := by
  unfold logPartition; simp +decide [ partitionFunction ] ;

/-- At zero inverse temperature the log-partition function is constant. -/
theorem logPartition_eq_log_card_of_beta_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (hβ : P.β = 0) (J : CouplingSpace P.N P.q) :
    logPartition P M 𝒥 J = Real.log (Fintype.card d : ℝ) := by
  have hinv : P.inverseTemperature = 0 := by
    apply NNReal.eq
    simpa [P.coe_inverseTemperature, hβ]
  simp [logPartition, hinv]

/-- At zero inverse temperature every positive-deviation tail event is empty. -/
theorem logPartition_tail_of_beta_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (hβ : P.β = 0) (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P M 𝒥 J -
          ∫ K, logPartition P M 𝒥 K
            ∂standardGaussianMeasure P.N P.q| > t} = 0 := by
  let a : ℝ := Real.log (Fintype.card d : ℝ)
  have hconst : ∀ J : CouplingSpace P.N P.q, logPartition P M 𝒥 J = a :=
    fun J => logPartition_eq_log_card_of_beta_zero P M 𝒥 hβ J
  have hintegral :
      ∫ K, logPartition P M 𝒥 K ∂standardGaussianMeasure P.N P.q = a := by
    simp only [hconst]
    simp
  have hset :
      {J : CouplingSpace P.N P.q | |logPartition P M 𝒥 J -
          ∫ K, logPartition P M 𝒥 K
            ∂standardGaussianMeasure P.N P.q| > t} = ∅ := by
    ext J
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [hconst J, hintegral]
    simpa using ht.le
  rw [hset]
  simp

/-- The same estimate for the product standard Gaussian coupling measure. -/
theorem logPartition_two_sided_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P M 𝒥 J -
          ∫ K, logPartition P M 𝒥 K
            ∂standardGaussianMeasure P.N P.q| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2))) := by
  rcases isEmpty_or_nonempty d with hd | hd
  · -- Empty state space: `logPartition` is identically zero, so the tail set
    -- is empty because `t > 0`.
    have hconst : ∀ K : CouplingSpace P.N P.q, logPartition P M 𝒥 K = 0 :=
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
  · exact logPartition_two_sided_tail P M 𝒥 h𝒥 hβ
      (logPartition_lipschitz P M 𝒥 h𝒥.le) t ht
end SYK
