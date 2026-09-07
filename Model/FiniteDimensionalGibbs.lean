import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-dimensional Gibbs states and trace-exponential calculus

This module collects density matrices and their expectations, Gibbs states at
nonnegative real inverse temperature, and the real derivative of the trace of
an affine matrix exponential. These constructions depend only on
finite-dimensional complex matrices, not on the SYK model parameters.
-/

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped MatrixOrder
open scoped Matrix.Norms.Operator

namespace SYK

section FiniteDimensionalGibbs

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Density matrices and expectations -/

/-- A finite-dimensional density matrix. -/
def IsDensityMatrix (ρ : Matrix d d ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- Expectation of a matrix observable in a density matrix. -/
noncomputable def expectation (ρ A : Matrix d d ℂ) : ℂ :=
  Matrix.trace (ρ * A)

omit [DecidableEq d] in
theorem expectation_star_eq
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    star (expectation ρ A) = expectation ρ A := by
  rw [expectation, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
  change Matrix.trace (star A * star ρ) = Matrix.trace (ρ * A)
  have hsρ : star ρ = ρ := by
    change Matrix.conjTranspose ρ = ρ
    exact hρ.1.isHermitian.eq
  rw [hA, hsρ]
  exact Matrix.trace_mul_comm A ρ

omit [DecidableEq d] in
theorem expectation_im_eq_zero
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    (expectation ρ A).im = 0 := by
  exact Complex.conj_eq_iff_im.mp (expectation_star_eq hρ hA)

omit [DecidableEq d] in
theorem expectation_eq_ofReal_re
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    ((expectation ρ A).re : ℂ) = expectation ρ A := by
  apply Complex.ext
  · simp
  · simp [expectation_im_eq_zero hρ hA]

theorem density_variance_nonneg
    {ρ B : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hB : star B = B) :
    0 ≤ (expectation ρ (B * B)).re - (expectation ρ B).re ^ 2 := by
  let z : ℂ := expectation ρ B
  let C : Matrix d d ℂ := B - z • (1 : Matrix d d ℂ)
  have hzstar : star z = z := by
    exact expectation_star_eq hρ hB
  have hC : star C = C := by
    simp [C, hB, hzstar]
  have hpos := hρ.1.conjTranspose_mul_mul_same C
  have htrace : 0 ≤ (Matrix.trace (star C * ρ * C)).re := by
    have hz : 0 ≤ Matrix.trace (Matrix.conjTranspose C * ρ * C) :=
      hpos.trace_nonneg
    exact (RCLike.nonneg_iff.mp hz).1
  have hcycle : Matrix.trace (star C * ρ * C) =
      Matrix.trace (ρ * (C * C)) := by
    rw [hC, Matrix.trace_mul_cycle C ρ C,
      Matrix.trace_mul_comm (C * C) ρ]
  have hCC : C * C =
      B * B - (2 * z) • B + z ^ 2 • 1 := by
    simp only [C, sub_mul, mul_sub]
    simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    rw [show (2 : ℂ) * z = z + z by ring, add_smul]
    simp only [smul_smul, pow_two]
    abel
  rw [hcycle, hCC] at htrace
  have htraceρ : Matrix.trace ρ = (1 : ℂ) := hρ.2
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_one, smul_eq_mul] at htrace
  have htrace' : 0 ≤
      (expectation ρ (B * B) - (2 * z) * expectation ρ B +
        z ^ 2 * Matrix.trace ρ).re := by
    simpa [expectation] using htrace
  rw [show expectation ρ B = z from rfl, htraceρ] at htrace'
  have hzim : z.im = 0 := by
    exact expectation_im_eq_zero hρ hB
  dsimp [z] at htrace' hzim ⊢
  norm_num [Complex.mul_re, pow_two] at htrace'
  nlinarith

/-! ## Gibbs states at nonnegative real inverse temperature -/

section PhysicalGibbs

/-- The unnormalized Gibbs operator `exp (-β H)`. -/
noncomputable def gibbsOperator (β : NNReal) (H : Matrix d d ℂ) : Matrix d d ℂ :=
  NormedSpace.exp (-((β : ℝ) : ℂ) • H)

/-- The finite-dimensional partition function `Tr (exp (-β H))`. -/
noncomputable def partitionFunction (β : NNReal) (H : Matrix d d ℂ) : ℂ :=
  Matrix.trace (gibbsOperator β H)

/-- Thermal expectation of an observable in the Gibbs state. -/
noncomputable def gibbsState (β : NNReal) (H O : Matrix d d ℂ) : ℂ :=
  Matrix.trace (O * gibbsOperator β H) / partitionFunction β H

@[simp]
theorem gibbsOperator_zero (H : Matrix d d ℂ) :
    gibbsOperator 0 H = 1 := by
  simp [gibbsOperator]

@[simp]
theorem partitionFunction_zero (H : Matrix d d ℂ) :
    partitionFunction 0 H = Fintype.card d := by
  simp [partitionFunction]

/-- The normalized Gibbs matrix, using the real positive partition function. -/
noncomputable def thermalDensity (β : NNReal) (H : Matrix d d ℂ) :
    Matrix d d ℂ :=
  ((partitionFunction β H).re⁻¹ : ℝ) • gibbsOperator β H

theorem gibbsOperator_posDef (β : NNReal) {H : Matrix d d ℂ}
    (hH : star H = H) : (gibbsOperator β H).PosDef := by
  let A : Matrix d d ℂ := -((β : ℝ) : ℂ) • H
  have hA : star A = A := by
    simp [A, hH]
  let B : Matrix d d ℂ := NormedSpace.exp ((2 : ℂ)⁻¹ • A)
  have hB : star B = B := by
    exact (show Matrix.IsHermitian ((2 : ℂ)⁻¹ • A) by
      simpa [Matrix.IsHermitian, hA]).exp.eq
  have hBB : B * B = NormedSpace.exp A := by
    dsimp [B]
    rw [← Matrix.exp_add_of_commute]
    · congr 1
      module
    · exact Commute.refl _
  have hpsd : (NormedSpace.exp A).PosSemidef := by
    have hnonneg : 0 ≤ NormedSpace.exp A := by
      rw [CStarAlgebra.nonneg_iff_eq_star_mul_self]
      refine ⟨B, ?_⟩
      change NormedSpace.exp A = star B * B
      rw [hB, hBB]
    exact Matrix.nonneg_iff_posSemidef.mp hnonneg
  apply hpsd.posDef_iff_isUnit.mpr
  exact Matrix.isUnit_exp A

theorem partitionFunction_star_eq (β : NNReal) {H : Matrix d d ℂ}
    (hH : star H = H) :
    star (partitionFunction β H) = partitionFunction β H := by
  have hG : star (gibbsOperator β H) = gibbsOperator β H :=
    (gibbsOperator_posDef β hH).isHermitian.eq
  change star (Matrix.trace (gibbsOperator β H)) =
    Matrix.trace (gibbsOperator β H)
  rw [← Matrix.trace_conjTranspose]
  change Matrix.trace (star (gibbsOperator β H)) = _
  rw [hG]

theorem partitionFunction_im_eq_zero (β : NNReal) {H : Matrix d d ℂ}
    (hH : star H = H) : (partitionFunction β H).im = 0 :=
  Complex.conj_eq_iff_im.mp (partitionFunction_star_eq β hH)

theorem partitionFunction_pos [Nonempty d] (β : NNReal)
    {H : Matrix d d ℂ} (hH : star H = H) :
    0 < (partitionFunction β H).re := by
  have h := (gibbsOperator_posDef β hH).trace_pos
  exact (RCLike.pos_iff.mp h).1

theorem thermalDensity_isDensityMatrix [Nonempty d] (β : NNReal)
    {H : Matrix d d ℂ} (hH : star H = H) :
    IsDensityMatrix (thermalDensity β H) := by
  have hZ : 0 < (partitionFunction β H).re := partitionFunction_pos β hH
  constructor
  · exact ((gibbsOperator_posDef β hH).smul (inv_pos.mpr hZ)).posSemidef
  · rw [thermalDensity, Matrix.trace_smul]
    change (((partitionFunction β H).re⁻¹ : ℝ) : ℂ) *
        partitionFunction β H = 1
    have hreal : ((partitionFunction β H).re : ℂ) =
        partitionFunction β H := by
      apply Complex.ext
      · simp
      · simp [partitionFunction_im_eq_zero β hH]
    rw [← hreal]
    simp only [Complex.ofReal_re]
    simp [ne_of_gt hZ]

theorem gibbsState_eq_expectation_thermalDensity [Nonempty d]
    (β : NNReal) {H O : Matrix d d ℂ} (hH : star H = H) :
    gibbsState β H O = expectation (thermalDensity β H) O := by
  have hZ : 0 < (partitionFunction β H).re := partitionFunction_pos β hH
  have hreal : ((partitionFunction β H).re : ℂ) =
      partitionFunction β H := by
    apply Complex.ext
    · simp
    · simp [partitionFunction_im_eq_zero β hH]
  rw [gibbsState, expectation, thermalDensity, Matrix.smul_mul,
    Matrix.trace_smul]
  change Matrix.trace (O * gibbsOperator β H) / partitionFunction β H =
    (((partitionFunction β H).re⁻¹ : ℝ) : ℂ) *
      Matrix.trace (gibbsOperator β H * O)
  rw [← hreal]
  simp only [Complex.ofReal_re]
  field_simp
  simpa [ne_of_gt hZ] using Matrix.trace_mul_comm O (gibbsOperator β H)

end PhysicalGibbs

section TraceExponentialDerivative

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable def matrixTraceCLM : Matrix d d ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap d ℝ ℂ)

omit [DecidableEq d] in
@[simp]
theorem matrixTraceCLM_apply (A : Matrix d d ℂ) :
    matrixTraceCLM A = Matrix.trace A := rfl

private theorem trace_pow_mul_cycle (A B : Matrix d d ℂ)
    {n i : ℕ} (hi : i ≤ n) :
    Matrix.trace (A ^ (n - i) * B * A ^ i) =
      Matrix.trace (B * A ^ n) := by
  calc
    Matrix.trace (A ^ (n - i) * B * A ^ i) =
        Matrix.trace (A ^ i * A ^ (n - i) * B) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (A ^ n * B) := by
      congr 1
      rw [← pow_add, Nat.add_sub_of_le hi]
    _ = Matrix.trace (B * A ^ n) := Matrix.trace_mul_comm _ _

private theorem hasDerivAt_trace_exp_term
    [Nonempty d]
    (A B : Matrix d d ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ matrixTraceCLM
        (((((n + 1).factorial : ℝ))⁻¹) •
          (A + s • B) ^ (n + 1)))
      (matrixTraceCLM
        ((((n.factorial : ℝ))⁻¹) •
          (B * (A + t • B) ^ n))) t := by
  letI : NormedAddCommGroup (Matrix d d ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix d d ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  have hpath : HasDerivAt (fun s : ℝ ↦ A + s • B) B t := by
    convert (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const B) using 1 <;>
      first | rfl | simp
  have hpow := hpath.fun_pow' (n + 1)
  have hscaled := hpow.const_smul (((n + 1).factorial : ℝ)⁻¹)
  have htrace : HasDerivAt
      (fun s : ℝ ↦ matrixTraceCLM
        (((n + 1).factorial : ℝ)⁻¹ • (A + s • B) ^ (n + 1)))
      (matrixTraceCLM
        (((n + 1).factorial : ℝ)⁻¹ •
          ∑ i ∈ Finset.range (n + 1),
            (A + t • B) ^ ((n + 1).pred - i) * B *
              (A + t • B) ^ i)) t := by
    convert (matrixTraceCLM (d := d)).hasFDerivAt.comp_hasDerivAt t hscaled using 1 <;>
      rfl
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      Matrix.trace
          ((A + t • B) ^ ((n + 1).pred - i) * B *
            (A + t • B) ^ i) =
        Matrix.trace (B * (A + t • B) ^ n) := by
    simpa using trace_pow_mul_cycle (A + t • B) B (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum :
      ∑ i ∈ Finset.range (n + 1),
          Matrix.trace
            ((A + t • B) ^ ((n + 1).pred - i) * B *
              (A + t • B) ^ i) =
        ∑ _i ∈ Finset.range (n + 1),
          Matrix.trace (B * (A + t • B) ^ n) := by
    exact Finset.sum_congr rfl fun i hi ↦ hterm i hi
  have hderiv :
      matrixTraceCLM
          (((n + 1).factorial : ℝ)⁻¹ •
            ∑ i ∈ Finset.range (n + 1),
              (A + t • B) ^ ((n + 1).pred - i) * B *
                (A + t • B) ^ i) =
        matrixTraceCLM
          ((n.factorial : ℝ)⁻¹ • (B * (A + t • B) ^ n)) := by
    simp only [matrixTraceCLM_apply, map_smul, Matrix.trace_sum]
    rw [hsum]
    rw [Finset.sum_const, Finset.card_range]
    rw [Nat.factorial_succ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
    push_cast
    ring
  rw [← hderiv]
  convert htrace using 1

theorem hasDerivAt_trace_exp_affine [Nonempty d]
    (A B : Matrix d d ℂ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ Matrix.trace (NormedSpace.exp (A + s • B)))
      (Matrix.trace (B * NormedSpace.exp (A + t • B))) t := by
  letI : NormedAddCommGroup (Matrix d d ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix d d ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  let C : ℝ → Matrix d d ℂ := fun s ↦ A + s • B
  let g : ℕ → ℝ → ℂ := fun n s ↦ matrixTraceCLM
    ((((n + 1).factorial : ℝ)⁻¹) • C s ^ (n + 1))
  let g' : ℕ → ℝ → ℂ := fun n s ↦ matrixTraceCLM
    (((n.factorial : ℝ)⁻¹) • (B * C s ^ n))
  let R : ℝ := ‖A‖ + (|t| + 1) * ‖B‖
  let K : ℝ := ‖matrixTraceCLM (d := d)‖ * ‖B‖
  let u : ℕ → ℝ := fun n ↦ K * ‖((n.factorial : ℝ)⁻¹)‖ * R ^ n
  have hR : 0 ≤ R := by positivity
  have hK : 0 ≤ K := by positivity
  have hu : Summable u := by
    have h := NormedSpace.norm_expSeries_summable'
      (𝕂 := ℝ) (𝔸 := ℝ) R
    have h' := h.mul_left K
    simpa [u, norm_smul, abs_of_nonneg hR, mul_assoc] using h'
  have hCnorm {y : ℝ} (hy : y ∈ Set.Ioo (t - 1) (t + 1)) : ‖C y‖ ≤ R := by
    have hyt : |y - t| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have hyabs : |y| ≤ |t| + 1 := by
      calc
        |y| = |t + (y - t)| := by ring_nf
        _ ≤ |t| + |y - t| := abs_add_le _ _
        _ ≤ |t| + 1 := by linarith
    calc
      ‖C y‖ = ‖A + y • B‖ := rfl
      _ ≤ ‖A‖ + ‖y • B‖ := norm_add_le _ _
      _ = ‖A‖ + |y| * ‖B‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ R := by
        dsimp [R]
        gcongr
  have hg (n : ℕ) (y : ℝ) (_hy : y ∈ Set.Ioo (t - 1) (t + 1)) :
      HasDerivAt (g n) (g' n y) y := by
    simpa [g, g', C] using hasDerivAt_trace_exp_term A B n y
  have hg_bound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (t - 1) (t + 1)) :
      ‖g' n y‖ ≤ u n := by
    have hpow : ‖C y ^ n‖ ≤ R ^ n := by
      exact (norm_pow_le (C y) n).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hCnorm hy) n)
    calc
      ‖g' n y‖ = ‖matrixTraceCLM
          (((n.factorial : ℝ)⁻¹) • (B * C y ^ n))‖ := rfl
      _ ≤ ‖matrixTraceCLM (d := d)‖ *
          ‖((n.factorial : ℝ)⁻¹) • (B * C y ^ n)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖matrixTraceCLM (d := d)‖ *
          (‖((n.factorial : ℝ)⁻¹)‖ * ‖B * C y ^ n‖) := by
        rw [norm_smul]
      _ ≤ ‖matrixTraceCLM (d := d)‖ *
          (‖((n.factorial : ℝ)⁻¹)‖ * (‖B‖ * ‖C y ^ n‖)) := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ ‖matrixTraceCLM (d := d)‖ *
          (‖((n.factorial : ℝ)⁻¹)‖ * (‖B‖ * R ^ n)) := by
        gcongr
      _ = u n := by simp [u, K]; ring
  have hg0 : Summable fun n ↦ g n t := by
    have htail : Summable fun n : ℕ ↦
        (((n + 1).factorial : ℝ)⁻¹) • C t ^ (n + 1) := by
      exact (NormedSpace.expSeries_summable' (𝕂 := ℝ) (C t)).comp_injective
        Nat.succ_injective
    rcases htail with ⟨a, ha⟩
    refine ⟨matrixTraceCLM (d := d) a, ?_⟩
    simpa [g, Function.comp_def] using
      ha.map (matrixTraceCLM (d := d)) (matrixTraceCLM (d := d)).continuous
  have htmem : t ∈ Set.Ioo (t - 1) (t + 1) := by constructor <;> linarith
  have htailDeriv : HasDerivAt (fun s ↦ ∑' n, g n s) (∑' n, g' n t) t :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      hg hg_bound htmem hg0 htmem
  have hfull (s : ℝ) : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • C s ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (C s)
  have hfun (s : ℝ) :
      Matrix.trace (NormedSpace.exp (C s)) =
        Matrix.trace (1 : Matrix d d ℂ) + ∑' n, g n s := by
    rw [show NormedSpace.exp (C s) =
        ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • C s ^ n by
      simpa using congrFun (NormedSpace.exp_eq_tsum ℝ) (C s)]
    change matrixTraceCLM (d := d)
      (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • C s ^ n) = _
    rw [ContinuousLinearMap.map_tsum (matrixTraceCLM (d := d)) (hfull s)]
    have htrace : Summable fun n : ℕ ↦ matrixTraceCLM (d := d)
        (((n.factorial : ℝ)⁻¹) • C s ^ n) := by
      rcases hfull s with ⟨a, ha⟩
      exact ⟨matrixTraceCLM (d := d) a,
        ha.map (matrixTraceCLM (d := d)) (matrixTraceCLM (d := d)).continuous⟩
    rw [← htrace.sum_add_tsum_nat_add 1]
    simp [g]
  have hderiv :
      (∑' n, g' n t) =
        Matrix.trace (B * NormedSpace.exp (C t)) := by
    let a : ℕ → Matrix d d ℂ := fun n ↦
      ((n.factorial : ℝ)⁻¹) • C t ^ n
    have ha : Summable a := hfull t
    have hBa : Summable fun n ↦ B * a n := ha.mul_left B
    calc
      (∑' n, g' n t) =
          ∑' n, matrixTraceCLM (d := d) (B * a n) := by
        congr 1
        funext n
        simp [g', a, Algebra.mul_smul_comm]
      _ = matrixTraceCLM (d := d) (∑' n, B * a n) :=
        (ContinuousLinearMap.map_tsum (matrixTraceCLM (d := d)) hBa).symm
      _ = matrixTraceCLM (d := d) (B * ∑' n, a n) := by
        congr 1
        exact (ha.hasSum.mul_left B).tsum_eq
      _ = Matrix.trace (B * NormedSpace.exp (C t)) := by
        rw [show NormedSpace.exp (C t) = ∑' n, a n by
          simpa [a] using congrFun (NormedSpace.exp_eq_tsum ℝ) (C t)]
        rfl
  have hsum := (hasDerivAt_const t (Matrix.trace (1 : Matrix d d ℂ))).add htailDeriv
  rw [hderiv] at hsum
  have hsum' : HasDerivAt
      ((fun _s : ℝ ↦ Matrix.trace (1 : Matrix d d ℂ)) +
        fun s ↦ ∑' n, g n s)
      (Matrix.trace (B * NormedSpace.exp (C t))) t := by
    simpa only [zero_add] using hsum
  refine hsum'.congr_of_eventuallyEq ?_
  filter_upwards with s
  simpa [C] using hfun s

end TraceExponentialDerivative

end FiniteDimensionalGibbs

end SYK
