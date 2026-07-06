import SYK.SYK_model.model
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open scoped BigOperators ComplexOrder ENNReal NNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK

section DensityMatrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A finite-dimensional density matrix. -/
def IsDensityMatrix (ρ : Matrix d d ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- Expectation of a matrix observable in a density matrix. -/
noncomputable def expectation (ρ A : Matrix d d ℂ) : ℂ :=
  Matrix.trace (ρ * A)

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

theorem expectation_im_eq_zero
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    (expectation ρ A).im = 0 := by
  have h := expectation_star_eq hρ hA
  exact Complex.conj_eq_iff_im.mp h

theorem expectation_eq_ofReal_re
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    ((expectation ρ A).re : ℂ) = expectation ρ A := by
  apply Complex.ext
  · simp
  · simp [expectation_im_eq_zero hρ hA]

theorem density_variance_nonneg
    {ρ B : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hB : star B = B) :
    0 ≤ (expectation ρ (B * B)).re - (expectation ρ B).re ^ 2 := by
  let x : ℝ := (expectation ρ B).re
  let C : Matrix d d ℂ := B - (x : ℂ) • (1 : Matrix d d ℂ)
  have hC : star C = C := by
    simp [C, hB]
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
      B * B - ((2 * x : ℝ) : ℂ) • B + ((x ^ 2 : ℝ) : ℂ) • 1 := by
    have htwo : ((2 * x : ℝ) : ℂ) = 2 * (x : ℂ) := by norm_num
    have hpow : ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) ^ 2 := by norm_num [pow_two]
    rw [htwo, hpow]
    simp only [C, sub_mul, mul_sub]
    simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    rw [show (2 : ℂ) * (x : ℂ) = (x : ℂ) + x by ring, add_smul]
    simp only [smul_smul, pow_two]
    abel
  rw [hcycle, hCC] at htrace
  have hexpB : expectation ρ B = (x : ℂ) := by
    rw [← expectation_eq_ofReal_re hρ hB]
  have htraceρ : Matrix.trace ρ = (1 : ℂ) := hρ.2
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_one, smul_eq_mul] at htrace
  have htrace' : 0 ≤
      (expectation ρ (B * B) - (2 * x : ℂ) * expectation ρ B +
        (x ^ 2 : ℂ) * Matrix.trace ρ).re := by
    simpa [expectation] using htrace
  rw [hexpB, htraceρ] at htrace'
  norm_num [pow_two] at htrace'
  dsimp [x] at htrace' ⊢
  nlinarith

end DensityMatrix

/-- The Euclidean space of real SYK couplings. -/
abbrev CouplingSpace (N q : ℕ) :=
  EuclideanSpace ℝ (InteractionIndex N q)

/-- The product standard Gaussian measure transported to coupling space. -/
noncomputable def standardGaussianMeasure (N q : ℕ) :
    Measure (CouplingSpace N q) :=
  (Measure.pi fun _ : InteractionIndex N q => gaussianReal 0 1).map
    (WithLp.toLp 2)

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

/--
The Gaussian concentration input isolated by the blueprint.  Mathlib does not
currently provide this theorem in the required finite-dimensional form, so the
final SYK theorem accepts this proposition as a hypothesis.
-/
def GaussianLipschitzConcentration {E : Type*}
    [MeasurableSpace E] [PseudoMetricSpace E]
    (γ : Measure E) : Prop :=
  ∀ (F : E → ℝ) (L t : ℝ),
    0 < L → 0 < t → LipschitzWith L.toNNReal F →
      γ {x | |F x - ∫ y, F y ∂γ| > t} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2)))

/-- The Lipschitz constant obtained from the SYK sum-of-squares estimate. -/
noncomputable def simpleLipschitzConstant (P : Params) (𝒥 : ℝ) : ℝ≥0 :=
  Real.toNNReal (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ))

/--
The two-sided superconcentration estimate.  Its only analytic input not
available in mathlib is `GaussianLipschitzConcentration`; the SYK gradient
estimate is supplied in the reusable `hLip` hypothesis.
-/
theorem logPartition_two_sided_tail
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
    (γ : Measure (CouplingSpace P.N P.q))
    (hγ : GaussianLipschitzConcentration
      (E := CouplingSpace P.N P.q) γ)
    (hLip : LipschitzWith (simpleLipschitzConstant P 𝒥)
      (logPartition P M 𝒥))
    (t : ℝ) (ht : 0 < t) :
    γ {J | |logPartition P M 𝒥 J -
        ∫ K, logPartition P M 𝒥 K ∂γ| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2))) := by
  have hq : 0 < (P.q : ℝ) := by exact_mod_cast P.q_pos
  have hsqrt : 0 < Real.sqrt (P.q : ℝ) := Real.sqrt_pos.2 hq
  let L : ℝ := |P.β| * 𝒥 / Real.sqrt (P.q : ℝ)
  have hL : 0 < L := div_pos (mul_pos (abs_pos.mpr hβ) h𝒥) hsqrt
  have hLip' : LipschitzWith L.toNNReal (logPartition P M 𝒥) := by
    simpa [L, simpleLipschitzConstant] using hLip
  have htail := hγ (logPartition P M 𝒥) L t hL ht hLip'
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

/-- The same estimate for the product standard Gaussian coupling measure. -/
theorem logPartition_two_sided_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
    (hγ : GaussianLipschitzConcentration
      (standardGaussianMeasure P.N P.q))
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
  exact logPartition_two_sided_tail P M 𝒥 h𝒥 hβ
    (standardGaussianMeasure P.N P.q) hγ hLip t ht

end SYK
