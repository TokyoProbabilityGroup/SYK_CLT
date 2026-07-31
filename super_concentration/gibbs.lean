import SYK.super_concentration.core
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Gibbs and trace calculus for SYK superconcentration

This module contains Gibbs-density identities and differentiation of the
trace of a matrix exponential along affine lines.
-/

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped MatrixOrder
open scoped Matrix.Norms.Operator
open MeasureTheory
open ProbabilityTheory

namespace SYK

section GibbsDensity

variable {d : Type*} [Fintype d] [DecidableEq d]

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
      refi…1502 tokens truncated…)⁻¹)‖ * R ^ n
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
  convert hsum using 1
  · funext s
    exact hfun s
  · simp [C]

end TraceExponentialDerivative

end SYK

