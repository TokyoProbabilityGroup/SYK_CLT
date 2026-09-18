import SYK.Model.FiniteDimensionalGibbs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef

/-! Density-matrix expectation bounds for anticommuting observables. -/

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped Matrix.Norms.Operator

namespace SYK

section AnticommutingFamily

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

omit [Fintype ι] in
private theorem weighted_sum_sq_aux
    (A : ι → Matrix d d ℂ) (c : ι → ℂ)
    (hsq : ∀ i, A i * A i = 1)
    (hanti : ∀ i j, i ≠ j → A i * A j = -(A j * A i))
    (s : Finset ι) :
    (∑ i ∈ s, c i • A i) * (∑ i ∈ s, c i • A i) =
      (∑ i ∈ s, c i ^ 2) • (1 : Matrix d d ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      let S : Matrix d d ℂ := ∑ i ∈ s, c i • A i
      have hAS : A a * S = -(S * A a) := by
        dsimp [S]
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [hanti a i (fun hai => ha (hai ▸ hi))]
        simp
      have hcross : (c a • A a) * S = -(S * (c a • A a)) := by
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hAS]
        simp
      have haa : (c a • A a) * (c a • A a) =
          c a ^ 2 • (1 : Matrix d d ℂ) := by
        rw [smul_mul_smul_comm, hsq, pow_two]
      change (c a • A a + S) * (c a • A a + S) =
        (c a ^ 2 + ∑ i ∈ s, c i ^ 2) • (1 : Matrix d d ℂ)
      rw [mul_add, add_mul, add_mul, hcross, haa, ih]
      module

theorem sum_sq_expectation_le_one
    (ρ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hρ : IsDensityMatrix ρ)
    (hstar : ∀ i, star (A i) = A i)
    (hsq : ∀ i, A i * A i = 1)
    (hanti : ∀ i j, i ≠ j → A i * A j = -(A j * A i)) :
    ∑ i, ‖expectation ρ (A i)‖ ^ 2 ≤ 1 := by
  classical
  let c : ι → ℂ := fun i => expectation ρ (A i)
  let B : Matrix d d ℂ := ∑ i, c i • A i
  let s : ℝ := ∑ i, ‖c i‖ ^ 2
  have hcstar (i : ι) : star (c i) = c i := by
    exact expectation_star_eq hρ (hstar i)
  have hcim (i : ι) : (c i).im = 0 := by
    exact expectation_im_eq_zero hρ (hstar i)
  have hBstar : star B = B := by
    classical
    simp only [B, star_sum, star_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcstar i, hstar i]
  have hBsqC : B * B = (∑ i, c i ^ 2) • (1 : Matrix d d ℂ) := by
    simpa [B] using weighted_sum_sq_aux A c hsq hanti Finset.univ
  have hsumC : (∑ i, c i ^ 2) = (s : ℂ) := by
    apply Complex.ext
    · rw [Complex.re_sum]
      change (∑ i, (c i ^ 2).re) = s
      dsimp [s]
      apply Finset.sum_congr rfl
      intro i _
      rw [Complex.sq_norm]
      simp [pow_two, Complex.mul_re, Complex.normSq_apply, hcim i]
    · rw [Complex.im_sum]
      simp only [Complex.ofReal_im]
      apply Finset.sum_eq_zero
      intro i _
      simp [pow_two, Complex.mul_im, hcim i]
  have hBsq : B * B = (s : ℂ) • (1 : Matrix d d ℂ) := by
    rw [hBsqC, hsumC]
  have hexpB : expectation ρ B = (s : ℂ) := by
    simp only [B, expectation, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    rw [← hsumC]
    apply Finset.sum_congr rfl
    intro i _
    change c i * c i = c i ^ 2
    rw [pow_two]
  have hexpBsq : expectation ρ (B * B) = (s : ℂ) := by
    rw [hBsq]
    simp [expectation, hρ.2]
  have hvar := density_variance_nonneg hρ hBstar
  rw [hexpBsq, hexpB] at hvar
  have hs0 : 0 ≤ s := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖c i‖
  have hs1 : s ≤ 1 := by
    norm_num at hvar
    nlinarith
  simpa [s, c] using hs1

end AnticommutingFamily


end SYK
