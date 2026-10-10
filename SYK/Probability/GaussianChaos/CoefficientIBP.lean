import SYK.Probability.GaussianChaos.HermiteIBP
import SYK.Probability.GaussianChaos.Basic

/-!
# Gaussian Hermite coefficients for finite product Gaussians

This module restates the general integration-by-parts theorem of
`SYK.Probability.GaussianChaos.HermiteIBP` with the coupling law `gaussianCouplings`,
without depending on the Majorana sign-parity theorem.
The growth hypothesis is the manuscript's: only the partial derivatives `η ≤ α` are bounded.
Entry points: `gaussianCouplings_eq_pi`, `hermite_coefficient_ibp`,
`hermite_coefficient_integrable`. The module also shows that Hermite products of positive
degree have mean zero (`integral_hermiteMulti_eq_zero`) and are integrable against each other
(`integrable_hermiteMulti_mul`). Orthogonality and completeness are downstream.
-/

open MeasureTheory ProbabilityTheory

namespace SYK.GaussianChaos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The product Gaussian measure used for integration by parts is the law of
the couplings used in the sign-parity theorem. -/
theorem gaussianCouplings_eq_pi :
    gaussianCouplings ι = Measure.pi (fun _ : ι => gaussianReal 0 1) := rfl

/-- `lem:Gaussian-Hermite-IBP` in the notation used by the sign-parity result.
The bounds concern exactly the partial derivatives `η ≤ α`. -/
theorem hermite_coefficient_ibp (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ g,
      |partialMulti η f g| ≤
        C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, hermiteMulti α g * f g ∂gaussianCouplings ι) =
      ∫ g, partialMulti α f g ∂gaussianCouplings ι := by
  simpa only [hermiteMulti, gaussianCouplings] using
    hermiteMulti_ibp_of_expGrowth α hf hgrowth

/-- Both sides of the Hermite coefficient identity are integrable under the
manuscript's regularity and growth hypotheses. -/
theorem hermite_coefficient_integrable (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ g,
      |partialMulti η f g| ≤
        C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable (fun g => hermiteMulti α g * f g) (gaussianCouplings ι) ∧
      Integrable (partialMulti α f) (gaussianCouplings ι) := by
  simpa only [hermiteMulti, gaussianCouplings] using
    hermiteMulti_ibp_integrable α hf hgrowth

omit [Fintype ι] in
private theorem partialList_zero (l : List ι) :
    partialList l (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      have hderiv : coordDeriv i (fun _ => (0 : ℝ)) = fun _ => 0 := by
        funext g
        simp [coordDeriv]
      simpa only [partialList, hderiv] using ih

omit [Fintype ι] in
private theorem partialList_one_of_ne_nil (l : List ι) (hl : l ≠ []) :
    partialList l (fun _ => (1 : ℝ)) = fun _ => 0 := by
  cases l with
  | nil => contradiction
  | cons i l =>
      have hderiv : coordDeriv i (fun _ => (1 : ℝ)) = fun _ => 0 := by
        funext g
        simp [coordDeriv]
      simpa only [partialList, hderiv] using
        (partialList_zero (ι := ι) l)

omit [DecidableEq ι] in
/-- Every Hermite polynomial of positive total degree has zero Gaussian mean.
This is the constant-test-function case of the finite-dimensional integration
by parts theorem. -/
theorem integral_hermiteMulti_eq_zero (α : ι → ℕ)
    (hα : 0 < ∑ i : ι, α i) :
    (∫ g, hermiteMulti α g ∂gaussianCouplings ι) = 0 := by
  classical
  have hlist : multiIndexList α ≠ [] := by
    intro h
    have hlen := multiIndexList_length α
    rw [h] at hlen
    simp at hlen
    omega
  have hpartial : partialMulti α (fun _ => (1 : ℝ)) = fun _ => 0 := by
    exact partialList_one_of_ne_nil _ hlist
  have hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ g,
      |partialMulti η (fun _ => (1 : ℝ)) g| ≤
        C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro η _
    refine ⟨1, by norm_num, ?_⟩
    intro g
    have hbound : |partialMulti η (fun _ => (1 : ℝ)) g| ≤ 1 := by
      by_cases hη : multiIndexList η = []
      · simp [partialMulti, hη, partialList]
      · rw [partialMulti, partialList_one_of_ne_nil _ hη]
        simp
    have hexp : (1 : ℝ) ≤ Real.exp ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (norm_nonneg (WithLp.toLp 2 g : EuclideanSpace ℝ ι)))
    simpa only [one_mul] using hbound.trans hexp
  have h := hermite_coefficient_ibp α (by fun_prop) hgrowth
  simpa only [mul_one, hpartial, integral_zero] using h

omit [DecidableEq ι] in
/-- Pairings of two multivariate Hermite polynomials are integrable under the
standard product Gaussian measure. -/
theorem integrable_hermiteMulti_mul (α β : ι → ℕ) :
    Integrable (fun g => hermiteMulti α g * hermiteMulti β g)
      (gaussianCouplings ι) := by
  classical
  obtain ⟨C, c, hC, hc, hb⟩ := hermiteMulti_exp_bound β
  let D := max C c
  have hD : 0 ≤ D := hC.trans (le_max_left C c)
  have hbound : ∀ g : ι → ℝ,
      |hermiteMulti β g| ≤
        D * Real.exp (D * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro g
    have hExp : Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) ≤
        Real.exp (D * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (le_max_right C c) (norm_nonneg _)
    calc
      |hermiteMulti β g| ≤
          C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := hb g
      _ ≤ D * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) :=
          mul_le_mul_of_nonneg_right (le_max_left C c) (Real.exp_nonneg _)
      _ ≤ D * Real.exp (D * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) :=
          mul_le_mul_of_nonneg_left hExp hD
  simpa only [gaussianCouplings_eq_pi] using
    integrable_hermiteMulti_mul_of_expGrowth α (continuous_hermiteMulti β) D hD hbound

end SYK.GaussianChaos
