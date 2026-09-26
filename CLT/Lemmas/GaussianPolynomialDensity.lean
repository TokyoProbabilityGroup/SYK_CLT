import SYK.CLT.Lemmas.GaussianHermiteDensity
import SYK.CLT.Lemmas.GaussianMomentDetermination

/-!
# Polynomial density for Gaussian `L²`

Analytic lemmas toward proving the Gaussian polynomial density condition in
`GaussianHermiteDensity.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace SYK.CLT

/-- A real exponential belongs to `L²` of the standard Gaussian. -/
theorem gaussianExp_memLp_two (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (t * x)) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (2 * t) using 1
  funext x
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- A Gaussian `L²` function remains integrable after multiplication by any
real exponential. -/
theorem gaussianLp_integrable_mul_exp
    (f : Lp ℝ 2 (gaussianReal 0 1)) (t : ℝ) :
    Integrable (fun x : ℝ => f x * Real.exp (t * x)) (gaussianReal 0 1) := by
  exact (Lp.memLp f).integrable_mul (gaussianExp_memLp_two t)

/-- The positive weighted Gaussian measure associated with an `L²` class. -/
noncomputable def gaussianPositiveMeasure
    (f : Lp ℝ 2 (gaussianReal 0 1)) : Measure ℝ :=
  (gaussianReal 0 1).withDensity fun x => ENNReal.ofReal (f x)

theorem gaussianPositiveMeasure_finite
    (f : Lp ℝ 2 (gaussianReal 0 1)) :
    IsFiniteMeasure (gaussianPositiveMeasure f) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact ((Lp.memLp f).integrable (by norm_num)).2

/-- Exponential moments of the positive weighted Gaussian measure. -/
theorem gaussianPositiveMeasure_integrable_exp
    (f : Lp ℝ 2 (gaussianReal 0 1)) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianPositiveMeasure f) := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x))
      (gaussianReal 0 1) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [gaussianPositiveMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas (by simp)]
  have hpos := (gaussianLp_integrable_mul_exp f t).pos_part
  convert hpos using 1
  funext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal',
    max_mul_of_nonneg (f x) 0 (le_of_lt (Real.exp_pos _))]
  simp

/-- Integrals under the positive weighted measure are positive-part weighted
Gaussian integrals. -/
theorem integral_gaussianPositiveMeasure
    (f : Lp ℝ 2 (gaussianReal 0 1)) (g : ℝ → ℝ) :
    (∫ x, g x ∂gaussianPositiveMeasure f) =
      ∫ x, max (f x) 0 * g x ∂gaussianReal 0 1 := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x))
      (gaussianReal 0 1) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [gaussianPositiveMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas (by simp)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal']

theorem gaussianPositiveMeasure_integrable_pow
    (f : Lp ℝ 2 (gaussianReal 0 1)) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianPositiveMeasure f) := by
  have hset : integrableExpSet id (gaussianPositiveMeasure f) = Set.univ := by
    ext t
    simp [integrableExpSet, gaussianPositiveMeasure_integrable_exp f t]
  simpa using (integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianPositiveMeasure f) (by simp [hset]) n)

private theorem gaussianPositivePart_mul_pow_integrable
    (f : Lp ℝ 2 (gaussianReal 0 1)) (n : ℕ) :
    Integrable (fun x : ℝ => max (f x) 0 * x ^ n) (gaussianReal 0 1) := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x))
      (gaussianReal 0 1) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have h := (integrable_withDensity_iff_integrable_smul₀'
    hmeas (by simp)).mp (gaussianPositiveMeasure_integrable_pow f n)
  simpa only [gaussianPositiveMeasure, smul_eq_mul, ENNReal.toReal_ofReal'] using h

/-- Vanishing Gaussian polynomial moments makes the positive and negative
weighted measures have equal moments. -/
theorem gaussianPositiveMeasure_moments_eq_of_orthogonal
    (f : Lp ℝ 2 (gaussianReal 0 1))
    (horth : ∀ n : ℕ, ∫ x : ℝ, f x * x ^ n ∂gaussianReal 0 1 = 0)
    (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂gaussianPositiveMeasure f) =
      ∫ x : ℝ, x ^ n ∂gaussianPositiveMeasure (-f) := by
  rw [integral_gaussianPositiveMeasure, integral_gaussianPositiveMeasure]
  have hpoint : (fun x : ℝ => max ((-f) x) 0 * x ^ n) =ᵐ[gaussianReal 0 1]
      (fun x => max (-(f x)) 0 * x ^ n) := by
    filter_upwards [Lp.coeFn_neg f] with x hx
    simp only [Pi.neg_apply] at hx
    rw [hx]
  have hneg : (∫ x : ℝ, max ((-f) x) 0 * x ^ n ∂gaussianReal 0 1) =
      ∫ x : ℝ, max (-(f x)) 0 * x ^ n ∂gaussianReal 0 1 := by
    exact integral_congr_ae hpoint
  rw [hneg]
  have hdecomp : (fun x : ℝ => max (f x) 0 * x ^ n -
      max (-(f x)) 0 * x ^ n) = (fun x => f x * x ^ n) := by
    funext x
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  have hnegInt : Integrable (fun x : ℝ => max (-(f x)) 0 * x ^ n)
      (gaussianReal 0 1) :=
    (gaussianPositivePart_mul_pow_integrable (-f) n).congr hpoint
  have h := integral_sub (gaussianPositivePart_mul_pow_integrable f n) hnegInt
  rw [hdecomp, horth n] at h
  linarith

/-- Vanishing polynomial moments identify the positive and negative
weighted Gaussian measures. -/
theorem gaussianPositiveMeasure_eq_neg_of_orthogonal
    (f : Lp ℝ 2 (gaussianReal 0 1))
    (horth : ∀ n : ℕ, ∫ x : ℝ, f x * x ^ n ∂gaussianReal 0 1 = 0) :
    gaussianPositiveMeasure f = gaussianPositiveMeasure (-f) := by
  letI := gaussianPositiveMeasure_finite f
  letI := gaussianPositiveMeasure_finite (-f)
  exact measure_eq_of_moments
    (gaussianPositiveMeasure_integrable_exp f)
    (gaussianPositiveMeasure_integrable_exp (-f))
    (gaussianPositiveMeasure_moments_eq_of_orthogonal f horth)

/-- A one-dimensional Gaussian `L²` class with vanishing polynomial
moments is zero. -/
theorem gaussianLp_eq_zero_of_polynomial_moments_zero
    (f : Lp ℝ 2 (gaussianReal 0 1))
    (horth : ∀ n : ℕ, ∫ x : ℝ, f x * x ^ n ∂gaussianReal 0 1 = 0) :
    f = 0 := by
  have hmeasure := gaussianPositiveMeasure_eq_neg_of_orthogonal f horth
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x))
      (gaussianReal 0 1) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmeasNeg : AEMeasurable (fun x : ℝ => ENNReal.ofReal ((-f) x))
      (gaussianReal 0 1) := (Lp.memLp (-f)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpos := Measure.rnDeriv_withDensity₀ (gaussianReal 0 1) hmeas
  have hneg := Measure.rnDeriv_withDensity₀ (gaussianReal 0 1) hmeasNeg
  change (gaussianPositiveMeasure f).rnDeriv (gaussianReal 0 1) =ᵐ[gaussianReal 0 1]
    (fun x => ENNReal.ofReal (f x)) at hpos
  change (gaussianPositiveMeasure (-f)).rnDeriv (gaussianReal 0 1) =ᵐ[gaussianReal 0 1]
    (fun x => ENNReal.ofReal ((-f) x)) at hneg
  rw [hmeasure] at hpos
  have heq := hpos.symm.trans hneg
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [heq, Lp.coeFn_neg f] with x hx hxneg
  simp only [Pi.neg_apply] at hxneg
  rw [hxneg] at hx
  have hxreal := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal'] at hxreal
  have h := max_zero_sub_max_neg_zero_eq_self (f x)
  rw [hxreal, sub_self] at h
  exact h.symm

end SYK.CLT
