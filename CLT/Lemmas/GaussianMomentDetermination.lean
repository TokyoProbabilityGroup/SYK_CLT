import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Moment determination under exponential integrability

Equality of all polynomial moments gives equality of moment-generating
functions by analyticity. Equality of their complex extensions then gives
equality of finite real measures. This is an analytic input for Gaussian
polynomial density.
-/

open MeasureTheory ProbabilityTheory

namespace SYK.CLT

/-- Two real measures with all exponential moments have the same moment
generating function if their polynomial moments agree. -/
theorem mgf_eq_of_moments {μ ν : Measure ℝ}
    (hμ : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hν : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂μ = ∫ x : ℝ, x ^ n ∂ν) :
    mgf id μ = mgf id ν := by
  have hsetμ : integrableExpSet id μ = Set.univ := by
    ext t
    simp [integrableExpSet, hμ t]
  have hsetν : integrableExpSet id ν = Set.univ := by
    ext t
    simp [integrableExpSet, hν t]
  have hcoeff : (fun n : ℕ => (∫ x : ℝ, x ^ n ∂μ) / (n.factorial : ℝ)) =
      (fun n : ℕ => (∫ x : ℝ, x ^ n ∂ν) / (n.factorial : ℝ)) := by
    funext n
    rw [hmom]
  have hseriesμ := hasFPowerSeriesAt_mgf (X := id) (μ := μ)
    (v := 0) (by simp [hsetμ])
  have hseriesν := hasFPowerSeriesAt_mgf (X := id) (μ := ν)
    (v := 0) (by simp [hsetν])
  simp only [id_eq, zero_mul, Real.exp_zero, mul_one] at hseriesμ hseriesν
  rw [hcoeff] at hseriesμ
  have hlocal : mgf id μ =ᶠ[nhds 0] mgf id ν := by
    filter_upwards [hseriesμ.eventually_hasSum_sub,
      hseriesν.eventually_hasSum_sub] with t htμ htν
    exact htμ.unique htν
  have hanμ : AnalyticOnNhd ℝ (mgf id μ) Set.univ := by
    simpa [hsetμ] using (analyticOnNhd_mgf (X := id) (μ := μ))
  have hanν : AnalyticOnNhd ℝ (mgf id ν) Set.univ := by
    simpa [hsetν] using (analyticOnNhd_mgf (X := id) (μ := ν))
  exact hanμ.eq_of_eventuallyEq hanν hlocal

/-- Exponentially integrable finite real measures are determined by their
polynomial moments. -/
theorem measure_eq_of_moments {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hν : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂μ = ∫ x : ℝ, x ^ n ∂ν) :
    μ = ν := by
  have hmgf := mgf_eq_of_moments hμ hν hmom
  have hzero : μ = 0 ↔ ν = 0 := by
    constructor
    · intro h
      by_contra hn
      have hpos := mgf_pos' (X := id) (t := 0) hn (hν 0)
      have hval : mgf id ν 0 = 0 := by
        rw [← congrFun hmgf 0, h, mgf_zero_measure]
        rfl
      rw [hval] at hpos
      exact (lt_irrefl 0) hpos
    · intro h
      by_contra hn
      have hpos := mgf_pos' (X := id) (t := 0) hn (hμ 0)
      have hval : mgf id μ 0 = 0 := by
        rw [congrFun hmgf 0, h, mgf_zero_measure]
        rfl
      rw [hval] at hpos
      exact (lt_irrefl 0) hpos
  have hsetμ : integrableExpSet id μ = Set.univ := by
    ext t
    simp [integrableExpSet, hμ t]
  have hcomplex : complexMGF id μ = complexMGF id ν := by
    funext z
    exact (eqOn_complexMGF_of_mgf' hmgf hzero) (by simp [hsetμ])
  exact Measure.ext_of_complexMGF_id_eq hcomplex

end SYK.CLT
