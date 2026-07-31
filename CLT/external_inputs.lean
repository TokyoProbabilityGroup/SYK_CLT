import SYK.CLT.main_result
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false

/-!
# External inputs for the high-temperature CLT

The complex second-moment estimate and the annealed pressure limit are proved
outside this directory.  They are collected in one explicit input structure
so the CLT files do not hide unfinished results behind axioms or identity
theorems.
-/

noncomputable section

open Filter MeasureTheory Topology

namespace SYK.CLT

/-- Zero-freeness and the complex second-moment estimate on a fixed disk. -/
def ComplexSecondMomentStatement (C : FixedParameters) : Prop :=
  ∃ R K : ℝ, ∃ k₀ : ℕ,
    0 < R ∧ 0 ≤ K ∧
    ∀ k ≥ k₀, ∀ z : ℂ, ‖z‖ ≤ R →
      annealedPartitionC C k z ≠ 0 ∧
      (∫ g,
          ‖partitionFunctionC C k z g / annealedPartitionC C k z - 1‖ ^ 2
            ∂standardGaussianMeasure (systemSize C k) C.q) ≤
        K / (systemSize C k : ℝ) ^ fluctuationExponent C

/-- Annealed pressure convergence and its derivative limit. -/
def AnnealedLimitStatement (C : FixedParameters) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧
    AnalyticOnNhd ℝ (limitingAnnealedPressure C) (Set.Ioo (-β₀) β₀) ∧
    (∀ β ∈ Set.Ioo (-β₀) β₀,
      limitingAnnealedPressure C (-β) = limitingAnnealedPressure C β) ∧
    (∀ β ∈ Set.Ioo (-β₀) β₀,
      Tendsto (fun k => annealedPressure C k β) atTop
        (𝓝 (limitingAnnealedPressure C β))) ∧
    (∀ β ∈ Set.Ioo (-β₀) β₀,
      Tendsto
        (fun k =>
          deriv (fun t => Real.log (annealedPartitionR C k t)) β /
            systemSize C k)
        atTop (𝓝 (limitingPressureDerivative C β))) ∧
    Tendsto
      (fun β => limitingPressureDerivative C β / β)
      (𝓝[≠] 0) (𝓝 ((C.q : ℝ)⁻¹))

/-- Results imported from the high-temperature analysis. -/
structure HighTemperatureInputs (C : FixedParameters) : Prop where
  complex_second_moment : ComplexSecondMomentStatement C
  annealed_limit : AnnealedLimitStatement C

end SYK.CLT
