import SYK.CLT.definitions
import SYK.CLT.lemmas.convex_derivative

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Topology

namespace SYK
namespace CLT

/-!
These two statements are interfaces to results formalized elsewhere.

The complex second-moment estimate will come from `SYK/Second_moment`.  The
annealed pressure limit will come from `SYK/Annealed_FE`.  Their literature
proofs are intentionally not reproduced in the CLT directory.
-/

/-- Zero-freeness and the complex second-moment estimate on a fixed disk. -/
theorem complex_secondMoment_input (P : FixedParameters) :
    ∃ R C : ℝ, ∃ k₀ : ℕ,
      0 < R ∧ 0 ≤ C ∧
      ∀ k ≥ k₀, ∀ z : ℂ, ‖z‖ ≤ R →
        annealedPartitionC P k z ≠ 0 ∧
        (∫ g,
            ‖partitionFunctionC P k z g / annealedPartitionC P k z - 1‖ ^ 2
              ∂standardGaussianMeasure (systemSize P k) P.q) ≤
          C / (systemSize P k : ℝ) ^ fluctuationExponent P := by
  sorry

/-- Annealed pressure convergence and the derivative convergence obtained
from convexity. -/
theorem annealed_pressure_and_derivative_limit (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      AnalyticOnNhd ℝ (limitingAnnealedPressure P) (Set.Ioo (-β₀) β₀) ∧
      (∀ β ∈ Set.Ioo (-β₀) β₀,
        limitingAnnealedPressure P (-β) = limitingAnnealedPressure P β) ∧
      (∀ β ∈ Set.Ioo (-β₀) β₀,
        Tendsto (fun k => annealedPressure P k β) atTop
          (𝓝 (limitingAnnealedPressure P β))) ∧
      (∀ β ∈ Set.Ioo (-β₀) β₀,
        Tendsto
          (fun k =>
            deriv (fun t => Real.log (annealedPartitionR P k t)) β /
              systemSize P k)
          atTop (𝓝 (limitingPressureDerivative P β))) ∧
      Tendsto
        (fun β => limitingPressureDerivative P β / β)
        (𝓝[≠] 0) (𝓝 ((P.q : ℝ)⁻¹)) := by
  sorry

/-- Asymptotics of the exact radial coefficient. -/
theorem radialCoefficient_asymptotic (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ∈ Set.Ioo (-β₀) β₀,
        Tendsto
          (fun k => radialCoefficient P k β / systemSize P k)
          atTop
          (𝓝 (β / 2 * limitingPressureDerivative P β)) := by
  sorry

end CLT
end SYK
