import SYK.CLT.lemmas.chaos_estimates
import SYK.CLT.lemmas.partition_basic

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory Topology

namespace SYK
namespace CLT

/-!
Completion of the CLT from the radial chi-square statistic, the higher-chaos
estimate, and the annealed derivative asymptotic.
-/

/-- Scaled relative CLT and matching relative-variance asymptotic. -/
theorem partitionFunction_CLT_with_variance (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
        ConvergesToCenteredGaussian
          (fun k => standardGaussianMeasure (systemSize P k) P.q)
          (scaledRelativePartition P β)
          ((Nat.factorial P.q : ℝ) / 2 * β ^ 2 *
            limitingPressureDerivative P β ^ 2) ∧
        Tendsto
          (fun k =>
            (systemSize P k : ℝ) ^ (P.q - 2) *
              variance (partitionFunctionR P k β)
                (standardGaussianMeasure (systemSize P k) P.q) /
              annealedPartitionR P k β ^ 2)
          atTop
          (𝓝 ((Nat.factorial P.q : ℝ) / 2 * β ^ 2 *
            limitingPressureDerivative P β ^ 2)) := by
  sorry

/-- The standardized high-temperature partition-function CLT. -/
theorem standardized_partition_CLT (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
        ConvergesToCenteredGaussian
          (fun k => standardGaussianMeasure (systemSize P k) P.q)
          (standardizedPartition P β) 1 := by
  sorry

end CLT
end SYK
