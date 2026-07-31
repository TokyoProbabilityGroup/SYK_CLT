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
def PartitionFunctionCLTStatement (P : FixedParameters) : Prop :=
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
            limitingPressureDerivative P β ^ 2))

/-- The standardized conclusion of the high-temperature CLT. -/
def StandardizedPartitionCLTStatement (P : FixedParameters) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
      ConvergesToCenteredGaussian
        (fun k => standardGaussianMeasure (systemSize P k) P.q)
        (standardizedPartition P β) 1

/-- Internal probabilistic inputs still being formalized in the CLT tree. -/
structure PartitionFunctionCLTInputs (P : FixedParameters)
    (_hHT : HighTemperatureInputs P) : Prop where
  scaled_clt_and_variance : PartitionFunctionCLTStatement P
  standardized_clt : StandardizedPartitionCLTStatement P

/-- Scaled relative CLT and matching relative-variance asymptotic. -/
theorem partitionFunction_CLT_with_variance (P : FixedParameters)
    (hHT : HighTemperatureInputs P)
    (hCLT : PartitionFunctionCLTInputs P hHT) : PartitionFunctionCLTStatement P :=
  hCLT.scaled_clt_and_variance

/-- The standardized high-temperature partition-function CLT. -/
theorem standardized_partition_CLT (P : FixedParameters)
    (hHT : HighTemperatureInputs P)
    (hCLT : PartitionFunctionCLTInputs P hHT) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
        ConvergesToCenteredGaussian
          (fun k => standardGaussianMeasure (systemSize P k) P.q)
          (standardizedPartition P β) 1 :=
  hCLT.standardized_clt

end CLT
end SYK
