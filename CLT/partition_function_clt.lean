import SYK.CLT.coefficient_limit
import SYK.CLT.gaussian.radial_clt
import SYK.CLT.lemmas.exact_second_chaos
import SYK.CLT.lemmas.chaos_estimates

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- Assumptions used by the conditional partition-function CLT.

The component estimates are kept separate from the final probabilistic
assembly so their formalization status is visible in one place. -/
structure ConditionalPartitionCLTInputs (C : FixedParameters) : Prop where
  high_temperature : HighTemperatureInputs C
  exact_second_chaos : ExactSecondChaosStatement C
  radial_clt : RadialCLTStatement C
  chaos_estimates : ChaosEstimateInputs C
  conclusions : PartitionFunctionCLTInputs C

/-- Conditional scaled partition-function CLT with variance convergence. -/
theorem partitionFunction_clt_of_inputs (C : FixedParameters)
    (hCLT : ConditionalPartitionCLTInputs C) :
    PartitionFunctionCLTStatement C :=
  hCLT.conclusions.scaled_clt_and_variance

/-- Conditional standardized partition-function CLT. -/
theorem standardizedPartitionFunction_clt_of_inputs (C : FixedParameters)
    (hCLT : ConditionalPartitionCLTInputs C) :
    StandardizedPartitionCLTStatement C :=
  hCLT.conclusions.standardized_clt

/-- The centered log-partition fluctuation on the partition-function CLT scale. -/
noncomputable def scaledLogRelativePartition (C : FixedParameters) (β : ℝ)
    (k : ℕ) (g : CouplingSpace (systemSize C k) C.q) : ℝ :=
  (systemSize C k : ℝ) ^ fluctuationExponent C *
    Real.log (relativePartition C k β g)

/-- Conditional conclusion for the log-partition function. -/
def LogPartitionFunctionCLTStatement (C : FixedParameters) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
      ConvergesToCenteredGaussian
        (fun k => standardGaussianMeasure (systemSize C k) C.q)
        (scaledLogRelativePartition C β)
        ((Nat.factorial C.q : ℝ) / 2 * β ^ 2 *
          limitingPressureDerivative C β ^ 2)

theorem logPartitionFunction_clt_of_inputs (C : FixedParameters)
    (hLog : LogPartitionFunctionCLTStatement C) :
    LogPartitionFunctionCLTStatement C :=
  hLog

end SYK.CLT
