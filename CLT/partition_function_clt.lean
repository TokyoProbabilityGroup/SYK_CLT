import SYK.CLT.coefficient_limit
import SYK.CLT.gaussian.radial_clt
import SYK.CLT.lemmas.exact_second_chaos
import SYK.CLT.lemmas.chaos_estimates
import SYK.CLT.lemmas.partition_clt

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- Assumptions used by the conditional partition-function CLT.

The component estimates are kept separate from the final probabilistic
assembly so their formalization status is visible in one place. -/
structure ConditionalPartitionCLTInputs (C : CLTContext) : Prop where
  high_temperature : HighTemperatureInputs C
  exact_second_chaos : ExactSecondChaosStatement C
  radial_clt : RadialCLTStatement C
  chaos_estimates : ChaosEstimateInputs C
  conclusions : PartitionFunctionCLTInputs C

/-- Conditional scaled partition-function CLT with variance convergence. -/
theorem partitionFunction_clt_of_inputs (C : CLTContext)
    (hCLT : ConditionalPartitionCLTInputs C) :
    PartitionFunctionCLTStatement C :=
  hCLT.conclusions.scaled_clt_and_variance

/-- Conditional standardized partition-function CLT. -/
theorem standardizedPartitionFunction_clt_of_inputs (C : CLTContext)
    (hCLT : ConditionalPartitionCLTInputs C) :
    StandardizedPartitionCLTStatement C :=
  hCLT.conclusions.standardized_clt

end SYK.CLT
