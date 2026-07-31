import SYK.CLT.clifford.second_chaos
import SYK.CLT.coefficient_limit
import SYK.CLT.gaussian.radial_clt
import SYK.CLT.remainder.higher_chaos_closure
import SYK.CLT.lemmas.partition_clt

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- All internal components required after the external analytic inputs. -/
structure ConditionalPartitionCLTInputs (C : CLTContext)
    (hHT : HighTemperatureInputs C) : Prop where
  exact_second_chaos : ExactSecondChaosInputs C
  radial : RadialCLTInputs C
  higher_chaos : HigherChaosInputs C hHT
  probabilistic_assembly : PartitionFunctionCLTInputs C hHT

/-- Conditional scaled partition-function CLT with variance convergence. -/
theorem partitionFunction_clt_of_inputs (C : CLTContext)
    (hHT : HighTemperatureInputs C)
    (hCLT : ConditionalPartitionCLTInputs C hHT) :
    PartitionFunctionCLTStatement C :=
  partitionFunction_CLT_with_variance C hHT hCLT.probabilistic_assembly

/-- Conditional standardized partition-function CLT. -/
theorem standardizedPartitionFunction_clt_of_inputs (C : CLTContext)
    (hHT : HighTemperatureInputs C)
    (hCLT : ConditionalPartitionCLTInputs C hHT) :
    StandardizedPartitionCLTStatement C :=
  standardized_partition_CLT C hHT hCLT.probabilistic_assembly

end SYK.CLT
