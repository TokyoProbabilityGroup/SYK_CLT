import SYK.CLT.partition_function_clt
import SYK.CLT.log_partition_function_clt

set_option autoImplicit false

/-!
# High-temperature central limit theorem for the SYK partition function

This is the paper-facing entry point for `refs/CLT_SYK.tex`.  It only assembles
and exports declarations proved in imported modules.
-/

noncomputable section

namespace SYK
namespace CLT

/-- Compatibility alias for the conditional standardized theorem. -/
theorem main_result (C : CLTContext)
    (hHT : HighTemperatureInputs C)
    (hCLT : ConditionalPartitionCLTInputs C hHT) :
    StandardizedPartitionCLTStatement C :=
  standardizedPartitionFunction_clt_of_inputs C hHT hCLT

#print axioms partitionFunction_clt_of_inputs
#print axioms standardizedPartitionFunction_clt_of_inputs
#print axioms logPartitionFunction_clt_of_inputs

end CLT
end SYK
