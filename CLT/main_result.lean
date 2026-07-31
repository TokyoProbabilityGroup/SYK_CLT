import SYK.CLT.partition_function_clt

set_option autoImplicit false

/-!
# High-temperature central limit theorem for the SYK partition function

This is the paper-facing entry point for `refs/CLT_SYK.tex`.  It only assembles
and exports declarations proved in imported modules.
-/

noncomputable section

namespace SYK
namespace CLT

/-- The conditional standardized partition-function CLT. -/
theorem main_result (C : FixedParameters)
    (hCLT : ConditionalPartitionCLTInputs C) :
    StandardizedPartitionCLTStatement C :=
  standardizedPartitionFunction_clt_of_inputs C hCLT

end CLT
end SYK
