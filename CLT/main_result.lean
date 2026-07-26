import SYK.CLT.lemmas.partition_clt

set_option autoImplicit false

/-!
# High-temperature central limit theorem for the SYK partition function

This is the paper-facing entry point for `refs/CLT_SYK.tex`.  The finite model
and all notation are in `SYK.CLT.definitions`; the internal argument is split
among the files under `SYK/CLT/lemmas`.
-/

noncomputable section

namespace SYK
namespace CLT

/-- The high-temperature standardized central limit theorem. -/
theorem main_result (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
        ConvergesToCenteredGaussian
          (fun k => standardGaussianMeasure (systemSize P k) P.q)
          (standardizedPartition P β) 1 :=
  standardized_partition_CLT P

end CLT
end SYK
