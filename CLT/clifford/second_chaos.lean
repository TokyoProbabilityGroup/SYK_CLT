import SYK.CLT.clifford.parity_rule
import SYK.CLT.lemmas.exact_second_chaos

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- Exact finite-size first- and second-chaos identification. -/
structure ExactSecondChaosInputs (C : CLTContext) : Prop where
  identification : ∀ k : ℕ, ∀ β : ℝ,
    chaosProjectionExpansion 1 (relativePartition C k β) = 0 ∧
      chaosProjectionExpansion 2 (relativePartition C k β) =
        fun g => radialCoefficient C k β * radialStatistic C k g

theorem secondChaos_relativePartition_eq_radial (C : CLTContext)
    (h : ExactSecondChaosInputs C) (k : ℕ) (β : ℝ) :
    chaosProjectionExpansion 1 (relativePartition C k β) = 0 ∧
      chaosProjectionExpansion 2 (relativePartition C k β) =
        fun g => radialCoefficient C k β * radialStatistic C k g :=
  first_second_chaos_identification C k β (h.identification k β)

end SYK.CLT
