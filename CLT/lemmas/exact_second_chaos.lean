import SYK.CLT.definitions
import SYK.CLT.lemmas.hermite_gauge_selection

set_option autoImplicit false

noncomputable section

namespace SYK
namespace CLT

/-!
The sign-gauge argument eliminates the first chaos and forces the second chaos
to be radial.  The coefficient is then obtained by Gaussian integration by
parts and the scaling identity `Z(β; tg) = Z(tβ; g)`.
-/

/-- Exact finite-size identification of the first and second Gaussian chaoses. -/
def ExactSecondChaosStatement (P : FixedParameters) : Prop :=
  ∀ k : ℕ, ∀ β : ℝ,
    chaosProjectionExpansion 1 (relativePartition P k β) = 0 ∧
      chaosProjectionExpansion 2 (relativePartition P k β) =
        fun g => radialCoefficient P k β * radialStatistic P k g

end CLT
end SYK
