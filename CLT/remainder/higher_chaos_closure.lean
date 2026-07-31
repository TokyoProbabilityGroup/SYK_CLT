import SYK.CLT.external_inputs
import SYK.CLT.remainder.analytic_tail
import SYK.CLT.remainder.low_chaos
import SYK.CLT.remainder.vanishing_order

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Topology

namespace SYK.CLT

/-- Negligibility of the chaos remainder at the partition-function CLT scale. -/
def HigherChaosClosureStatement (C : CLTContext) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ β : ℝ, |β| < β₀ →
      Tendsto
        (fun k =>
          (systemSize C k : ℝ) ^ (C.q - 2) *
            ∫ g, higherChaosRemainder C k β g ^ 2
              ∂standardGaussianMeasure (systemSize C k) C.q)
        atTop (𝓝 0)

/-- Explicit interface for the analytic-tail closure argument. -/
structure HigherChaosInputs (C : CLTContext)
    (_hHT : HighTemperatureInputs C) : Prop where
  closure : HigherChaosClosureStatement C

theorem higher_chaos_negligible (C : CLTContext)
    (hHT : HighTemperatureInputs C) (h : HigherChaosInputs C hHT) :
    HigherChaosClosureStatement C :=
  higher_chaos_closure C h.closure

end SYK.CLT
