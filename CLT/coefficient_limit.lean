import SYK.CLT.external_inputs

set_option autoImplicit false

noncomputable section

open Topology

namespace SYK.CLT

/-- The deterministic radial-coefficient limit derived from the annealed input. -/
theorem radialCoefficient_limit (C : CLTContext)
    (hHT : HighTemperatureInputs C) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ∈ Set.Ioo (-β₀) β₀,
        Filter.Tendsto
          (fun k => radialCoefficient C k β / systemSize C k)
          Filter.atTop
          (𝓝 (β / 2 * limitingPressureDerivative C β)) :=
  radialCoefficient_asymptotic C hHT

end SYK.CLT
