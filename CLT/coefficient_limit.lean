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
          (𝓝 (β / 2 * limitingPressureDerivative C β)) := by
  obtain ⟨β₀, hβ₀, _, _, _, hderiv, _⟩ := hHT.annealed_limit
  refine ⟨β₀, hβ₀, fun β hβ => ?_⟩
  have h := hderiv β hβ
  simpa only [radialCoefficient, div_eq_mul_inv, mul_assoc] using
    ((tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => β / 2) Filter.atTop (𝓝 (β / 2))).mul h)

end SYK.CLT
