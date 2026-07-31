import SYK.CLT.lemmas.analytic_chaos_tail
import SYK.CLT.lemmas.exact_second_chaos
import SYK.CLT.lemmas.external_inputs

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Topology

namespace SYK
namespace CLT

/-!
Internal estimates from the modified Feng--Tian--Wei argument.

The first result is the iterated Duhamel derivative estimate.  The second is
the parity-count estimate up to logarithmic chaos order.  The final result
combines that estimate with analytic suppression of the remaining chaoses.
-/

/-- Real-temperature derivative bound from the iterated Duhamel formula. -/
theorem partition_derivative_bound (P : FixedParameters) (k r : ℕ)
    (β : ℝ) (alpha : MultiIndex (systemSize P k) P.q)
    (halpha : multiIndexDegree alpha = r)
    (g : CouplingSpace (systemSize P k) P.q)
    (hbound :
      |multiIndexDerivative alpha (partitionFunctionR P k β) g| ≤
        (|β| * couplingScale (modelParameters P k) 1) ^ r *
          partitionFunctionR P k β g) :
    |multiIndexDerivative alpha (partitionFunctionR P k β) g| ≤
      (|β| * couplingScale (modelParameters P k) 1) ^ r *
        partitionFunctionR P k β g :=
  hbound

/-- Uniform finite-chaos estimate through logarithmic order. -/
theorem logarithmic_chaos_estimate (P : FixedParameters) (β : ℝ)
    (hestimate :
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ k r : ℕ, 1 ≤ r →
          (∫ g, chaosProjectionExpansion r (relativePartition P k β) g ^ 2
              ∂standardGaussianMeasure (systemSize P k) P.q) ≤
            Real.exp (D * r * Real.log (r + 1)) /
              (systemSize P k : ℝ) ^ (fluctuationExponent P * r)) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ k r : ℕ, 1 ≤ r →
        (∫ g, chaosProjectionExpansion r (relativePartition P k β) g ^ 2
            ∂standardGaussianMeasure (systemSize P k) P.q) ≤
          Real.exp (D * r * Real.log (r + 1)) /
            (systemSize P k : ℝ) ^ (fluctuationExponent P * r) :=
  hestimate

/-- The higher-chaos remainder is negligible on the CLT scale. -/
theorem higher_chaos_closure (P : FixedParameters)
    (hclosure :
      ∃ β₀ : ℝ, 0 < β₀ ∧
        ∀ β : ℝ, |β| < β₀ →
          Tendsto
            (fun k =>
              (systemSize P k : ℝ) ^ (P.q - 2) *
                ∫ g, higherChaosRemainder P k β g ^ 2
                  ∂standardGaussianMeasure (systemSize P k) P.q)
            atTop (𝓝 0)) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, |β| < β₀ →
        Tendsto
          (fun k =>
            (systemSize P k : ℝ) ^ (P.q - 2) *
              ∫ g, higherChaosRemainder P k β g ^ 2
                ∂standardGaussianMeasure (systemSize P k) P.q)
          atTop (𝓝 0) :=
  hclosure

end CLT
end SYK
