import SYK.CLT.remainder.duhamel_bound
import SYK.CLT.remainder.even_tuple_count

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace SYK.CLT

/-- Uniform finite-chaos bound used below logarithmic order. -/
def LowChaosEstimateStatement (C : CLTContext) (β : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ k r : ℕ, 1 ≤ r →
      (∫ g, chaosProjectionExpansion r (relativePartition C k β) g ^ 2
          ∂standardGaussianMeasure (systemSize C k) C.q) ≤
        Real.exp (D * r * Real.log (r + 1)) /
          (systemSize C k : ℝ) ^ (fluctuationExponent C * r)

/-- Explicit interface for the low-chaos estimate. -/
structure LowChaosInputs (C : CLTContext) : Prop where
  estimate : ∀ β : ℝ, LowChaosEstimateStatement C β

theorem low_chaos_negligible (C : CLTContext) (h : LowChaosInputs C)
    (β : ℝ) : LowChaosEstimateStatement C β :=
  logarithmic_chaos_estimate C β (h.estimate β)

end SYK.CLT
