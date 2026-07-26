import SYK.CLT.definitions
import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace SYK
namespace CLT

/-!
Hilbert-valued analytic suppression for high chaos orders.

Each component has a zero whose order is at least its chaos order.  A boundary
second-moment bound therefore gains a geometric factor when evaluated on a
smaller disk.
-/

/-- Abstract analytic suppression estimate used above logarithmic chaos
order. -/
theorem analytic_suppression_high_components
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℕ → ℂ → H) (R C : ℝ) (m : ℕ) (w : ℂ)
    (hR : 0 < R) (hw : ‖w‖ < R) (hC : 0 ≤ C)
    (hfactor :
      ∀ r : ℕ, ∃ V : ℂ → H,
        AnalyticOnNhd ℂ V (Metric.closedBall 0 R) ∧
          ∀ z ∈ Metric.closedBall (0 : ℂ) R, G r z = z ^ r • V z)
    (hsummable :
      ∀ z : ℂ, ‖z‖ = R → Summable (fun r => ‖G r z‖ ^ 2))
    (hboundary :
      ∀ z : ℂ, ‖z‖ = R → ∑' r : ℕ, ‖G r z‖ ^ 2 ≤ C) :
    (∑' r : ℕ, if m < r then ‖G r w‖ ^ 2 else 0) ≤
      ((‖w‖ / R) ^ (2 * (m + 1)) /
        (1 - (‖w‖ / R) ^ 2)) * C := by
  sorry

end CLT
end SYK
