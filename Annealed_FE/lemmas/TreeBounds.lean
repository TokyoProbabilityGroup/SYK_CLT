import SYK.Annealed_FE.main_result

set_option autoImplicit false

/-!
# Tree bounds lemma

Lean statement of Lemma `lem:treebounds-0` from `refs/SYK-HT-arxiv.tex`.
-/

noncomputable section

open Metric

namespace SYK
namespace AnnealedFE
namespace Lemmas

/-- Lemma `lem:treebounds-0`: for every tolerance `c > 0`, sufficiently small
inverse temperature makes the hypertree series analytic on `|z| ≤ 2`, close to
`z`, with first derivative close to `1` and controlled second derivative. -/
theorem treebounds_0 (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    {c : ℝ} (hc : 0 < c) :
    ∃ βstar : ℝ, 0 < βstar ∧
      ∀ β : ℝ, |β| ≤ βstar →
        AnalyticOnNhd ℂ (phiC q β) (closedBall 0 2) ∧
        (∀ z : ℂ, ‖z‖ ≤ 2 → ‖phiC q β z - z‖ ≤ c) ∧
        (∀ z : ℂ, ‖z‖ ≤ 2 → ‖deriv (phiC q β) z - 1‖ ≤ c) ∧
        (∀ z : ℂ, ‖z‖ ≤ 2 → ‖z‖ ^ 2 * ‖deriv (deriv (phiC q β)) z‖ ≤ c) := by
  sorry

end Lemmas
end AnnealedFE
end SYK
