import SYK.Annealed_FE.main_result

set_option autoImplicit false

/-!
# Non-tree bounds lemma

Lean statement of Lemma `lem:nontrees-0` from `refs/SYK-HT-arxiv.tex`.
-/

noncomputable section

namespace SYK
namespace AnnealedFE
namespace Lemmas

/-- The non-tree contribution `B_n(z)` appearing in Lemma `lem:nontrees-0`. -/
constant nonTreeContribution (q : ℕ) (β : ℝ) (n : ℕ) : ℂ → ℂ

/-- Lemma `lem:nontrees-0`: in a sufficiently small high-temperature window,
the non-tree contribution and its derivative are uniformly bounded by `1` on
`|z| ≤ 2`, uniformly in `n ≥ 1`. -/
theorem nontrees_0 (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
    ∃ βstar : ℝ, 0 < βstar ∧
      ∀ β : ℝ, |β| ≤ βstar →
        (∀ n : ℕ, 1 ≤ n → ∀ z : ℂ, ‖z‖ ≤ 2 →
          ‖nonTreeContribution q β n z‖ ≤ 1) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ z : ℂ, ‖z‖ ≤ 2 →
          ‖deriv (nonTreeContribution q β n) z‖ ≤ 1) := by
  sorry

end Lemmas
end AnnealedFE
end SYK
