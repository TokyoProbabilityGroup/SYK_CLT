import SYK.Annealed_FE.main_result

set_option autoImplicit false

/-!
# Equality of hatted and unhatted CCG series

Lean statement of Lemma `lemma:RvsHatR` from `refs/SYK-HT-arxiv.tex`.
-/

noncomputable section

namespace SYK
namespace AnnealedFE
namespace Lemmas

/-- The hatted vertex-pointed CCG function `\hat{𝓡}`. -/
constant ccgHatR (q : ℕ) : ℂ → ℂ

/-- The hatted edge-pointed CCG function `\hat{𝓔}`. -/
constant ccgHatE (q : ℕ) : ℂ → ℂ

/-- Lemma `lemma:RvsHatR`: the hatted and original vertex-/edge-pointed CCG
series agree. -/
theorem R_vs_HatR (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
    (∀ z : ℂ, ccgHatR q z = ccgR q z) ∧
      (∀ z : ℂ, ccgHatE q z = ccgE q z) := by
  sorry

end Lemmas
end AnnealedFE
end SYK
