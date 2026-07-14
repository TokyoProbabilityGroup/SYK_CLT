import SYK.Annealed_FE.main_result

set_option autoImplicit false

/-!
# CCG operator contraction lemma

Lean statement of Lemma `lemma:T-bounded-contraction` from
`refs/SYK-HT-arxiv.tex`.
-/

noncomputable section

namespace SYK
namespace AnnealedFE
namespace Lemmas

/-- Abstract carrier for the paper's Banach space `𝓕_{e,Ω}`. -/
constant CCGFunctionSpace (q : ℕ) : Type

/-- The paper's metric induced by `‖·‖_{e,Ω}` on `𝓕_{e,Ω}`. -/
constant ccgNormDistance {q : ℕ} : CCGFunctionSpace q → CCGFunctionSpace q → ℝ

/-- The fixed-point operator `𝓣`. -/
constant ccgOperator {q : ℕ} : CCGFunctionSpace q → CCGFunctionSpace q

/-- Lemma `lemma:T-bounded-contraction`: the CCG operator maps the function
space into itself and is an `e⁻¹`-contraction for the paper's norm. -/
theorem T_bounded_contraction (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (G₁ G₂ : CCGFunctionSpace q) :
    0 ≤ ccgNormDistance (ccgOperator G₁) (ccgOperator G₂) ∧
      ccgNormDistance (ccgOperator G₁) (ccgOperator G₂) ≤
        Real.exp (-1) * ccgNormDistance G₁ G₂ := by
  sorry

end Lemmas
end AnnealedFE
end SYK
