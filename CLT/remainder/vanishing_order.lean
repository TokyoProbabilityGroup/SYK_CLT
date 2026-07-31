import SYK.CLT.gaussian.chaos_decomposition

set_option autoImplicit false

namespace SYK.CLT

/-- A component vanishes to at least order `r` when it factors by `z ^ r`. -/
def VanishesToOrderAtLeast {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (G : ℂ → H) (r : ℕ) : Prop :=
  ∃ V : ℂ → H, ∀ z, G z = z ^ r • V z

end SYK.CLT
