import SYK.CLT.gaussian.hermite

set_option autoImplicit false

namespace SYK.CLT

/-- The parity condition used by the finite incidence count. -/
def IsEvenMultiIndex {N q : ℕ} (alpha : MultiIndex N q) : Prop :=
  ∀ a : Fin N, Even (vertexMultiplicity alpha a)

end SYK.CLT
