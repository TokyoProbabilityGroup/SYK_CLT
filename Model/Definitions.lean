import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Trace

namespace SYK

/-- Parameters of an SYK model. -/
structure Params where
  N : ℕ
  q : ℕ
  q_even : Even q
  q_pos : 0 < q
  q_le_N : q ≤ N

/-- A label for a `q`-body interaction is a `q`-element subset of the fermion labels. -/
abbrev InteractionIndex (N q : ℕ) := {s : Finset (Fin N) // s.card = q}

/-- The elements of an interaction index in their canonical increasing order. -/
def orderedIndices {N q : ℕ} (s : InteractionIndex N q) : List (Fin N) :=
  s.1.sort (· ≤ ·)

@[simp]
theorem length_orderedIndices {N q : ℕ} (s : InteractionIndex N q) :
    (orderedIndices s).length = q := by
  simp [orderedIndices, s.2]

end SYK
