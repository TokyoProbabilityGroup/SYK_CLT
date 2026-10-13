module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

public section

/-!
# Parameters and interaction labels of the SYK model

`Params` records the number of Majorana generators `N` and the interaction order
`q`, with `q` even, positive and at most `N`; it carries no inverse temperature.
An interaction label is a `q`-element subset of `Fin N`, and `orderedIndices`
lists its elements in increasing order, which fixes the order of the Majorana
product in `SYK.Model.Majorana`.
-/

namespace SYK

/-- Parameters of an SYK model. -/
structure Params where
  /-- The number of Majorana operators. -/
  N : ℕ
  /-- The interaction order. -/
  q : ℕ
  /-- The interaction order is even. -/
  q_even : Even q
  /-- The interaction order is positive. -/
  q_pos : 0 < q
  /-- An interaction involves at most all `N` operators. -/
  q_le_N : q ≤ N

/-- A label for a `q`-body interaction is a `q`-element subset of the fermion labels. -/
abbrev InteractionIndex (N q : ℕ) := {s : Finset (Fin N) // s.card = q}

/-- The elements of an interaction index in their canonical increasing order. -/
@[expose] def orderedIndices {N q : ℕ} (s : InteractionIndex N q) : List (Fin N) :=
  s.1.sort (· ≤ ·)

@[simp]
theorem length_orderedIndices {N q : ℕ} (s : InteractionIndex N q) :
    (orderedIndices s).length = q := by
  simp [orderedIndices, s.2]

end SYK
