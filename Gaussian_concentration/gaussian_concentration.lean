import SYK.SYK_model.model
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open scoped BigOperators ENNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK

/-- The Euclidean space of real SYK couplings. -/
abbrev CouplingSpace (N q : ℕ) :=
  EuclideanSpace ℝ (InteractionIndex N q)

@[simp]
theorem couplingSpace_card (N q : ℕ) :
    Fintype.card (InteractionIndex N q) = Nat.choose N q := by
  simpa [InteractionIndex] using
    (Fintype.card_finset_len (α := Fin N) q)

/-- The product standard Gaussian measure transported to coupling space. -/
noncomputable def standardGaussianMeasure (N q : ℕ) :
    Measure (CouplingSpace N q) :=
  (Measure.pi fun _ : InteractionIndex N q => gaussianReal 0 1).map
    (WithLp.toLp 2)

/--
Gaussian concentration for the product standard Gaussian on the SYK coupling
space. The coupling space has `Nat.choose N q` coordinates by
`couplingSpace_card`.
-/
theorem gaussian_lipschitz_concentration
    (N q : ℕ) (F : CouplingSpace N q → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasure N q
        {x | |F x - ∫ y, F y ∂standardGaussianMeasure N q| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  sorry

end SYK
