import SYK.Model.Definitions
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real

open scoped ENNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK

/-- The Euclidean space of real SYK couplings. -/
abbrev CouplingSpace (N q : ℕ) :=
  EuclideanSpace ℝ ({s : Finset (Fin N) // s.card = q})

@[simp]
theorem couplingSpace_card (N q : ℕ) :
    Fintype.card ({s : Finset (Fin N) // s.card = q}) = Nat.choose N q := by
  simp

/-- The product standard Gaussian measure transported to coupling space. -/
noncomputable def standardGaussianMeasure (N q : ℕ) :
    Measure (CouplingSpace N q) :=
  (Measure.pi fun _ : ({s : Finset (Fin N) // s.card = q}) => gaussianReal 0 1).map
    (WithLp.toLp 2)

end SYK
