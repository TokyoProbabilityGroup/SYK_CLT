import SYK.Model.Definitions
import SYK.Probability.GaussianConcentration.StandardGaussian

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
  GaussianConcentration.standardGaussianMeasureOnEuclidean
    ({s : Finset (Fin N) // s.card = q})

/-- The coupling-space measure is definitionally the generic finite-dimensional
standard Gaussian measure. -/
@[simp]
theorem standardGaussianMeasure_eq_onEuclidean (N q : ℕ) :
    standardGaussianMeasure N q =
      GaussianConcentration.standardGaussianMeasureOnEuclidean
        ({s : Finset (Fin N) // s.card = q}) := rfl

end SYK
