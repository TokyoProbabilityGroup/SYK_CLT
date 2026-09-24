import SYK.Model.Majorana
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

/-- The standard scale `σ_N` multiplying each standard Gaussian coordinate.
Each actual coefficient `J_A = σ_N g_A` has variance `(q-1)! / N^(q-1)`;
this is the variance of one coefficient, not of the whole Hamiltonian. -/
noncomputable def couplingScale (P : Params) : ℝ :=
  Real.sqrt ((P.q - 1).factorial / (P.N : ℝ) ^ (P.q - 1))

/-- The standard scale is nonnegative. -/
theorem couplingScale_nonneg (P : Params) : 0 ≤ couplingScale P :=
  Real.sqrt_nonneg _

/-- The square of the standard scale is the prescribed coefficient variance. -/
theorem couplingScale_sq (P : Params) :
    couplingScale P ^ 2 = (P.q - 1).factorial / (P.N : ℝ) ^ (P.q - 1) := by
  exact Real.sq_sqrt (by positivity)

/-- The standard SYK Hamiltonian in standard Gaussian coordinates `g_A`. -/
noncomputable def normalizedHamiltonian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g : CouplingSpace P.N P.q) : Matrix d d ℂ :=
  hamiltonian P M (fun I => couplingScale P * g I)

theorem normalizedHamiltonian_affine
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (J V : CouplingSpace P.N P.q) (s : ℝ) :
    normalizedHamiltonian P M (J + s • V) =
      normalizedHamiltonian P M J +
        s • normalizedHamiltonian P M V := by
  classical
  simp only [normalizedHamiltonian, hamiltonian]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _hI
  change ((couplingScale P * (J I + s * V I) : ℝ) : ℂ) •
      M.interactionOperator I =
    ((couplingScale P * J I : ℝ) : ℂ) • M.interactionOperator I +
      s • (((couplingScale P * V I : ℝ) : ℂ) • M.interactionOperator I)
  rw [← smul_assoc, ← add_smul]
  congr 1
  rw [Complex.real_smul]
  push_cast
  ring

/-- The standard Hamiltonian vanishes at the zero coupling vector. -/
@[simp]
theorem normalizedHamiltonian_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ)) :
    normalizedHamiltonian P M 0 = 0 := by
  simp [normalizedHamiltonian, hamiltonian]

/-- The standard Hamiltonian is additive in the Gaussian coordinates. -/
theorem normalizedHamiltonian_add
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g h : CouplingSpace P.N P.q) :
    normalizedHamiltonian P M (g + h) =
      normalizedHamiltonian P M g + normalizedHamiltonian P M h := by
  simpa using normalizedHamiltonian_affine P M g h 1

/-- The standard Hamiltonian commutes with real scalar multiplication. -/
theorem normalizedHamiltonian_smul
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (s : ℝ) (g : CouplingSpace P.N P.q) :
    normalizedHamiltonian P M (s • g) = s • normalizedHamiltonian P M g := by
  simpa using normalizedHamiltonian_affine P M 0 g s

/-- Real Gaussian coefficients give a self-adjoint standard Hamiltonian. -/
theorem normalizedHamiltonian_self_adjoint
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (g : CouplingSpace P.N P.q) :
    star (normalizedHamiltonian P M g) =
      normalizedHamiltonian P M g := by
  exact hamiltonian_self_adjoint P M _

end SYK
