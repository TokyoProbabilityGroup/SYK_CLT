import SYK.super_concentration.super_conc
import SYK.SYK_model.model
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false

/-!
# Definitions for the SYK partition-function CLT

The model adapter in this file uses `SYK.normalizedHamiltonian` from
`SYK.SYK_model.model`.  Random variables at different system sizes have
different Gaussian sample spaces, so Gaussian convergence is recorded through
characteristic functions.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ComplexConjugate NNReal

namespace SYK
namespace CLT

/-- A fixed even interaction order in the range of the CLT. -/
structure FixedParameters where
  q : ℕ
  q_even : Even q
  four_le_q : 4 ≤ q

/-- System sizes tend to infinity through even integers, starting at `q`. -/
def systemSize (P : FixedParameters) (k : ℕ) : ℕ :=
  P.q + 2 * k

theorem systemSize_even (P : FixedParameters) (k : ℕ) :
    Even (systemSize P k) := by
  rcases P.q_even with ⟨m, hm⟩
  refine ⟨m + k, ?_⟩
  unfold systemSize
  omega

theorem q_le_systemSize (P : FixedParameters) (k : ℕ) :
    P.q ≤ systemSize P k := by
  simp [systemSize]

theorem tendsto_systemSize_atTop (P : FixedParameters) :
    Tendsto (systemSize P) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with k hk
  simp only [systemSize]
  omega

/-- The positive exponent `a = q / 2 - 1`. -/
def fluctuationExponent (P : FixedParameters) : ℕ :=
  P.q / 2 - 1

/-- Parameters used to call the repository's Hamiltonian. -/
def modelParameters (P : FixedParameters) (k : ℕ) : Params where
  N := systemSize P k
  q := P.q
  q_even := P.q_even
  q_pos := lt_of_lt_of_le (by omega) P.four_le_q
  q_le_N := q_le_systemSize P k
  β := 0
  β_nonneg := le_rfl

/-- The standard irreducible matrix size for `N` Majorana generators. -/
abbrev HilbertIndex (N : ℕ) := Fin (2 ^ (N / 2))

/-- Existence of a concrete matrix representation of the Majorana relations. -/
theorem exists_majoranaSystem (N : ℕ) :
    Nonempty (MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) ℂ)) := by
  sorry

/-- A fixed concrete Majorana representation. -/
noncomputable def matrixMajorana (N : ℕ) :
    MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) ℂ) :=
  Classical.choice (exists_majoranaSystem N)

/-- The Gaussian Hamiltonian with coupling variance
`(q - 1)! / N^(q - 1)`. -/
noncomputable def gaussianHamiltonian (P : FixedParameters) (k : ℕ)
    (g : CouplingSpace (systemSize P k) P.q) :
    Matrix (HilbertIndex (systemSize P k)) (HilbertIndex (systemSize P k)) ℂ :=
  normalizedHamiltonian (modelParameters P k)
    (matrixMajorana (systemSize P k)) 1 g

/-- The normalized matrix trace `2^(-N/2) Tr`. -/
noncomputable def normalizedTrace {N : ℕ}
    (A : Matrix (HilbertIndex N) (HilbertIndex N) ℂ) : ℂ :=
  (Fintype.card (HilbertIndex N) : ℂ)⁻¹ * Matrix.trace A

/-- The complex-temperature partition function
`Z_N(z;g) = tr(exp(-z H_N(g)))`. -/
noncomputable def partitionFunctionC (P : FixedParameters) (k : ℕ)
    (z : ℂ) (g : CouplingSpace (systemSize P k) P.q) : ℂ :=
  normalizedTrace (NormedSpace.exp (-(z • gaussianHamiltonian P k g)))

/-- The real-temperature partition function. -/
noncomputable def partitionFunctionR (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  (partitionFunctionC P k (β : ℂ) g).re

/-- The annealed complex partition function `F_N(z) = E Z_N(z)`. -/
noncomputable def annealedPartitionC (P : FixedParameters) (k : ℕ)
    (z : ℂ) : ℂ :=
  ∫ g, partitionFunctionC P k z g
    ∂standardGaussianMeasure (systemSize P k) P.q

/-- The real annealed partition function, defined directly as an expectation. -/
noncomputable def annealedPartitionR (P : FixedParameters) (k : ℕ)
    (β : ℝ) : ℝ :=
  ∫ g, partitionFunctionR P k β g
    ∂standardGaussianMeasure (systemSize P k) P.q

/-- The relative partition function `Y_N = Z_N / F_N`. -/
noncomputable def relativePartition (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  partitionFunctionR P k β g / annealedPartitionR P k β

/-- The finite-volume annealed pressure `N⁻¹ log F_N`. -/
noncomputable def annealedPressure (P : FixedParameters) (k : ℕ)
    (β : ℝ) : ℝ :=
  Real.log (annealedPartitionR P k β) / systemSize P k

/-- A selected pointwise limit of the annealed pressures. -/
noncomputable def limitingAnnealedPressure (P : FixedParameters) (β : ℝ) : ℝ :=
  limUnder atTop (fun k => annealedPressure P k β)

/-- The derivative `ell_q'` appearing in the limiting variance. -/
noncomputable def limitingPressureDerivative (P : FixedParameters) (β : ℝ) : ℝ :=
  deriv (limitingAnnealedPressure P) β

/-- The number `M_N = choose N q` of interaction labels. -/
def interactionCount (P : FixedParameters) (k : ℕ) : ℕ :=
  Nat.choose (systemSize P k) P.q

/-- The centered radial statistic
`Q_N = M_N⁻¹ ∑ I, (g_I² - 1)`. -/
noncomputable def radialStatistic (P : FixedParameters) (k : ℕ)
    (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  (interactionCount P k : ℝ)⁻¹ *
    ∑ I : InteractionIndex (systemSize P k) P.q, (g I) ^ 2 - 1

/-- The exact finite-volume radial coefficient
`A_N(β) = β/2 * ∂β log F_N(β)`. -/
noncomputable def radialCoefficient (P : FixedParameters) (k : ℕ)
    (β : ℝ) : ℝ :=
  β / 2 * deriv (fun t => Real.log (annealedPartitionR P k t)) β

/-- The part of `Y_N - 1` left after subtracting its radial second chaos. -/
noncomputable def higherChaosRemainder (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  relativePartition P k β g - 1 -
    radialCoefficient P k β * radialStatistic P k g

/-- Convergence to a centered Gaussian law of variance `v`, expressed through
characteristic functions. -/
def ConvergesToCenteredGaussian
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (μ : (k : ℕ) → Measure (Ω k))
    (X : (k : ℕ) → Ω k → ℝ) (v : ℝ) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun k =>
        ∫ ω,
          Complex.exp (Complex.I * ((t * X k ω : ℝ) : ℂ)) ∂μ k)
      atTop
      (𝓝 (Complex.exp (-(((v * t ^ 2 / 2 : ℝ) : ℂ)))))

/-- The relative partition function at its natural fluctuation scale. -/
noncomputable def scaledRelativePartition (P : FixedParameters) (β : ℝ)
    (k : ℕ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  (systemSize P k : ℝ) ^ fluctuationExponent P *
    (relativePartition P k β g - 1)

/-- The centered partition function normalized by its standard deviation. -/
noncomputable def standardizedPartition (P : FixedParameters) (β : ℝ)
    (k : ℕ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  (partitionFunctionR P k β g - annealedPartitionR P k β) /
    Real.sqrt
      (variance (partitionFunctionR P k β)
        (standardGaussianMeasure (systemSize P k) P.q))

end CLT
end SYK
