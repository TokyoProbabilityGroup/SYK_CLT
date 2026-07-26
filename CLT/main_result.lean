import SYK.CLT.lemmas.convex_derivative
import SYK.CLT.lemmas.hermite_gauge_selection
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false

/-!
# Central limit theorem for the high-temperature SYK partition function

This file formalizes the statement and proof interface of `refs/CLT_SYK.tex`.
The finite-volume Hamiltonian is the one from `SYK.SYK_model.model`; in
particular, the normalization is

`sqrt ((q - 1)! / N^(q - 1)) * ∑ I, g I * ψ I`.

The random variables for different values of `N` live on different Gaussian
coupling spaces.  For that reason, convergence in distribution is expressed
through characteristic functions.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ComplexConjugate NNReal

namespace SYK
namespace CLT

/-! ## Fixed interaction order and admissible system sizes -/

/-- A fixed even interaction order in the range of the preprint. -/
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

/-- The positive exponent `a = q / 2 - 1` used in the fluctuation scale. -/
def fluctuationExponent (P : FixedParameters) : ℕ :=
  P.q / 2 - 1

/-- Parameters used to call the repository's SYK Hamiltonian. -/
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

/-- A fixed concrete Majorana representation for every system size. -/
noncomputable def matrixMajorana (N : ℕ) :
    MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) ℂ) :=
  Classical.choice (exists_majoranaSystem N)

/-! ## Gaussian SYK partition function -/

/-- The Gaussian Hamiltonian `H_N(g)` with the normalization in the preprint.

This is an adapter around `SYK.normalizedHamiltonian` from `model.lean`.
-/
noncomputable def gaussianHamiltonian (P : FixedParameters) (k : ℕ)
    (g : CouplingSpace (systemSize P k) P.q) :
    Matrix (HilbertIndex (systemSize P k)) (HilbertIndex (systemSize P k)) ℂ :=
  normalizedHamiltonian (modelParameters P k)
    (matrixMajorana (systemSize P k)) 1 g

theorem gaussianHamiltonian_selfAdjoint (P : FixedParameters) (k : ℕ)
    (g : CouplingSpace (systemSize P k) P.q) :
    star (gaussianHamiltonian P k g) = gaussianHamiltonian P k g := by
  exact normalizedHamiltonian_self_adjoint
    (modelParameters P k) (matrixMajorana (systemSize P k)) 1 g

/-- The normalized matrix trace `2^(-N/2) Tr`. -/
noncomputable def normalizedTrace {N : ℕ}
    (A : Matrix (HilbertIndex N) (HilbertIndex N) ℂ) : ℂ :=
  (Fintype.card (HilbertIndex N) : ℂ)⁻¹ * Matrix.trace A

/-- The complex-temperature partition function
`Z_N(z;g) = tr(exp(-z H_N(g)))`. -/
noncomputable def partitionFunctionC (P : FixedParameters) (k : ℕ)
    (z : ℂ) (g : CouplingSpace (systemSize P k) P.q) : ℂ :=
  normalizedTrace (NormedSpace.exp (-(z • gaussianHamiltonian P k g)))

/-- The real partition function, obtained by restricting the complex one. -/
noncomputable def partitionFunctionR (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  (partitionFunctionC P k (β : ℂ) g).re

/-- The annealed complex partition function `F_N(z) = E Z_N(z)`. -/
noncomputable def annealedPartitionC (P : FixedParameters) (k : ℕ)
    (z : ℂ) : ℂ :=
  ∫ g, partitionFunctionC P k z g
    ∂standardGaussianMeasure (systemSize P k) P.q

/-- The real restriction of the annealed partition function. -/
noncomputable def annealedPartitionR (P : FixedParameters) (k : ℕ)
    (β : ℝ) : ℝ :=
  ∫ g, partitionFunctionR P k β g
    ∂standardGaussianMeasure (systemSize P k) P.q

theorem annealedPartitionR_eq_complex_re (P : FixedParameters) (k : ℕ)
    (β : ℝ) :
    annealedPartitionR P k β =
      (annealedPartitionC P k (β : ℂ)).re := by
  sorry

/-- The relative partition function `Y_N = Z_N / F_N`. -/
noncomputable def relativePartition (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  partitionFunctionR P k β g / annealedPartitionR P k β

/-- The finite-volume annealed pressure `N⁻¹ log F_N`. -/
noncomputable def annealedPressure (P : FixedParameters) (k : ℕ)
    (β : ℝ) : ℝ :=
  Real.log (annealedPartitionR P k β) / systemSize P k

/-- A selected pointwise limit of the finite-volume annealed pressures. -/
noncomputable def limitingAnnealedPressure (P : FixedParameters) (β : ℝ) : ℝ :=
  limUnder atTop (fun k => annealedPressure P k β)

/-- The derivative `ell_q'` appearing in the limiting variance. -/
noncomputable def limitingPressureDerivative (P : FixedParameters) (β : ℝ) : ℝ :=
  deriv (limitingAnnealedPressure P) β

/-! ## Exact radial projection and its remainder -/

/-- The number `M_N = choose N q` of interaction labels. -/
def interactionCount (P : FixedParameters) (k : ℕ) : ℕ :=
  Nat.choose (systemSize P k) P.q

/-- The centered radial statistic
`Q_N = M_N⁻¹ ∑ I, (g_I² - 1)`. -/
noncomputable def radialStatistic (P : FixedParameters) (k : ℕ)
    (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  (interactionCount P k : ℝ)⁻¹ *
    ∑ I : InteractionIndex (systemSize P k) P.q, (g I) ^ 2 - 1

/-- The exact finite-volume Feng--Tian--Wei coefficient
`A_N(β) = β/2 * ∂β log F_N(β)`. -/
noncomputable def radialCoefficient (P : FixedParameters) (k : ℕ)
    (β : ℝ) : ℝ :=
  β / 2 * deriv (fun t => Real.log (annealedPartitionR P k t)) β

/-- The part of `Y_N - 1` left after subtracting its radial second chaos. -/
noncomputable def higherChaosRemainder (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  relativePartition P k β g - 1 -
    radialCoefficient P k β * radialStatistic P k g

theorem exact_FTW_decomposition (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) :
    relativePartition P k β g - 1 =
      radialCoefficient P k β * radialStatistic P k g +
        higherChaosRemainder P k β g := by
  simp [higherChaosRemainder]

/-! ## Analytic and finite-chaos inputs from the preprint -/

/-- The complex zero-free and second-moment input on a fixed disk. -/
theorem complex_secondMoment_input (P : FixedParameters) :
    ∃ R C : ℝ, ∃ k₀ : ℕ,
      0 < R ∧ 0 ≤ C ∧
      ∀ k ≥ k₀, ∀ z : ℂ, ‖z‖ ≤ R →
        annealedPartitionC P k z ≠ 0 ∧
        (∫ g,
            ‖partitionFunctionC P k z g / annealedPartitionC P k z - 1‖ ^ 2
              ∂standardGaussianMeasure (systemSize P k) P.q) ≤
          C / (systemSize P k : ℝ) ^ fluctuationExponent P := by
  sorry

/-- Exact identification of the first and second Gaussian chaoses.

The first chaos vanishes.  The second chaos is the radial term appearing in
`exact_FTW_decomposition`.
-/
theorem first_second_chaos_identification (P : FixedParameters) (k : ℕ)
    (β : ℝ) :
    chaosProjectionExpansion 1 (relativePartition P k β) = 0 ∧
      chaosProjectionExpansion 2 (relativePartition P k β) =
        fun g => radialCoefficient P k β * radialStatistic P k g := by
  sorry

/-- The higher-chaos remainder is negligible on the CLT scale. -/
theorem higher_chaos_closure (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, |β| < β₀ →
        Tendsto
          (fun k =>
            (systemSize P k : ℝ) ^ (P.q - 2) *
              ∫ g, higherChaosRemainder P k β g ^ 2
                ∂standardGaussianMeasure (systemSize P k) P.q)
          atTop (𝓝 0) := by
  sorry

/-! ## Annealed free energy and the deterministic coefficient -/

/-- High-temperature annealed pressure convergence, including convergence of
its derivative. -/
theorem annealed_pressure_and_derivative_limit (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      AnalyticOnNhd ℝ (limitingAnnealedPressure P) (Set.Ioo (-β₀) β₀) ∧
      (∀ β ∈ Set.Ioo (-β₀) β₀,
        limitingAnnealedPressure P (-β) = limitingAnnealedPressure P β) ∧
      (∀ β ∈ Set.Ioo (-β₀) β₀,
        Tendsto (fun k => annealedPressure P k β) atTop
          (𝓝 (limitingAnnealedPressure P β))) ∧
      (∀ β ∈ Set.Ioo (-β₀) β₀,
        Tendsto
          (fun k =>
            deriv (fun t => Real.log (annealedPartitionR P k t)) β /
              systemSize P k)
          atTop (𝓝 (limitingPressureDerivative P β))) ∧
      Tendsto
        (fun β => limitingPressureDerivative P β / β)
        (𝓝[≠] 0) (𝓝 ((P.q : ℝ)⁻¹)) := by
  sorry

theorem radialCoefficient_asymptotic (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ∈ Set.Ioo (-β₀) β₀,
        Tendsto
          (fun k => radialCoefficient P k β / systemSize P k)
          atTop
          (𝓝 (β / 2 * limitingPressureDerivative P β)) := by
  sorry

/-! ## Distributional statements -/

/-- Convergence to a centered Gaussian law of variance `v`, expressed by
pointwise convergence of characteristic functions. -/
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

/-- The partition function centered and normalized by its standard deviation. -/
noncomputable def standardizedPartition (P : FixedParameters) (β : ℝ)
    (k : ℕ) (g : CouplingSpace (systemSize P k) P.q) : ℝ :=
  (partitionFunctionR P k β g - annealedPartitionR P k β) /
    Real.sqrt
      (variance (partitionFunctionR P k β)
        (standardGaussianMeasure (systemSize P k) P.q))

/-- Scaled relative CLT and matching relative-variance asymptotic. -/
theorem partitionFunction_CLT_with_variance (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
        ConvergesToCenteredGaussian
          (fun k => standardGaussianMeasure (systemSize P k) P.q)
          (scaledRelativePartition P β)
          ((Nat.factorial P.q : ℝ) / 2 * β ^ 2 *
            limitingPressureDerivative P β ^ 2) ∧
        Tendsto
          (fun k =>
            (systemSize P k : ℝ) ^ (P.q - 2) *
              variance (partitionFunctionR P k β)
                (standardGaussianMeasure (systemSize P k) P.q) /
              annealedPartitionR P k β ^ 2)
          atTop
          (𝓝 ((Nat.factorial P.q : ℝ) / 2 * β ^ 2 *
            limitingPressureDerivative P β ^ 2)) := by
  sorry

/-- The high-temperature standardized central limit theorem from
`CLT_SYK.tex`. -/
theorem main_result (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
        ConvergesToCenteredGaussian
          (fun k => standardGaussianMeasure (systemSize P k) P.q)
          (standardizedPartition P β) 1 := by
  sorry

end CLT
end SYK
