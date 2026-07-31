import SYK.super_concentration.super_conc
import SYK.SYK_model.model
import Mathlib.LinearAlgebra.Matrix.Kronecker
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
open scoped BigOperators ComplexConjugate Kronecker NNReal

namespace SYK
namespace CLT

/-- A fixed even interaction order in the range of the CLT. -/
structure FixedParameters where
  q : ℕ
  q_even : Even q
  four_le_q : 4 ≤ q

/-- Parameters fixed throughout the partition-function CLT. -/
abbrev CLTContext := FixedParameters

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

private def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

private def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

private def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

private lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply]

private lemma pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Complex.I_mul_I]

private lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply]

private lemma pauliX_pauliY :
    pauliX * pauliY = -(pauliY * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, Matrix.mul_apply]

private lemma pauliZ_pauliX :
    pauliZ * pauliX = -(pauliX * pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply]

private lemma pauliZ_pauliY :
    pauliZ * pauliY = -(pauliY * pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, pauliZ, Matrix.mul_apply]

private lemma star_pauliX : star pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, star, Matrix.conjTranspose] <;>
    norm_num [Complex.ext_iff]

private lemma star_pauliY : star pauliY = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, star, Matrix.conjTranspose] <;>
    norm_num [Complex.ext_iff]

private lemma star_pauliZ : star pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, star, Matrix.conjTranspose] <;>
    norm_num [Complex.ext_iff]

private def pauliMajorana :
    MajoranaSystem 2 (Matrix (Fin 2) (Fin 2) ℂ) where
  ψ i := ![pauliX, pauliY] i
  majorana_rel i j := by
    fin_cases i <;> fin_cases j <;>
      simp [pauliX_sq, pauliY_sq, pauliX_pauliY] <;>
      norm_num
  self_adjoint i := by
    fin_cases i <;> simp [star_pauliX, star_pauliY]

private lemma pauliZ_anticommute (i : Fin 2) :
    pauliZ * pauliMajorana.ψ i =
      -(pauliMajorana.ψ i * pauliZ) := by
  fin_cases i <;>
    simp [pauliMajorana, pauliZ_pauliX, pauliZ_pauliY]

private def extendedPsi
    {N : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (M : MajoranaSystem N (Matrix d d ℂ)) :
    Fin N ⊕ Fin 2 → Matrix (Fin 2 × d) (Fin 2 × d) ℂ
  | Sum.inl i => pauliZ ⊗ₖ M.ψ i
  | Sum.inr i => pauliMajorana.ψ i ⊗ₖ 1

private lemma extendedPsi_rel
    {N : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (M : MajoranaSystem N (Matrix d d ℂ))
    (i j : Fin N ⊕ Fin 2) :
    extendedPsi M i * extendedPsi M j +
        extendedPsi M j * extendedPsi M i =
      if i = j then 2 else 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [extendedPsi]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            ← Matrix.kronecker_add, pauliZ_sq, M.majorana_rel]
          by_cases h : i = j
          · subst j
            simp only [if_pos]
            simpa using
              (Matrix.natCast_kronecker_natCast
                (α := ℂ) (m := Fin 2) (n := d) 1 2)
          · simp [h]
      | inr j =>
          simp only [extendedPsi]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          rw [Matrix.mul_one, Matrix.one_mul]
          rw [pauliZ_anticommute]
          rw [← Matrix.add_kronecker]
          simp
  | inr i =>
      cases j with
      | inl j =>
          simp only [extendedPsi]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          rw [Matrix.one_mul, Matrix.mul_one]
          rw [pauliZ_anticommute]
          rw [← Matrix.add_kronecker]
          simp
      | inr j =>
          simp only [extendedPsi]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            ← Matrix.add_kronecker, pauliMajorana.majorana_rel]
          by_cases h : i = j
          · subst j
            simp only [if_pos]
            rw [Matrix.mul_one]
            simpa using
              (Matrix.natCast_kronecker_natCast
                (α := ℂ) (m := Fin 2) (n := d) 2 1)
          · simp [h]

private lemma star_extendedPsi
    {N : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (M : MajoranaSystem N (Matrix d d ℂ))
    (i : Fin N ⊕ Fin 2) :
    star (extendedPsi M i) = extendedPsi M i := by
  cases i with
  | inl i =>
      simp only [extendedPsi]
      change (pauliZ ⊗ₖ M.ψ i).conjTranspose = _
      rw [Matrix.conjTranspose_kronecker]
      change (star pauliZ) ⊗ₖ star (M.ψ i) = _
      rw [star_pauliZ, M.self_adjoint]
  | inr i =>
      simp only [extendedPsi]
      change (pauliMajorana.ψ i ⊗ₖ
        (1 : Matrix d d ℂ)).conjTranspose = _
      rw [Matrix.conjTranspose_kronecker]
      change star (pauliMajorana.ψ i) ⊗ₖ
        star (1 : Matrix d d ℂ) = _
      rw [pauliMajorana.self_adjoint]
      simp

private def addTwoMajorana
    {N : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (M : MajoranaSystem N (Matrix d d ℂ)) :
    MajoranaSystem (N + 2)
      (Matrix (Fin 2 × d) (Fin 2 × d) ℂ) where
  ψ i := extendedPsi M (finSumFinEquiv.symm i)
  majorana_rel i j := by
    simpa using
      extendedPsi_rel M (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  self_adjoint i := star_extendedPsi M (finSumFinEquiv.symm i)

private def zeroMajorana :
    MajoranaSystem 0 (Matrix (Fin 1) (Fin 1) ℂ) where
  ψ i := Fin.elim0 i
  majorana_rel i := Fin.elim0 i
  self_adjoint i := Fin.elim0 i

private def oneMajorana :
    MajoranaSystem 1 (Matrix (Fin 1) (Fin 1) ℂ) where
  ψ _ := 1
  majorana_rel i j := by
    have h : i = j := Subsingleton.elim _ _
    subst j
    norm_num
  self_adjoint _ := by simp

private def reindexMajorana
    {N : ℕ} {d e : Type*}
    [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (M : MajoranaSystem N (Matrix d d ℂ)) (f : d ≃ e) :
    MajoranaSystem N (Matrix e e ℂ) where
  ψ i := Matrix.reindexAlgEquiv ℂ ℂ f (M.ψ i)
  majorana_rel i j := by
    let E := Matrix.reindexAlgEquiv ℂ ℂ f
    change E (M.ψ i) * E (M.ψ j) +
        E (M.ψ j) * E (M.ψ i) = _
    rw [← map_mul, ← map_mul, ← map_add, M.majorana_rel]
    by_cases h : i = j <;> simp [h, map_ofNat]
  self_adjoint i := by
    change star (Matrix.reindex f f (M.ψ i)) =
      Matrix.reindex f f (M.ψ i)
    change (Matrix.reindex f f (M.ψ i)).conjTranspose =
      Matrix.reindex f f (M.ψ i)
    rw [Matrix.conjTranspose_reindex]
    change Matrix.reindex f f (star (M.ψ i)) =
      Matrix.reindex f f (M.ψ i)
    rw [M.self_adjoint]

private theorem exists_majoranaAux (N : ℕ) :
    ∃ d : Type, ∃ _ : Fintype d, ∃ _ : DecidableEq d,
      Fintype.card d = 2 ^ (N / 2) ∧
        Nonempty (MajoranaSystem N (Matrix d d ℂ)) := by
  induction N using Nat.twoStepInduction with
  | zero =>
      exact ⟨Fin 1, inferInstance, inferInstance, by norm_num,
        ⟨zeroMajorana⟩⟩
  | one =>
      exact ⟨Fin 1, inferInstance, inferInstance, by norm_num,
        ⟨oneMajorana⟩⟩
  | more N ih _ =>
      rcases ih with ⟨d, hdFintype, hdDecidableEq, hdcard, ⟨M⟩⟩
      letI : Fintype d := hdFintype
      letI : DecidableEq d := hdDecidableEq
      refine ⟨Fin 2 × d, inferInstance, inferInstance, ?_,
        ⟨addTwoMajorana M⟩⟩
      rw [Fintype.card_prod, Fintype.card_fin, hdcard]
      have hdiv : (N + 2) / 2 = N / 2 + 1 := by omega
      rw [hdiv, pow_succ]
      ac_rfl

/-- Existence of a concrete matrix representation of the Majorana relations. -/
theorem exists_majoranaSystem (N : ℕ) :
    Nonempty (MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) ℂ)) := by
  rcases exists_majoranaAux N with
    ⟨d, hdFintype, hdDecidableEq, hdcard, ⟨M⟩⟩
  letI : Fintype d := hdFintype
  letI : DecidableEq d := hdDecidableEq
  let e : d ≃ HilbertIndex N :=
    Fintype.equivFinOfCardEq hdcard
  exact ⟨reindexMajorana M e⟩

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
