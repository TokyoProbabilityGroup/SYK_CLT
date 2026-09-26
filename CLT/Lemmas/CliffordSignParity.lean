import SYK.Model.Majorana
import SYK.Model.FiniteDimensionalGibbs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SYK

namespace MajoranaSystem

variable {N : ℕ} {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (M : MajoranaSystem N A)

theorem listProduct_mul_reverse (l : List (Fin N)) :
    (l.map M.ψ).prod * (l.reverse.map M.ψ).prod = 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (l.map M.ψ).prod, ih, one_mul, M.majorana_sq]

/-- The interaction index consisting of all labels except `x`. -/
def complementIndex (x : Fin N) : InteractionIndex N (N - 1) :=
  ⟨Finset.univ.erase x, by simp⟩

/-- The product of all generators except `ψ x` (a single-coordinate reflection). -/
noncomputable def reflection (x : Fin N) : A := M.psiProduct (complementIndex x)

/-- The inverse of `reflection x`. -/
noncomputable def reflectionInv (x : Fin N) : A :=
  ((orderedIndices (complementIndex x)).reverse.map M.ψ).prod

theorem reflection_mul_inv (x : Fin N) : M.reflection x * M.reflectionInv x = 1 :=
  M.listProduct_mul_reverse _

theorem reflectionInv_mul (x : Fin N) : M.reflectionInv x * M.reflection x = 1 := by
  have := M.listProduct_mul_reverse (orderedIndices (complementIndex x)).reverse
  rw [List.reverse_reverse] at this
  exact this

theorem reflection_mul_generator (hN : Even N) (x j : Fin N) :
    M.reflection x * M.ψ j =
      (if j = x then (-1 : ℂ) else 1) • (M.ψ j * M.reflection x) := by
  by_cases hjx : j = x
  · subst hjx
    have hnot : j ∉ orderedIndices (complementIndex j) := by
      simp [orderedIndices, complementIndex]
    have h := M.listProduct_mul_generator j (orderedIndices (complementIndex j)) hnot
    rw [length_orderedIndices] at h
    have hodd : Odd (N - 1) := by
      have := j.pos
      obtain ⟨m, hm⟩ := hN
      exact ⟨m - 1, by omega⟩
    rw [hodd.neg_one_pow] at h
    simpa [reflection, psiProduct] using h
  · have hmem : j ∈ (complementIndex x).1 := by simp [complementIndex, hjx]
    have h := M.psiProduct_mul_generator_of_mem (complementIndex x) j hmem
    have hev : Even (N - 1 - 1) := by
      obtain ⟨m, hm⟩ := hN
      exact ⟨m - 1, by omega⟩
    rw [hev.neg_one_pow] at h
    simpa [reflection, hjx] using h

/-- For every set `S` of labels there is an invertible element conjugating
`ψ j` to `-ψ j` for `j ∈ S` and fixing `ψ j` otherwise. -/
theorem exists_gauge (hN : Even N) (S : Finset (Fin N)) :
    ∃ U V : A, U * V = 1 ∧ V * U = 1 ∧
      ∀ j, U * M.ψ j = (if j ∈ S then (-1 : ℂ) else 1) • (M.ψ j * U) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 1, by simp, by simp, fun j => by simp⟩
  | @insert x S hx ih =>
    obtain ⟨U, V, hUV, hVU, hU⟩ := ih
    refine ⟨M.reflection x * U, V * M.reflectionInv x, ?_, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc U, hUV, one_mul, M.reflection_mul_inv]
    · rw [mul_assoc, ← mul_assoc (M.reflectionInv x), M.reflectionInv_mul, one_mul, hVU]
    · intro j
      rw [mul_assoc, hU j, Algebra.mul_smul_comm, ← mul_assoc, M.reflection_mul_generator hN,
        Algebra.smul_mul_assoc, smul_smul, mul_assoc]
      congr 1
      by_cases hj : j = x
      · subst hj; simp [hx]
      · simp [hj]

theorem mul_listProduct {U : A} {ε : Fin N → ℂ}
    (h : ∀ j, U * M.ψ j = ε j • (M.ψ j * U)) (l : List (Fin N)) :
    U * (l.map M.ψ).prod = (l.map ε).prod • ((l.map M.ψ).prod * U) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, h i, Algebra.smul_mul_assoc, mul_assoc, ih, Algebra.mul_smul_comm,
      smul_smul, mul_assoc]

theorem mul_interactionOperator {q : ℕ} {U : A} {ε : Fin N → ℂ}
    (h : ∀ j, U * M.ψ j = ε j • (M.ψ j * U)) (s : InteractionIndex N q) :
    U * M.interactionOperator s = (∏ j ∈ s.1, ε j) • (M.interactionOperator s * U) := by
  have hl := M.mul_listProduct h (orderedIndices s)
  have hprod : ((orderedIndices s).map ε).prod = ∏ j ∈ s.1, ε j := by
    rw [← List.prod_toFinset _ (by simp [orderedIndices])]
    simp [orderedIndices]
  rw [hprod] at hl
  change U * M.psiProduct s = _ • (M.psiProduct s * U) at hl
  rw [interactionOperator, Algebra.mul_smul_comm, hl, Algebra.smul_mul_assoc, smul_comm]

end MajoranaSystem

/-- The sign character `χ_s(I) = ∏_{x ∈ I} s_x`. -/
def signCharacter {N q : ℕ} (s : Fin N → ℝ) (I : InteractionIndex N q) : ℝ :=
  ∏ x ∈ I.1, s x

/-- Conjugation of the Hamiltonian by a gauge element. -/
theorem hamiltonian_gauge {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (P : Params) (hN : Even P.N) (M : MajoranaSystem P.N A) (J : InteractionIndex P.N P.q → ℝ)
    (s : Fin P.N → ℝ) (hs : ∀ x, s x = 1 ∨ s x = -1) :
    ∃ U V : A, U * V = 1 ∧ V * U = 1 ∧
      hamiltonian P M (fun I => signCharacter s I * J I) = U * hamiltonian P M J * V := by
  classical
  obtain ⟨U, V, hUV, hVU, hU⟩ := M.exists_gauge hN (Finset.univ.filter fun x => s x = -1)
  have hε : ∀ j, (if j ∈ Finset.univ.filter (fun x => s x = -1) then (-1 : ℂ) else 1) =
      ((s j : ℝ) : ℂ) := by
    intro j
    rcases hs j with h | h <;> norm_num [h]
  simp only [hε] at hU
  refine ⟨U, V, hUV, hVU, ?_⟩
  have key : U * hamiltonian P M J =
      hamiltonian P M (fun I => signCharacter s I * J I) * U := by
    rw [hamiltonian, hamiltonian, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Algebra.mul_smul_comm, M.mul_interactionOperator hU, smul_smul,
      Algebra.smul_mul_assoc]
    congr 1
    simp [signCharacter, mul_comm]
  rw [key, mul_assoc, hUV, mul_one]

/-- **Sign-gauge invariance** of the partition function:
`Z_N(β; G) = Z_N(β; (χ_s(I) g_I)_I)` for every `s ∈ {±1}^N`, when `N` is even. -/
theorem partitionFunction_sign_gauge {n : Type*} [Fintype n] [DecidableEq n]
    (P : Params) (hN : Even P.N) (M : MajoranaSystem P.N (Matrix n n ℂ)) (β : ℝ)
    (J : InteractionIndex P.N P.q → ℝ) (s : Fin P.N → ℝ) (hs : ∀ x, s x = 1 ∨ s x = -1) :
    SYK.partitionFunction (β : ℂ) (hamiltonian P M J) =
      SYK.partitionFunction (β : ℂ)
        (hamiltonian P M (fun I => signCharacter s I * J I)) := by
  obtain ⟨U, V, hUV, hVU, hH⟩ := hamiltonian_gauge P hN M J s hs
  have hunit : IsUnit U := ⟨⟨U, V, hUV, hVU⟩, rfl⟩
  have hinv : U⁻¹ = V := Matrix.inv_eq_right_inv hUV
  simp only [SYK.partitionFunction, gibbsOperator]
  rw [hH]
  have : -(β : ℂ) • (U * hamiltonian P M J * V) = U * (-(β : ℂ) • hamiltonian P M J) * U⁻¹ := by
    rw [hinv, Matrix.mul_smul, Matrix.smul_mul]
  rw [this, Matrix.exp_conj _ _ hunit, hinv, Matrix.trace_mul_comm, ← mul_assoc, hVU, one_mul]

/-! ### Multi-indices, Hermite polynomials and the Gaussian expectation -/

/-- A multi-index `α` is even if `∑_{I ∋ x} α_I` is even for every `x ∈ [N]`. -/
def IsEvenMultiIndex {N q : ℕ} (α : InteractionIndex N q → ℕ) : Prop :=
  ∀ x : Fin N, Even (∑ I with x ∈ I.1, α I)

/-- A multi-index is odd if it is not even. -/
def IsOddMultiIndex {N q : ℕ} (α : InteractionIndex N q → ℕ) : Prop :=
  ¬ IsEvenMultiIndex α

/-- The multivariate (probabilists') Hermite polynomial `H_α(g) = ∏_I He_{α_I}(g_I)`. -/
noncomputable def hermiteMulti {ι : Type*} [Fintype ι] (α : ι → ℕ) (g : ι → ℝ) : ℝ :=
  ∏ I, Polynomial.aeval (g I) (Polynomial.hermite (α I))

/-- The law of the couplings: i.i.d. standard Gaussians. -/
noncomputable def gaussianCouplings (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

theorem hermite_aeval_neg (n : ℕ) (x : ℝ) :
    Polynomial.aeval (-x) (Polynomial.hermite n) =
      (-1) ^ n * Polynomial.aeval x (Polynomial.hermite n) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hodd : Odd (n + i)
  · simp [Polynomial.coeff_hermite_of_odd_add hodd]
  · have hev : Even (n + i) := Nat.not_odd_iff_even.mp hodd
    have hsign : ((-1 : ℝ)) ^ i = (-1) ^ n := by
      rcases Nat.even_or_odd n with hn | hn
      · have : Even i := by
          rcases Nat.even_or_odd i with hi | hi
          · exact hi
          · exact absurd (hn.add_odd hi) hodd
        rw [hn.neg_one_pow, this.neg_one_pow]
      · have : Odd i := by
          rcases Nat.even_or_odd i with hi | hi
          · exact absurd (hn.add_even hi) hodd
          · exact hi
        rw [hn.neg_one_pow, this.neg_one_pow]
    rw [neg_pow, hsign, zsmul_eq_mul, zsmul_eq_mul]
    ring

theorem hermite_aeval_sign (n : ℕ) (c x : ℝ) (hc : c = 1 ∨ c = -1) :
    Polynomial.aeval (c * x) (Polynomial.hermite n) =
      c ^ n * Polynomial.aeval x (Polynomial.hermite n) := by
  rcases hc with rfl | rfl
  · simp
  · rw [neg_one_mul, hermite_aeval_neg]

/-- Flipping the sign of the coordinates is measure preserving for i.i.d. Gaussians. -/
theorem integral_gaussianCouplings_sign {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (F : (ι → ℝ) → ℂ) :
    ∫ g, F (fun i => c i * g i) ∂gaussianCouplings ι = ∫ g, F g ∂gaussianCouplings ι := by
  have hsq : ∀ i, c i * c i = 1 := fun i => by rcases hc i with h | h <;> simp [h]
  let e1 : ∀ i, ℝ ≃ᵐ ℝ := fun i =>
    { toFun := fun x => c i * x
      invFun := fun x => c i * x
      left_inv := fun x => by simp only [← mul_assoc, hsq, one_mul]
      right_inv := fun x => by simp only [← mul_assoc, hsq, one_mul]
      measurable_toFun := measurable_const_mul (c i)
      measurable_invFun := measurable_const_mul (c i) }
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.piCongrRight e1
  have hmp : MeasurePreserving e (gaussianCouplings ι) (gaussianCouplings ι) := by
    refine measurePreserving_pi (f := fun i x => c i * x) _ _ fun i => ?_
    rcases hc i with h | h
    · simp only [h, one_mul]
      exact MeasurePreserving.id _
    · simp only [h, neg_one_mul]
      exact ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
  exact hmp.integral_comp' F

/-- **Parity rule.** If `α` is odd (and `N` is even), then `𝔼[Z_N(β; G) H_α(G)] = 0`
for i.i.d. standard Gaussian couplings `G`. -/
theorem expectation_partitionFunction_mul_hermite_eq_zero {n : Type*} [Fintype n]
    [DecidableEq n] (P : Params) (hN : Even P.N) (M : MajoranaSystem P.N (Matrix n n ℂ))
    (β : ℝ) (α : InteractionIndex P.N P.q → ℕ) (hα : IsOddMultiIndex α) :
    ∫ g, SYK.partitionFunction (β : ℂ) (hamiltonian P M g) * (hermiteMulti α g : ℂ)
      ∂gaussianCouplings (InteractionIndex P.N P.q) = 0 := by
  classical
  have hex : ∃ x : Fin P.N, Odd (∑ I with x ∈ I.1, α I) := by
    by_contra h
    push Not at h
    exact hα fun x => Nat.not_odd_iff_even.mp (h x)
  obtain ⟨x, hx⟩ := hex
  set s : Fin P.N → ℝ := fun y => if y = x then -1 else 1 with hs_def
  have hs : ∀ y, s y = 1 ∨ s y = -1 := fun y => by
    by_cases h : y = x <;> simp [hs_def, h]
  set c : InteractionIndex P.N P.q → ℝ := fun I => if x ∈ I.1 then -1 else 1 with hc_def
  have hc : ∀ I, c I = 1 ∨ c I = -1 := fun I => by
    by_cases h : x ∈ I.1 <;> simp [hc_def, h]
  have hsc : ∀ I, signCharacter s I = c I := fun I => by
    simp only [signCharacter, hs_def, hc_def]
    rw [Finset.prod_ite_eq']
  have hZ : ∀ g, SYK.partitionFunction (β : ℂ) (hamiltonian P M (fun I => c I * g I)) =
      SYK.partitionFunction (β : ℂ) (hamiltonian P M g) :=
    fun g => by
      rw [partitionFunction_sign_gauge P hN M β g s hs]
      simp only [hsc]
  have hH : ∀ g, hermiteMulti α (fun I => c I * g I) = -hermiteMulti α g := fun g => by
    simp only [hermiteMulti]
    simp only [fun I => hermite_aeval_sign (α I) (c I) (g I) (hc I)]
    rw [Finset.prod_mul_distrib]
    have : ∏ I, c I ^ α I = -1 := by
      have h1 : ∀ I, c I ^ α I = (-1 : ℝ) ^ (if x ∈ I.1 then α I else 0) := fun I => by
        by_cases h : x ∈ I.1 <;> simp [hc_def, h]
      simp only [h1]
      rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter, hx.neg_one_pow]
    rw [this, neg_one_mul]
  have key := integral_gaussianCouplings_sign c hc
    (fun g => SYK.partitionFunction (β : ℂ) (hamiltonian P M g) *
      (hermiteMulti α g : ℂ))
  simp only [hZ, hH, Complex.ofReal_neg, mul_neg, integral_neg] at key
  linear_combination -key / 2
end SYK
