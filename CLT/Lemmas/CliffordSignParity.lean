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

/-- An invertible Clifford element exchanges two generators under conjugation.
It negates all other generators. For even interaction order, this realizes a
transposition of interaction labels up to signs. -/
theorem exists_generator_swap (i j : Fin N) (hij : i ≠ j) :
    ∃ U V : A, U * V = 1 ∧ V * U = 1 ∧
      U * M.ψ i = M.ψ j * U ∧
      U * M.ψ j = M.ψ i * U ∧
      ∀ k, k ≠ i → k ≠ j → U * M.ψ k = -(M.ψ k * U) := by
  let U : A := M.ψ i + M.ψ j
  let V : A := (1 / 2 : ℂ) • U
  have hanti : M.ψ i * M.ψ j + M.ψ j * M.ψ i = 0 := by
    simpa [hij] using M.majorana_rel i j
  have hU2 : U * U = (2 : A) := by
    dsimp [U]
    calc
      (M.ψ i + M.ψ j) * (M.ψ i + M.ψ j) =
          (M.ψ i * M.ψ i + M.ψ j * M.ψ j) +
            (M.ψ i * M.ψ j + M.ψ j * M.ψ i) := by noncomm_ring
      _ = 2 := by
        rw [M.majorana_sq, M.majorana_sq, hanti]
        norm_num
  have hhalf : (1 / 2 : ℂ) • (2 : A) = 1 := by
    have htwo : (2 : A) = (2 : ℂ) • (1 : A) := by
      simp only [two_smul]
      norm_num
    rw [htwo, smul_smul]
    norm_num
  have hUV : U * V = 1 := by
    change U * ((1 / 2 : ℂ) • U) = 1
    rw [Algebra.mul_smul_comm, hU2]
    exact hhalf
  have hVU : V * U = 1 := by
    change ((1 / 2 : ℂ) • U) * U = 1
    rw [Algebra.smul_mul_assoc, hU2]
    exact hhalf
  refine ⟨U, V, hUV, hVU, ?_, ?_, ?_⟩
  · dsimp [U]
    simp only [add_mul, mul_add, M.majorana_sq]
    abel
  · dsimp [U]
    simp only [add_mul, mul_add, M.majorana_sq]
    abel
  · intro k hki hkj
    dsimp [U]
    rw [add_mul, mul_add, M.anticommute (Ne.symm hki),
      M.anticommute (Ne.symm hkj)]
    abel

/-- Reordering a word of Majorana generators changes it by a sign. -/
theorem listProduct_eq_sign_smul_of_perm
    (l₁ l₂ : List (Fin N)) (h : l₁.Perm l₂) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      (l₁.map M.ψ).prod = c • (l₂.map M.ψ).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | @cons i l₁ l₂ _ ih =>
      obtain ⟨c, hc, heq⟩ := ih
      refine ⟨c, hc, ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [heq, Algebra.mul_smul_comm]
  | @swap i j l =>
      by_cases hij : i = j
      · subst j
        exact ⟨1, Or.inl rfl, by simp⟩
      · refine ⟨-1, Or.inr rfl, ?_⟩
        simp only [List.map_cons, List.prod_cons]
        calc
          M.ψ j * (M.ψ i * (l.map M.ψ).prod) =
              (M.ψ j * M.ψ i) * (l.map M.ψ).prod := by rw [mul_assoc]
          _ = (-(M.ψ i * M.ψ j)) * (l.map M.ψ).prod := by
              rw [M.anticommute (Ne.symm hij)]
          _ = (-1 : ℂ) • (M.ψ i * (M.ψ j * (l.map M.ψ).prod)) := by
              simp [mul_assoc]
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
      obtain ⟨c₁, hc₁, heq₁⟩ := ih₁
      obtain ⟨c₂, hc₂, heq₂⟩ := ih₂
      refine ⟨c₁ * c₂, ?_, ?_⟩
      · rcases hc₁ with h₁ | h₁ <;> rcases hc₂ with h₂ | h₂ <;>
          simp [h₁, h₂]
      · rw [heq₁, heq₂, smul_smul]

/-- The swap conjugation as a signed permutation of generator labels. -/
theorem exists_generator_swap_action (i j : Fin N) (hij : i ≠ j) :
    ∃ U V : A, U * V = 1 ∧ V * U = 1 ∧
      ∀ k : Fin N,
        U * M.ψ k =
          (if k = i ∨ k = j then (1 : ℂ) else -1) •
            (M.ψ (Equiv.swap i j k) * U) := by
  obtain ⟨U, V, hUV, hVU, hi, hj, hother⟩ := M.exists_generator_swap i j hij
  refine ⟨U, V, hUV, hVU, ?_⟩
  intro k
  by_cases hki : k = i
  · subst k
    simpa [hij] using hi
  by_cases hkj : k = j
  · subst k
    simpa [hij] using hj
  simpa [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj] using
    hother k hki hkj

/-- Move the swap element through a Majorana word. -/
theorem mul_listProduct_swap {U : A} (i j : Fin N)
    (hU : ∀ k : Fin N,
      U * M.ψ k =
        (if k = i ∨ k = j then (1 : ℂ) else -1) •
          (M.ψ (Equiv.swap i j k) * U)) (l : List (Fin N)) :
    U * (l.map M.ψ).prod =
      ((l.map fun k => if k = i ∨ k = j then (1 : ℂ) else -1).prod) •
        ((l.map (fun k => M.ψ (Equiv.swap i j k))).prod * U) := by
  induction l with
  | nil => simp
  | cons k l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← mul_assoc, hU k, Algebra.smul_mul_assoc, mul_assoc, ih,
        Algebra.mul_smul_comm, smul_smul, mul_assoc]

/-- Relabel an interaction by exchanging two Majorana labels. -/
def swapInteractionIndex {q : ℕ} (i j : Fin N) (s : InteractionIndex N q) :
    InteractionIndex N q :=
  ⟨s.1.image (Equiv.swap i j), by
    rw [Finset.card_image_of_injective _ (Equiv.swap i j).injective, s.2]⟩

theorem swapInteractionIndex_swap {q : ℕ} (i j : Fin N)
    (s : InteractionIndex N q) :
    swapInteractionIndex i j (swapInteractionIndex i j s) = s := by
  apply Subtype.ext
  simp [swapInteractionIndex, Finset.image_image, Function.comp_def]

def swapInteractionEquiv {q : ℕ} (i j : Fin N) :
    InteractionIndex N q ≃ InteractionIndex N q where
  toFun := swapInteractionIndex i j
  invFun := swapInteractionIndex i j
  left_inv := swapInteractionIndex_swap i j
  right_inv := swapInteractionIndex_swap i j

theorem orderedIndices_swap_perm {q : ℕ} (i j : Fin N)
    (s : InteractionIndex N q) :
    ((orderedIndices s).map (Equiv.swap i j)).Perm
      (orderedIndices (swapInteractionIndex i j s)) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (Finset.sort_nodup _ _).map (Equiv.swap i j).injective
  · exact Finset.sort_nodup _ _
  · ext k
    simp [orderedIndices, swapInteractionIndex]

/-- Swapping two generator labels carries each interaction word to the
relabelled interaction word, up to a real sign. -/
theorem psiProduct_swap {q : ℕ} {U : A} (i j : Fin N)
    (hU : ∀ k : Fin N,
      U * M.ψ k =
        (if k = i ∨ k = j then (1 : ℂ) else -1) •
          (M.ψ (Equiv.swap i j k) * U)) (s : InteractionIndex N q) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      U * M.psiProduct s =
        c • (M.psiProduct (swapInteractionIndex i j s) * U) := by
  let ε : Fin N → ℂ := fun k => if k = i ∨ k = j then 1 else -1
  have hε (l : List (Fin N)) : (l.map ε).prod = 1 ∨ (l.map ε).prod = -1 := by
    induction l with
    | nil => simp
    | cons k l ih =>
        rcases ih with ih | ih <;> by_cases hk : k = i ∨ k = j <;>
          simp [ε, hk, ih]
  have hword := M.mul_listProduct_swap i j hU (orderedIndices s)
  obtain ⟨c, hc, hreorder⟩ := M.listProduct_eq_sign_smul_of_perm
    ((orderedIndices s).map (Equiv.swap i j))
    (orderedIndices (swapInteractionIndex i j s))
    (orderedIndices_swap_perm i j s)
  have hreorder' :
      ((orderedIndices s).map (fun k => M.ψ (Equiv.swap i j k))).prod =
        c • ((orderedIndices (swapInteractionIndex i j s)).map M.ψ).prod := by
    simpa only [List.map_map, Function.comp_def] using hreorder
  refine ⟨(orderedIndices s |>.map ε).prod * c, ?_, ?_⟩
  · rcases hε (orderedIndices s) with h | h <;> rcases hc with hc | hc <;>
      simp [h, hc]
  · change U * (orderedIndices s |>.map M.ψ).prod = _
    rw [hword]
    change _ = _ • ((orderedIndices (swapInteractionIndex i j s) |>.map M.ψ).prod * U)
    rw [hreorder', Algebra.smul_mul_assoc, smul_smul]

theorem interactionOperator_swap {q : ℕ} {U : A} (i j : Fin N)
    (hU : ∀ k : Fin N,
      U * M.ψ k =
        (if k = i ∨ k = j then (1 : ℂ) else -1) •
          (M.ψ (Equiv.swap i j k) * U)) (s : InteractionIndex N q) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      U * M.interactionOperator s =
        c • (M.interactionOperator (swapInteractionIndex i j s) * U) := by
  obtain ⟨c, hc, hpsi⟩ := M.psiProduct_swap i j hU s
  refine ⟨c, hc, ?_⟩
  simp only [interactionOperator, Algebra.mul_smul_comm, hpsi,
    Algebra.smul_mul_assoc]
  rw [smul_comm]

/-- A single choice of real signs for every interaction under a generator swap. -/
theorem exists_interaction_swap_sign {q : ℕ} {U : A} (i j : Fin N)
    (hU : ∀ k : Fin N,
      U * M.ψ k =
        (if k = i ∨ k = j then (1 : ℂ) else -1) •
          (M.ψ (Equiv.swap i j k) * U)) :
    ∃ c : InteractionIndex N q → ℝ,
      (∀ s, c s = 1 ∨ c s = -1) ∧
      ∀ s, U * M.interactionOperator s =
        (c s : ℂ) • (M.interactionOperator (swapInteractionIndex i j s) * U) := by
  classical
  have h (s : InteractionIndex N q) : ∃ r : ℝ,
      (r = 1 ∨ r = -1) ∧
      U * M.interactionOperator s =
        (r : ℂ) • (M.interactionOperator (swapInteractionIndex i j s) * U) := by
    obtain ⟨c, hc, heq⟩ := M.interactionOperator_swap i j hU s
    rcases hc with hc | hc
    · exact ⟨1, Or.inl rfl, by simpa [hc] using heq⟩
    · exact ⟨-1, Or.inr rfl, by simpa [hc] using heq⟩
  choose c hc heq using h
  exact ⟨c, hc, heq⟩

/-- A signed relabelling of couplings conjugates the finite interaction sum. -/
theorem interactionSum_swap {q : ℕ} (i j : Fin N)
    (U V : A) (hUV : U * V = 1)
    (c J : InteractionIndex N q → ℝ)
    (hO : ∀ s, U * M.interactionOperator s =
      (c s : ℂ) • (M.interactionOperator (swapInteractionIndex i j s) * U)) :
    U * (∑ s : InteractionIndex N q,
        (J s : ℂ) • M.interactionOperator s) * V =
      ∑ s : InteractionIndex N q,
        ((c (swapInteractionIndex i j s) * J (swapInteractionIndex i j s) : ℝ) : ℂ) •
          M.interactionOperator s := by
  classical
  have hterm (s : InteractionIndex N q) :
      U * ((J s : ℂ) • M.interactionOperator s) * V =
        ((J s * c s : ℝ) : ℂ) •
          M.interactionOperator (swapInteractionIndex i j s) := by
    rw [Algebra.mul_smul_comm, hO s, smul_smul,
      Algebra.smul_mul_assoc, mul_assoc, hUV, mul_one]
    congr 1
    exact (Complex.ofReal_mul _ _).symm
  calc
    U * (∑ s : InteractionIndex N q,
        (J s : ℂ) • M.interactionOperator s) * V =
        ∑ s : InteractionIndex N q,
          U * ((J s : ℂ) • M.interactionOperator s) * V := by
            rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ s : InteractionIndex N q,
          ((J s * c s : ℝ) : ℂ) •
            M.interactionOperator (swapInteractionIndex i j s) := by
            exact Finset.sum_congr rfl (fun s _ => hterm s)
    _ = ∑ s : InteractionIndex N q,
          ((c (swapInteractionIndex i j s) * J (swapInteractionIndex i j s) : ℝ) : ℂ) •
            M.interactionOperator s := by
            apply Fintype.sum_equiv (swapInteractionEquiv i j)
            intro s
            simp [swapInteractionEquiv, swapInteractionIndex_swap, mul_comm]

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

/-- Relabelling the two selected Majorana generators induces a signed
permutation of the Gaussian interaction coordinates. -/
theorem hamiltonian_swap (P : Params) {A : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (M : MajoranaSystem P.N A) (i j : Fin P.N) (hij : i ≠ j) :
    ∃ c : InteractionIndex P.N P.q → ℝ,
      (∀ s, c s = 1 ∨ c s = -1) ∧
      ∃ U V : A, U * V = 1 ∧ V * U = 1 ∧
        ∀ J : InteractionIndex P.N P.q → ℝ,
          hamiltonian P M
            (fun s => c s * J (MajoranaSystem.swapInteractionIndex i j s)) =
            U * hamiltonian P M J * V := by
  obtain ⟨U, V, hUV, hVU, hU⟩ := M.exists_generator_swap_action i j hij
  obtain ⟨c, hc, hO⟩ := M.exists_interaction_swap_sign i j hU
  refine ⟨fun s => c (MajoranaSystem.swapInteractionIndex i j s),
    fun s => hc _, U, V, hUV, hVU, ?_⟩
  intro J
  exact (M.interactionSum_swap i j U V hUV c J hO).symm

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

/-- Vertex transposition invariance of the finite partition function, with
the signs required by the canonical ordering of interaction words. -/
theorem partitionFunction_swap {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (i j : Fin P.N) (hij : i ≠ j) (β : ℝ) :
    ∃ c : InteractionIndex P.N P.q → ℝ,
      (∀ s, c s = 1 ∨ c s = -1) ∧
      ∀ J : InteractionIndex P.N P.q → ℝ,
        SYK.partitionFunction (β : ℂ)
          (hamiltonian P M
            (fun s => c s * J (MajoranaSystem.swapInteractionIndex i j s))) =
          SYK.partitionFunction (β : ℂ) (hamiltonian P M J) := by
  obtain ⟨c, hc, U, V, hUV, hVU, hH⟩ := hamiltonian_swap P M i j hij
  refine ⟨c, hc, ?_⟩
  intro J
  have hunit : IsUnit U := ⟨⟨U, V, hUV, hVU⟩, rfl⟩
  have hinv : U⁻¹ = V := Matrix.inv_eq_right_inv hUV
  simp only [SYK.partitionFunction, gibbsOperator]
  rw [hH J]
  have hconj : -(β : ℂ) • (U * hamiltonian P M J * V) =
      U * (-(β : ℂ) • hamiltonian P M J) * U⁻¹ := by
    rw [hinv, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, Matrix.exp_conj _ _ hunit, hinv,
    Matrix.trace_mul_comm, ← mul_assoc, hVU, one_mul]

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
theorem integral_gaussianCouplings_sign {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (c : ι → ℝ)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (F : (ι → ℝ) → E) :
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

/-- Reindexing i.i.d. standard Gaussian coordinates preserves expectation. -/
theorem integral_gaussianCouplings_perm {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : ι ≃ ι) (F : (ι → ℝ) → E) :
    ∫ g, F (fun i => g (e i)) ∂gaussianCouplings ι =
      ∫ g, F g ∂gaussianCouplings ι := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm)
      (gaussianCouplings ι) (gaussianCouplings ι) := by
    exact measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e.symm
  have heq (g : ι → ℝ) :
      (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm) g =
        (fun i => g (e i)) := by
    funext i
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι => ℝ) e.symm g (e i)
    simpa using h
  have h := hmp.integral_comp' F
  simp_rw [heq] at h
  exact h

/-- A signed permutation of i.i.d. Gaussian coordinates preserves expectation. -/
theorem integral_gaussianCouplings_signed_perm {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : ι ≃ ι) (c : ι → ℝ) (hc : ∀ i, c i = 1 ∨ c i = -1)
    (F : (ι → ℝ) → E) :
    ∫ g, F (fun i => c i * g (e i)) ∂gaussianCouplings ι =
      ∫ g, F g ∂gaussianCouplings ι := by
  calc
    _ = ∫ g, F (fun i => c i * g i) ∂gaussianCouplings ι :=
      integral_gaussianCouplings_perm e (fun g => F (fun i => c i * g i))
    _ = ∫ g, F g ∂gaussianCouplings ι :=
      integral_gaussianCouplings_sign c hc F

/-- Flipping the interactions containing one vertex negates an odd Hermite monomial. -/
theorem hermiteMulti_vertex_flip {N q : ℕ} (α : InteractionIndex N q → ℕ)
    (x : Fin N) (hx : Odd (∑ I with x ∈ I.1, α I))
    (g : InteractionIndex N q → ℝ) :
    hermiteMulti α (fun I => (if x ∈ I.1 then -1 else 1) * g I) =
      -hermiteMulti α g := by
  classical
  let c : InteractionIndex N q → ℝ := fun I => if x ∈ I.1 then -1 else 1
  have hc : ∀ I, c I = 1 ∨ c I = -1 := fun I => by
    by_cases h : x ∈ I.1 <;> simp [c, h]
  simp only [hermiteMulti]
  change (∏ I, Polynomial.aeval (c I * g I) (Polynomial.hermite (α I))) =
    -(∏ I, Polynomial.aeval (g I) (Polynomial.hermite (α I)))
  simp only [fun I => hermite_aeval_sign (α I) (c I) (g I) (hc I)]
  rw [Finset.prod_mul_distrib]
  have hsign : ∏ I, c I ^ α I = -1 := by
    have h1 : ∀ I, c I ^ α I = (-1 : ℝ) ^ (if x ∈ I.1 then α I else 0) := fun I => by
      by_cases h : x ∈ I.1 <;> simp [c, h]
    simp only [h1]
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter, hx.neg_one_pow]
  rw [hsign, neg_one_mul]

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
  have hH : ∀ g, hermiteMulti α (fun I => c I * g I) = -hermiteMulti α g :=
    fun g => hermiteMulti_vertex_flip α x hx g
  have key := integral_gaussianCouplings_sign c hc
    (fun g => SYK.partitionFunction (β : ℂ) (hamiltonian P M g) *
      (hermiteMulti α g : ℂ))
  simp only [hZ, hH, Complex.ofReal_neg, mul_neg, integral_neg] at key
  linear_combination -key / 2
end SYK
