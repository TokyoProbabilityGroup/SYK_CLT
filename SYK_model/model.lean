import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped BigOperators ComplexConjugate

namespace SYK

/-- Parameters of an SYK model. -/
structure Params where
  N : ℕ
  q : ℕ
  q_even : Even q
  q_pos : 0 < q
  q_le_N : q ≤ N
  β : ℝ
  β_nonneg : 0 ≤ β

/-- The inverse temperature packaged with its nonnegativity proof. -/
def Params.inverseTemperature (P : Params) : NNReal := ⟨P.β, P.β_nonneg⟩

@[simp]
theorem Params.coe_inverseTemperature (P : Params) :
    (P.inverseTemperature : ℝ) = P.β := rfl

/-- A label for a `q`-body interaction is a `q`-element subset of the fermion labels. -/
abbrev InteractionIndex (N q : ℕ) := {s : Finset (Fin N) // s.card = q}

/-- The elements of an interaction index in their canonical increasing order. -/
def orderedIndices {N q : ℕ} (s : InteractionIndex N q) : List (Fin N) :=
  s.1.sort (· ≤ ·)

@[simp]
theorem length_orderedIndices {N q : ℕ} (s : InteractionIndex N q) :
    (orderedIndices s).length = q := by
  simp [orderedIndices, s.2]

/-- An abstract complex star-algebra carrying `N` Majorana generators. -/
structure MajoranaSystem (N : ℕ) (A : Type*)
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] where
  ψ : Fin N → A
  majorana_rel :
    ∀ i j, ψ i * ψ j + ψ j * ψ i = if i = j then 2 else 0
  self_adjoint : ∀ i, star (ψ i) = ψ i

namespace MajoranaSystem

variable {N q : ℕ} {A : Type*}
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (M : MajoranaSystem N A)

/-- The ordered product of the Majorana generators in an interaction. -/
def psiProduct (s : InteractionIndex N q) : A :=
  ((orderedIndices s).map M.ψ).prod

theorem anticommute {i j : Fin N} (hij : i ≠ j) :
    M.ψ i * M.ψ j = -(M.ψ j * M.ψ i) := by
  have h := M.majorana_rel i j
  rw [if_neg hij] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem listProduct_mul (i : Fin N) (l : List (Fin N))
    (h : ∀ j ∈ l, M.ψ j * M.ψ i = -(M.ψ i * M.ψ j)) :
    (l.map M.ψ).prod * M.ψ i =
      ((-1 : ℂ) ^ l.length) • (M.ψ i * (l.map M.ψ).prod) := by
  induction l with
  | nil => simp
  | cons j l ih =>
      have hj : M.ψ j * M.ψ i = -(M.ψ i * M.ψ j) := h j (by simp)
      have hl : ∀ k ∈ l, M.ψ k * M.ψ i = -(M.ψ i * M.ψ k) := by
        intro k hk
        exact h k (by simp [hk])
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      calc
        (M.ψ j * (l.map M.ψ).prod) * M.ψ i =
            M.ψ j * ((l.map M.ψ).prod * M.ψ i) := by rw [mul_assoc]
        _ = M.ψ j * (((-1 : ℂ) ^ l.length) •
            (M.ψ i * (l.map M.ψ).prod)) := by rw [ih hl]
        _ = ((-1 : ℂ) ^ l.length) •
            (M.ψ j * (M.ψ i * (l.map M.ψ).prod)) := by
              rw [Algebra.mul_smul_comm]
        _ = ((-1 : ℂ) ^ l.length) •
            ((M.ψ j * M.ψ i) * (l.map M.ψ).prod) := by rw [mul_assoc]
        _ = ((-1 : ℂ) ^ l.length) •
            (-(M.ψ i * (M.ψ j * (l.map M.ψ).prod))) := by rw [hj, neg_mul, mul_assoc]
        _ = (((-1 : ℂ) ^ l.length) * (-1 : ℂ)) •
            (M.ψ i * (M.ψ j * (l.map M.ψ).prod)) := by
              rw [mul_smul]
              simp
        _ = ((-1 : ℂ) ^ (l.length + 1)) •
            (M.ψ i * (M.ψ j * (l.map M.ψ).prod)) := by rw [pow_succ]

private theorem reverse_listProduct (l : List (Fin N)) (hl : l.Nodup) :
    (l.reverse.map M.ψ).prod =
      ((-1 : ℂ) ^ l.length.choose 2) • (l.map M.ψ).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      have hanti : ∀ j ∈ l, M.ψ j * M.ψ i = -(M.ψ i * M.ψ j) := by
        intro j hj
        exact M.anticommute (fun hji ↦ hl.1 (hji ▸ hj))
      simp only [List.reverse_cons, List.map_append, List.prod_append,
        List.map_cons, List.prod_cons, List.length_cons,
        List.map_nil, List.prod_nil, mul_one]
      rw [ih hl.2, Algebra.smul_mul_assoc, M.listProduct_mul i l hanti, smul_smul]
      have hexponent : (l.length + 1).choose 2 = l.length.choose 2 + l.length := by
        simpa [add_comm] using Nat.choose_succ_succ' l.length 1
      rw [hexponent, pow_add]

private theorem star_listProduct (l : List (Fin N)) :
    star ((l.map M.ψ).prod) = (l.reverse.map M.ψ).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [star_mul, M.self_adjoint, ih]
      simp [List.reverse_cons]

/-- Reversing a product under `star` contributes one sign for every pair of generators. -/
theorem star_psiProduct (s : InteractionIndex N q) :
    star (M.psiProduct s) =
      ((-1 : ℂ) ^ (q * (q - 1) / 2)) • M.psiProduct s := by
  rw [psiProduct, M.star_listProduct, M.reverse_listProduct]
  · simp [Nat.choose_two_right]
  · simp [orderedIndices]

/-- For even `q`, the reversal sign is `(-1)^(q/2)`. -/
theorem star_psiProduct_of_even (s : InteractionIndex N q) (hq : Even q) :
    star (M.psiProduct s) = ((-1 : ℂ) ^ (q / 2)) • M.psiProduct s := by
  rw [M.star_psiProduct s]
  congr 1
  rcases hq with ⟨m, rfl⟩
  have hhalf : (m + m) / 2 = m := by omega
  rw [hhalf]
  by_cases hm0 : m = 0
  · simp [hm0]
  have hexponent :
      (m + m) * (m + m - 1) / 2 = m * (m + m - 1) := by
    calc
      (m + m) * (m + m - 1) / 2 =
          2 * (m * (m + m - 1)) / 2 := by ring_nf
      _ = m * (m + m - 1) := Nat.mul_div_right _ (by norm_num)
  rw [hexponent, pow_mul]
  have hodd : Odd (m + m - 1) := ⟨m - 1, by omega⟩
  rcases Nat.even_or_odd m with hm | hm
  · simp [hm.neg_one_pow]
  · simp [hm.neg_one_pow, hodd.neg_one_pow]

end MajoranaSystem

/-- The phase used for an even `q`. -/
def phase (q : ℕ) : ℂ := Complex.I ^ (q / 2)

private theorem star_phase_mul_sign (q : ℕ) :
    star (phase q) * ((-1 : ℂ) ^ (q / 2)) = phase q := by
  change star (Complex.I ^ (q / 2)) * ((-1 : ℂ) ^ (q / 2)) =
    Complex.I ^ (q / 2)
  rw [star_pow, Complex.star_def, Complex.conj_I]
  rw [neg_pow]
  have hsign :
      ((-1 : ℂ) ^ (q / 2)) * ((-1 : ℂ) ^ (q / 2)) = 1 := by
    rw [← mul_pow]
    simp
  calc
    ((-1 : ℂ) ^ (q / 2) * Complex.I ^ (q / 2)) * ((-1 : ℂ) ^ (q / 2)) =
        (((-1 : ℂ) ^ (q / 2)) * ((-1 : ℂ) ^ (q / 2))) *
          Complex.I ^ (q / 2) := by ring
    _ = Complex.I ^ (q / 2) := by rw [hsign, one_mul]

private theorem star_coupling_mul_sign (r : ℝ) (q : ℕ) :
    star (((r : ℝ) : ℂ) * phase q) * ((-1 : ℂ) ^ (q / 2)) =
      ((r : ℝ) : ℂ) * phase q := by
  rw [star_mul]
  have hr : star (((r : ℝ) : ℂ)) = ((r : ℝ) : ℂ) := by
    simp
  rw [hr]
  calc
    (star (phase q) * (r : ℂ)) * ((-1 : ℂ) ^ (q / 2)) =
        (r : ℂ) * (star (phase q) * ((-1 : ℂ) ^ (q / 2))) := by ring
    _ = (r : ℂ) * phase q := by rw [star_phase_mul_sign]

/-- The deterministic SYK Hamiltonian associated to real couplings `J`. -/
noncomputable def hamiltonian
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (P : Params) (M : MajoranaSystem P.N A)
    (J : InteractionIndex P.N P.q → ℝ) : A :=
  ∑ s, (((J s : ℝ) : ℂ) * phase P.q) • M.psiProduct s

/-- The even-`q` phase makes the deterministic SYK Hamiltonian self-adjoint. -/
theorem hamiltonian_self_adjoint
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (P : Params) (M : MajoranaSystem P.N A)
    (J : InteractionIndex P.N P.q → ℝ) :
    star (hamiltonian P M J) = hamiltonian P M J := by
  classical
  rw [hamiltonian, star_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [star_smul, M.star_psiProduct_of_even s P.q_even, smul_smul,
    star_coupling_mul_sign]

section MatrixThermodynamics

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The unnormalized Gibbs operator `exp (-β H)`. -/
noncomputable def gibbsOperator (β : NNReal) (H : Matrix d d ℂ) : Matrix d d ℂ :=
  NormedSpace.exp (-((β : ℝ) : ℂ) • H)

/-- The finite-dimensional partition function `Tr (exp (-β H))`. -/
noncomputable def partitionFunction (β : NNReal) (H : Matrix d d ℂ) : ℂ :=
  Matrix.trace (gibbsOperator β H)

/-- Thermal expectation of an observable in the Gibbs state. -/
noncomputable def gibbsState (β : NNReal) (H O : Matrix d d ℂ) : ℂ :=
  Matrix.trace (O * gibbsOperator β H) / partitionFunction β H

@[simp]
theorem gibbsOperator_zero (H : Matrix d d ℂ) :
    gibbsOperator 0 H = 1 := by
  simp [gibbsOperator]

@[simp]
theorem partitionFunction_zero (H : Matrix d d ℂ) :
    partitionFunction 0 H = Fintype.card d := by
  simp [partitionFunction]

end MatrixThermodynamics

end SYK
