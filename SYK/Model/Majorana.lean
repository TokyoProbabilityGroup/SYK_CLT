import SYK.Model.Definitions

/-!
# Abstract Majorana systems and interaction operators

`MajoranaSystem N A` is a family of `N` self-adjoint generators `ψ i` in a complex
star-algebra `A` with `ψ i ψ j + ψ j ψ i = 2 δ_ij`. For an interaction label `s`,
`psiProduct` is the ordered product of its generators, `phase q = i ^ (q / 2)`, and
`interactionOperator = phase q • psiProduct` is self-adjoint for even `q`. The file
also proves the algebraic identities used downstream (squares, reordering signs,
anticommutation with generators inside `s`) and defines the deterministic
`hamiltonian`. Nothing here assumes a matrix representation or irreducibility.
-/

open scoped BigOperators ComplexConjugate

namespace SYK

/-- An abstract complex star-algebra carrying `N` Majorana generators. -/
structure MajoranaSystem (N : ℕ) (A : Type*)
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] where
  /-- The Majorana generators. -/
  ψ : Fin N → A
  /-- The canonical anticommutation relations `ψᵢψⱼ + ψⱼψᵢ = 2δᵢⱼ`. -/
  majorana_rel :
    ∀ i j, ψ i * ψ j + ψ j * ψ i = if i = j then 2 else 0
  /-- Each generator is self-adjoint. -/
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

/-- Moving a generator past a product of distinct other generators contributes
one minus sign per factor. -/
theorem listProduct_mul_generator
    (i : Fin N) (l : List (Fin N)) (hi : i ∉ l) :
    (l.map M.ψ).prod * M.ψ i =
      ((-1 : ℂ) ^ l.length) • (M.ψ i * (l.map M.ψ).prod) := by
  apply M.listProduct_mul
  intro j hj
  exact M.anticommute (fun hji ↦ hi (hji ▸ hj))

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
private theorem star_psiProduct (s : InteractionIndex N q) :
    star (M.psiProduct s) =
      ((-1 : ℂ) ^ (q * (q - 1) / 2)) • M.psiProduct s := by
  rw [psiProduct, M.star_listProduct, M.reverse_listProduct]
  · simp [Nat.choose_two_right]
  · simp [orderedIndices]

/-- For even `q`, the reversal sign is `(-1)^(q/2)`. -/
private theorem star_psiProduct_of_even (s : InteractionIndex N q) (hq : Even q) :
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

private theorem phase_sq (q : ℕ) :
    phase q * phase q = (-1 : ℂ) ^ (q / 2) := by
  rw [phase, ← mul_pow]
  norm_num

/-- The phase has complex norm one. -/
private theorem star_phase_mul_self (q : ℕ) :
    star (phase q) * phase q = 1 := by
  change star (Complex.I ^ (q / 2)) * Complex.I ^ (q / 2) = 1
  rw [star_pow, ← mul_pow]
  norm_num

namespace MajoranaSystem

variable {N q : ℕ} {A : Type*}
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (M : MajoranaSystem N A)

/-- A phase-corrected Majorana interaction observable. -/
noncomputable def interactionOperator (s : InteractionIndex N q) : A :=
  phase q • M.psiProduct s

private theorem star_phase_mul_sign (q : ℕ) :
    star (phase q) * ((-1 : ℂ) ^ (q / 2)) = phase q := by
  calc
    star (phase q) * ((-1 : ℂ) ^ (q / 2)) =
        star (phase q) * (phase q * phase q) := by rw [phase_sq]
    _ = (star (phase q) * phase q) * phase q := by rw [mul_assoc]
    _ = phase q := by rw [star_phase_mul_self, one_mul]

theorem interactionOperator_star
    (hq : Even q) (s : InteractionIndex N q) :
    star (M.interactionOperator s) = M.interactionOperator s := by
  rw [interactionOperator, star_smul, M.star_psiProduct_of_even s hq,
    smul_smul, star_phase_mul_sign]

theorem majorana_sq (i : Fin N) : M.ψ i * M.ψ i = 1 := by
  have h := M.majorana_rel i i
  rw [if_pos rfl] at h
  rw [← one_add_one_eq_two] at h
  apply smul_right_injective A (show (2 : ℂ) ≠ 0 by norm_num)
  simpa [two_smul] using h

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

private theorem star_listProduct_mul_self
    (l : List (Fin N)) (hl : l.Nodup) :
    star ((l.map M.ψ).prod) * (l.map M.ψ).prod = 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      simp only [List.map_cons, List.prod_cons, star_mul, M.self_adjoint]
      rw [← mul_assoc, mul_assoc (star ((l.map M.ψ).prod)),
        M.majorana_sq, mul_one, ih hl.2]

theorem psiProduct_star_mul_self (s : InteractionIndex N q) :
    star (M.psiProduct s) * M.psiProduct s = 1 := by
  apply M.star_listProduct_mul_self
  simp [orderedIndices]

theorem interactionOperator_sq
    (hq : Even q) (s : InteractionIndex N q) :
    M.interactionOperator s * M.interactionOperator s = 1 := by
  have hstar := M.interactionOperator_star hq s
  calc
    M.interactionOperator s * M.interactionOperator s =
        star (M.interactionOperator s) * M.interactionOperator s := by
          rw [hstar]
    _ = (star (phase q) * phase q) •
        (star (M.psiProduct s) * M.psiProduct s) := by
          rw [interactionOperator, star_smul, smul_mul_smul_comm]
    _ = (star (phase q) * phase q) • (1 : A) := by
          rw [M.psiProduct_star_mul_self]
  rw [star_phase_mul_self, one_smul]


/-- Moving an included generator past an interaction word contributes `q-1`
minus signs, because its own factor commutes with itself. -/
theorem psiProduct_mul_generator_of_mem
    (s : InteractionIndex N q) (i : Fin N) (hi : i ∈ s.1) :
    M.psiProduct s * M.ψ i =
      ((-1 : ℂ) ^ (q - 1)) • (M.ψ i * M.psiProduct s) := by
  let l := orderedIndices s
  have hmem : i ∈ l := by simpa [l, orderedIndices] using hi
  have hnodup : l.Nodup := by simp [l, orderedIndices]
  obtain ⟨c, _hsign, hc⟩ := M.listProduct_eq_sign_smul_of_perm l (i :: l.erase i)
    (List.perm_cons_erase hmem)
  simp only [List.map_cons, List.prod_cons] at hc
  have heq : M.psiProduct s = c • (M.ψ i * ((l.erase i).map M.ψ).prod) := hc
  have hanti := M.listProduct_mul_generator i (l.erase i) hnodup.not_mem_erase
  rw [List.length_erase_of_mem hmem, show l.length = q from length_orderedIndices s] at hanti
  rw [heq, Algebra.smul_mul_assoc, mul_assoc, hanti,
    Algebra.mul_smul_comm, Algebra.mul_smul_comm, smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

/-- For even degree, the interaction anticommutes with each included generator. -/
theorem interactionOperator_mul_generator_of_mem
    (hq : Even q) (s : InteractionIndex N q) (i : Fin N) (hi : i ∈ s.1) :
    M.interactionOperator s * M.ψ i = -(M.ψ i * M.interactionOperator s) := by
  have hqpos : 0 < q := by
    have := Finset.card_pos.mpr ⟨i, hi⟩
    simpa [s.2] using this
  have hodd : Odd (q - 1) := by
    obtain ⟨m, hm⟩ := hq
    exact ⟨m - 1, by omega⟩
  rw [interactionOperator, Algebra.smul_mul_assoc, M.psiProduct_mul_generator_of_mem s i hi,
    hodd.neg_one_pow, neg_one_smul, smul_neg, Algebra.mul_smul_comm]

end MajoranaSystem

/-- The deterministic SYK Hamiltonian associated to real couplings `J`. -/
noncomputable def hamiltonian
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (P : Params) (M : MajoranaSystem P.N A)
    (J : InteractionIndex P.N P.q → ℝ) : A :=
  ∑ s, ((J s : ℝ) : ℂ) • M.interactionOperator s

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
  rw [star_smul, M.interactionOperator_star P.q_even]
  simp

end SYK
