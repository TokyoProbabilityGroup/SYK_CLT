import SYK.Model.Majorana
import SYK.Model.FiniteDimensionalGibbs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Algebraic core for SYK superconcentration

This module contains anticommuting-family bounds, the interaction algebra used
by the concentration argument, and the exact finite-volume SYK estimate.
-/

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped Matrix.Norms.Operator

namespace SYK


section AnticommutingFamily

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

omit [Fintype ι] in
private theorem weighted_sum_sq_aux
    (A : ι → Matrix d d ℂ) (c : ι → ℂ)
    (hsq : ∀ i, A i * A i = 1)
    (hanti : ∀ i j, i ≠ j → A i * A j = -(A j * A i))
    (s : Finset ι) :
    (∑ i ∈ s, c i • A i) * (∑ i ∈ s, c i • A i) =
      (∑ i ∈ s, c i ^ 2) • (1 : Matrix d d ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      let S : Matrix d d ℂ := ∑ i ∈ s, c i • A i
      have hAS : A a * S = -(S * A a) := by
        dsimp [S]
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [hanti a i (fun hai => ha (hai ▸ hi))]
        simp
      have hcross : (c a • A a) * S = -(S * (c a • A a)) := by
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hAS]
        simp
      have haa : (c a • A a) * (c a • A a) =
          c a ^ 2 • (1 : Matrix d d ℂ) := by
        rw [smul_mul_smul_comm, hsq, pow_two]
      change (c a • A a + S) * (c a • A a + S) =
        (c a ^ 2 + ∑ i ∈ s, c i ^ 2) • (1 : Matrix d d ℂ)
      rw [mul_add, add_mul, add_mul, hcross, haa, ih]
      module

theorem sum_sq_expectation_le_one
    (ρ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hρ : IsDensityMatrix ρ)
    (hstar : ∀ i, star (A i) = A i)
    (hsq : ∀ i, A i * A i = 1)
    (hanti : ∀ i j, i ≠ j → A i * A j = -(A j * A i)) :
    ∑ i, ‖expectation ρ (A i)‖ ^ 2 ≤ 1 := by
  classical
  let c : ι → ℂ := fun i => expectation ρ (A i)
  let B : Matrix d d ℂ := ∑ i, c i • A i
  let s : ℝ := ∑ i, ‖c i‖ ^ 2
  have hcstar (i : ι) : star (c i) = c i := by
    exact expectation_star_eq hρ (hstar i)
  have hcim (i : ι) : (c i).im = 0 := by
    exact expectation_im_eq_zero hρ (hstar i)
  have hBstar : star B = B := by
    classical
    simp only [B, star_sum, star_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcstar i, hstar i]
  have hBsqC : B * B = (∑ i, c i ^ 2) • (1 : Matrix d d ℂ) := by
    simpa [B] using weighted_sum_sq_aux A c hsq hanti Finset.univ
  have hsumC : (∑ i, c i ^ 2) = (s : ℂ) := by
    apply Complex.ext
    · rw [Complex.re_sum]
      change (∑ i, (c i ^ 2).re) = s
      dsimp [s]
      apply Finset.sum_congr rfl
      intro i _
      rw [Complex.sq_norm]
      simp [pow_two, Complex.mul_re, Complex.normSq_apply, hcim i]
    · rw [Complex.im_sum]
      simp only [Complex.ofReal_im]
      apply Finset.sum_eq_zero
      intro i _
      simp [pow_two, Complex.mul_im, hcim i]
  have hBsq : B * B = (s : ℂ) • (1 : Matrix d d ℂ) := by
    rw [hBsqC, hsumC]
  have hexpB : expectation ρ B = (s : ℂ) := by
    simp only [B, expectation, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    rw [← hsumC]
    apply Finset.sum_congr rfl
    intro i _
    change c i * c i = c i ^ 2
    rw [pow_two]
  have hexpBsq : expectation ρ (B * B) = (s : ℂ) := by
    rw [hBsq]
    simp [expectation, hρ.2]
  have hvar := density_variance_nonneg hρ hBstar
  rw [hexpBsq, hexpB] at hvar
  have hs0 : 0 ≤ s := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖c i‖
  have hs1 : s ≤ 1 := by
    norm_num at hvar
    nlinarith
  simpa [s, c] using hs1

end AnticommutingFamily

namespace MajoranaSystem

variable {N q : ℕ} {A : Type*}
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (M : MajoranaSystem N A)

theorem majorana_sq (i : Fin N) : M.ψ i * M.ψ i = 1 := by
  have h := M.majorana_rel i i
  rw [if_pos rfl] at h
  rw [← one_add_one_eq_two] at h
  apply smul_right_injective A (show (2 : ℂ) ≠ 0 by norm_num)
  simpa [two_smul] using h

private theorem listProduct_mul_generator
    (i : Fin N) (l : List (Fin N))
    (hi : i ∉ l) :
    (l.map M.ψ).prod * M.ψ i =
      ((-1 : ℂ) ^ l.length) • (M.ψ i * (l.map M.ψ).prod) := by
  induction l with
  | nil => simp
  | cons j l ih =>
      have hij : j ≠ i := by
        intro hji
        apply hi
        simp [hji]
      have hil : i ∉ l := by
        intro hil
        exact hi (by simp [hil])
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [mul_assoc, ih hil, Algebra.mul_smul_comm, ← mul_assoc,
        M.anticommute hij, neg_mul, mul_assoc]
      rw [show ((-1 : ℂ) ^ l.length) •
          (-(M.ψ i * (M.ψ j * (l.map M.ψ).prod))) =
          (((-1 : ℂ) ^ l.length) * (-1)) •
            (M.ψ i * (M.ψ j * (l.map M.ψ).prod)) by simp]
      rw [pow_succ]

private theorem listProduct_eq_smul_of_perm
    (l₁ l₂ : List (Fin N)) (h : l₁.Perm l₂) :
    ∃ c : ℂ, (l₁.map M.ψ).prod = c • (l₂.map M.ψ).prod := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | @cons i l₁ l₂ _ ih =>
      rcases ih with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [hc, Algebra.mul_smul_comm]
  | @swap i j l =>
      by_cases hij : i = j
      · subst j
        exact ⟨1, by simp⟩
      · refine ⟨-1, ?_⟩
        simp only [List.map_cons, List.prod_cons]
        calc
          M.ψ j * (M.ψ i * (l.map M.ψ).prod) =
              (M.ψ j * M.ψ i) * (l.map M.ψ).prod := by rw [mul_assoc]
          _ = (-(M.ψ i * M.ψ j)) * (l.map M.ψ).prod := by
            rw [M.anticommute (Ne.symm hij)]
          _ = (-1 : ℂ) • (M.ψ i * (M.ψ j * (l.map M.ψ).prod)) := by
            simp [mul_assoc]
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨c₁, hc₁⟩
      rcases ih₂ with ⟨c₂, hc₂⟩
      refine ⟨c₁ * c₂, ?_⟩
      rw [hc₁, hc₂, smul_smul]

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
  have hp : star (phase q) * phase q = 1 := by
    change star (Complex.I ^ (q / 2)) * Complex.I ^ (q / 2) = 1
    rw [star_pow, ← mul_pow]
    norm_num
  rw [hp, one_smul]

end MajoranaSystem

section FixedCore

variable {N q : ℕ}

/-- Labels outside a fixed interaction core. -/
abbrev Outside (A : InteractionIndex N (q - 1)) :=
  {j : Fin N // j ∉ A.1}

/-- Add one label to a fixed `(q - 1)`-body core. -/
def extendInteraction (hq : 0 < q) (A : InteractionIndex N (q - 1))
    (j : Outside A) : InteractionIndex N q :=
  ⟨insert j.1 A.1, by
    rw [Finset.card_insert_of_notMem j.2, A.2]
    omega⟩

namespace MajoranaSystem

variable {A : Type*}
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (M : MajoranaSystem N A)

private theorem psiProduct_extend_eq_smul
    (hq : 0 < q) (C : InteractionIndex N (q - 1)) (j : Outside C) :
    ∃ c : ℂ, M.psiProduct (extendInteraction hq C j) =
      c • (M.ψ j.1 * M.psiProduct C) := by
  have hperm : List.Perm
      (orderedIndices (extendInteraction hq C j))
      (j.1 :: orderedIndices C) := by
    apply (List.perm_ext_iff_of_nodup (by simp [orderedIndices])
      (by simp [orderedIndices, j.2])).2
    intro i
    simp [orderedIndices, extendInteraction]
  simpa [psiProduct] using
    M.listProduct_eq_smul_of_perm _ _ hperm

theorem extendInteraction_anticommute
    (hq0 : 0 < q) (hq : Even q)
    (C : InteractionIndex N (q - 1))
    (j k : Outside C) (hjk : j ≠ k) :
    M.interactionOperator (extendInteraction hq0 C j) *
        M.interactionOperator (extendInteraction hq0 C k) =
      -(M.interactionOperator (extendInteraction hq0 C k) *
        M.interactionOperator (extendInteraction hq0 C j)) := by
  rcases M.psiProduct_extend_eq_smul hq0 C j with ⟨cⱼ, hcⱼ⟩
  rcases M.psiProduct_extend_eq_smul hq0 C k with ⟨cₖ, hcₖ⟩
  let D : A := M.psiProduct C
  have hjmem : j.1 ∉ orderedIndices C := by
    simpa [orderedIndices] using j.2
  have hkmem : k.1 ∉ orderedIndices C := by
    simpa [orderedIndices] using k.2
  have hodd : Odd (q - 1) := by
    rcases hq with ⟨m, rfl⟩
    exact ⟨m - 1, by omega⟩
  have hDⱼ : D * M.ψ j.1 = -(M.ψ j.1 * D) := by
    have h := M.listProduct_mul_generator j.1 (orderedIndices C) hjmem
    rw [length_orderedIndices, hodd.neg_one_pow] at h
    simpa [D, psiProduct] using h
  have hDₖ : D * M.ψ k.1 = -(M.ψ k.1 * D) := by
    have h := M.listProduct_mul_generator k.1 (orderedIndices C) hkmem
    rw [length_orderedIndices, hodd.neg_one_pow] at h
    simpa [D, psiProduct] using h
  have hjk' : j.1 ≠ k.1 := by
    intro h
    apply hjk
    exact Subtype.ext h
  have hψ : M.ψ j.1 * M.ψ k.1 = -(M.ψ k.1 * M.ψ j.1) :=
    M.anticommute hjk'
  have hbase :
      (M.ψ j.1 * D) * (M.ψ k.1 * D) =
        -((M.ψ k.1 * D) * (M.ψ j.1 * D)) := by
    calc
      (M.ψ j.1 * D) * (M.ψ k.1 * D) =
          M.ψ j.1 * (D * M.ψ k.1) * D := by simp only [mul_assoc]
      _ = M.ψ j.1 * (-(M.ψ k.1 * D)) * D := by rw [hDₖ]
      _ = -((M.ψ j.1 * M.ψ k.1) * (D * D)) := by noncomm_ring
      _ = (M.ψ k.1 * M.ψ j.1) * (D * D) := by rw [hψ]; simp
      _ = -(M.ψ k.1 * (D * M.ψ j.1) * D) := by rw [hDⱼ]; noncomm_ring
      _ = -((M.ψ k.1 * D) * (M.ψ j.1 * D)) := by simp only [mul_assoc]
  rw [interactionOperator, interactionOperator, hcⱼ, hcₖ,
    smul_smul, smul_smul, smul_mul_smul_comm, smul_mul_smul_comm, hbase]
  simp [D, mul_comm]

end MajoranaSystem

abbrev ChosenPoint (I : InteractionIndex N q) :=
  {j : Fin N // j ∈ I.1}

private def eraseChosenPoint (_hq : 0 < q) (I : InteractionIndex N q)
    (j : ChosenPoint I) : InteractionIndex N (q - 1) :=
  ⟨I.1.erase j.1, by
    rw [Finset.card_erase_of_mem j.2, I.2]⟩

/-- Double-counting equivalence between cores with an added point and
interactions with a chosen point. -/
def extensionEquiv (hq : 0 < q) :
    (Σ C : InteractionIndex N (q - 1), Outside C) ≃
      (Σ I : InteractionIndex N q, ChosenPoint I) where
  toFun p :=
    ⟨extendInteraction hq p.1 p.2,
      ⟨p.2.1, by simp [extendInteraction]⟩⟩
  invFun p :=
    ⟨eraseChosenPoint hq p.1 p.2,
      ⟨p.2.1, by simp [eraseChosenPoint]⟩⟩
  left_inv p := by
    rcases p with ⟨C, j⟩
    apply Sigma.ext
    · apply Subtype.ext
      simp [eraseChosenPoint, extendInteraction, j.2]
    · apply (Subtype.heq_iff_coe_eq (fun i ↦ by
        simp [eraseChosenPoint, extendInteraction, j.2])).2
      rfl
  right_inv p := by
    rcases p with ⟨I, j⟩
    apply Sigma.ext
    · apply Subtype.ext
      simp [eraseChosenPoint, extendInteraction, j.2]
    · apply (Subtype.heq_iff_coe_eq (fun i ↦ by
        simp [eraseChosenPoint, extendInteraction, j.2])).2
      rfl

theorem sum_over_extensions (hq : 0 < q)
    (f : InteractionIndex N q → ℝ) :
    ∑ C : InteractionIndex N (q - 1),
      ∑ j : Outside C, f (extendInteraction hq C j) =
    (q : ℝ) * ∑ I : InteractionIndex N q, f I := by
  calc
    ∑ C : InteractionIndex N (q - 1),
        ∑ j : Outside C, f (extendInteraction hq C j) =
      ∑ p : Σ C : InteractionIndex N (q - 1), Outside C,
        f (extendInteraction hq p.1 p.2) := by
          exact (Fintype.sum_sigma'
            (fun C j ↦ f (extendInteraction hq C j))).symm
    _ = ∑ p : Σ I : InteractionIndex N q, ChosenPoint I, f p.1 := by
      exact Fintype.sum_equiv (extensionEquiv hq) _ _ (fun _ ↦ rfl)
    _ = ∑ I : InteractionIndex N q, ∑ _j : ChosenPoint I, f I := by
      exact Fintype.sum_sigma' (fun I (_j : ChosenPoint I) ↦ f I)
    _ = (q : ℝ) * ∑ I : InteractionIndex N q, f I := by
      simp [show ∀ I : InteractionIndex N q,
        I.1.card = q from fun I ↦ I.2, Finset.mul_sum]

end FixedCore

section ExactSYKBound

variable {N q : ℕ} {d : Type*} [Fintype d] [DecidableEq d]

theorem syk_sum_sq_expectation_le
    (hq0 : 0 < q) (hq : Even q)
    (M : MajoranaSystem N (Matrix d d ℂ))
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ) :
    ∑ I : InteractionIndex N q,
        ‖expectation ρ (M.interactionOperator I)‖ ^ 2 ≤
      (Nat.choose N (q - 1) : ℝ) / q := by
  let f : InteractionIndex N q → ℝ := fun I ↦
    ‖expectation ρ (M.interactionOperator I)‖ ^ 2
  have hcore (C : InteractionIndex N (q - 1)) :
      ∑ j : Outside C, f (extendInteraction hq0 C j) ≤ 1 := by
    simpa [f] using
      (sum_sq_expectation_le_one ρ
        (fun j : Outside C ↦ M.interactionOperator
          (extendInteraction hq0 C j)) hρ
        (fun j ↦ M.interactionOperator_star hq _)
        (fun j ↦ M.interactionOperator_sq hq _)
        (fun j k hjk ↦
          M.extendInteraction_anticommute hq0 hq C j k hjk))
  have hsum :
      ∑ C : InteractionIndex N (q - 1),
          ∑ j : Outside C, f (extendInteraction hq0 C j) ≤
        Nat.choose N (q - 1) := by
    calc
      ∑ C : InteractionIndex N (q - 1),
          ∑ j : Outside C, f (extendInteraction hq0 C j) ≤
          ∑ _C : InteractionIndex N (q - 1), (1 : ℝ) :=
        Finset.sum_le_sum fun C _ ↦ hcore C
      _ = Nat.choose N (q - 1) := by
        simp [Fintype.card_finset_len]
  rw [sum_over_extensions hq0] at hsum
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq0
  dsimp [f] at hsum ⊢
  apply (le_div_iff₀ hqR).2
  simpa [mul_comm] using hsum

end ExactSYKBound

end SYK
