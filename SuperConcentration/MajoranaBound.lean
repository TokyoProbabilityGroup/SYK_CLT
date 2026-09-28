import SYK.SuperConcentration.DensityMatrix
import SYK.Model.Majorana
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-! The finite-size sum-of-squares bound for Majorana interactions. -/

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped Matrix.Norms.Operator

namespace SYK

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
