import SYK.SYK_model.model
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open scoped BigOperators ComplexOrder ENNReal NNReal
open scoped MatrixOrder
open scoped Matrix.Norms.Operator
open MeasureTheory
open ProbabilityTheory

namespace SYK

section DensityMatrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A finite-dimensional density matrix. -/
def IsDensityMatrix (ρ : Matrix d d ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- Expectation of a matrix observable in a density matrix. -/
noncomputable def expectation (ρ A : Matrix d d ℂ) : ℂ :=
  Matrix.trace (ρ * A)

theorem expectation_star_eq
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    star (expectation ρ A) = expectation ρ A := by
  rw [expectation, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
  change Matrix.trace (star A * star ρ) = Matrix.trace (ρ * A)
  have hsρ : star ρ = ρ := by
    change Matrix.conjTranspose ρ = ρ
    exact hρ.1.isHermitian.eq
  rw [hA, hsρ]
  exact Matrix.trace_mul_comm A ρ

theorem expectation_im_eq_zero
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    (expectation ρ A).im = 0 := by
  have h := expectation_star_eq hρ hA
  exact Complex.conj_eq_iff_im.mp h

theorem expectation_eq_ofReal_re
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    ((expectation ρ A).re : ℂ) = expectation ρ A := by
  apply Complex.ext
  · simp
  · simp [expectation_im_eq_zero hρ hA]

theorem density_variance_nonneg
    {ρ B : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hB : star B = B) :
    0 ≤ (expectation ρ (B * B)).re - (expectation ρ B).re ^ 2 := by
  let z : ℂ := expectation ρ B
  let C : Matrix d d ℂ := B - z • (1 : Matrix d d ℂ)
  have hzstar : star z = z := by
    exact expectation_star_eq hρ hB
  have hC : star C = C := by
    simp [C, hB, hzstar]
  have hpos := hρ.1.conjTranspose_mul_mul_same C
  have htrace : 0 ≤ (Matrix.trace (star C * ρ * C)).re := by
    have hz : 0 ≤ Matrix.trace (Matrix.conjTranspose C * ρ * C) :=
      hpos.trace_nonneg
    exact (RCLike.nonneg_iff.mp hz).1
  have hcycle : Matrix.trace (star C * ρ * C) =
      Matrix.trace (ρ * (C * C)) := by
    rw [hC, Matrix.trace_mul_cycle C ρ C,
      Matrix.trace_mul_comm (C * C) ρ]
  have hCC : C * C =
      B * B - (2 * z) • B + z ^ 2 • 1 := by
    simp only [C, sub_mul, mul_sub]
    simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    rw [show (2 : ℂ) * z = z + z by ring, add_smul]
    simp only [smul_smul, pow_two]
    abel
  rw [hcycle, hCC] at htrace
  have htraceρ : Matrix.trace ρ = (1 : ℂ) := hρ.2
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_one, smul_eq_mul] at htrace
  have htrace' : 0 ≤
      (expectation ρ (B * B) - (2 * z) * expectation ρ B +
        z ^ 2 * Matrix.trace ρ).re := by
    simpa [expectation] using htrace
  rw [show expectation ρ B = z from rfl, htraceρ] at htrace'
  have hzim : z.im = 0 := by
    exact expectation_im_eq_zero hρ hB
  dsimp [z] at htrace' hzim ⊢
  norm_num [Complex.mul_re, pow_two] at htrace'
  nlinarith

end DensityMatrix

section AnticommutingFamily

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

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

/-- A phase-corrected Majorana interaction observable. -/
noncomputable def interactionOperator (s : InteractionIndex N q) : A :=
  phase q • M.chiProduct s

theorem majorana_sq (i : Fin N) : M.χ i * M.χ i = 1 := by
  have h := M.majorana_rel i i
  rw [if_pos rfl] at h
  rw [← one_add_one_eq_two] at h
  apply smul_right_injective A (show (2 : ℂ) ≠ 0 by norm_num)
  simpa [two_smul] using h

private theorem listProduct_mul_generator
    (i : Fin N) (l : List (Fin N))
    (hi : i ∉ l) :
    (l.map M.χ).prod * M.χ i =
      ((-1 : ℂ) ^ l.length) • (M.χ i * (l.map M.χ).prod) := by
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
          (-(M.χ i * (M.χ j * (l.map M.χ).prod))) =
          (((-1 : ℂ) ^ l.length) * (-1)) •
            (M.χ i * (M.χ j * (l.map M.χ).prod)) by simp]
      rw [pow_succ]

private theorem listProduct_eq_smul_of_perm
    (l₁ l₂ : List (Fin N)) (h : l₁.Perm l₂) :
    ∃ c : ℂ, (l₁.map M.χ).prod = c • (l₂.map M.χ).prod := by
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
          M.χ j * (M.χ i * (l.map M.χ).prod) =
              (M.χ j * M.χ i) * (l.map M.χ).prod := by rw [mul_assoc]
          _ = (-(M.χ i * M.χ j)) * (l.map M.χ).prod := by
            rw [M.anticommute (Ne.symm hij)]
          _ = (-1 : ℂ) • (M.χ i * (M.χ j * (l.map M.χ).prod)) := by
            simp [mul_assoc]
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨c₁, hc₁⟩
      rcases ih₂ with ⟨c₂, hc₂⟩
      refine ⟨c₁ * c₂, ?_⟩
      rw [hc₁, hc₂, smul_smul]

private theorem star_listProduct_mul_self
    (l : List (Fin N)) (hl : l.Nodup) :
    star ((l.map M.χ).prod) * (l.map M.χ).prod = 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      simp only [List.map_cons, List.prod_cons, star_mul, M.self_adjoint]
      rw [← mul_assoc, mul_assoc (star ((l.map M.χ).prod)),
        M.majorana_sq, mul_one, ih hl.2]

theorem chiProduct_star_mul_self (s : InteractionIndex N q) :
    star (M.chiProduct s) * M.chiProduct s = 1 := by
  apply M.star_listProduct_mul_self
  simp [orderedIndices]

private theorem star_phase_mul_sign' (q : ℕ) :
    star (phase q) * ((-1 : ℂ) ^ (q / 2)) = phase q := by
  change star (Complex.I ^ (q / 2)) * ((-1 : ℂ) ^ (q / 2)) =
    Complex.I ^ (q / 2)
  rw [star_pow, Complex.star_def, Complex.conj_I, neg_pow]
  have hsign :
      ((-1 : ℂ) ^ (q / 2)) * ((-1 : ℂ) ^ (q / 2)) = 1 := by
    rw [← mul_pow]
    simp
  calc
    ((-1 : ℂ) ^ (q / 2) * Complex.I ^ (q / 2)) *
        ((-1 : ℂ) ^ (q / 2)) =
      (((-1 : ℂ) ^ (q / 2)) * ((-1 : ℂ) ^ (q / 2))) *
        Complex.I ^ (q / 2) := by ring
    _ = Complex.I ^ (q / 2) := by rw [hsign, one_mul]

theorem interactionOperator_star
    (hq : Even q) (s : InteractionIndex N q) :
    star (M.interactionOperator s) = M.interactionOperator s := by
  rw [interactionOperator, star_smul, M.star_chiProduct_of_even s hq,
    smul_smul, star_phase_mul_sign']

theorem interactionOperator_sq
    (hq : Even q) (s : InteractionIndex N q) :
    M.interactionOperator s * M.interactionOperator s = 1 := by
  have hstar := M.interactionOperator_star hq s
  calc
    M.interactionOperator s * M.interactionOperator s =
        star (M.interactionOperator s) * M.interactionOperator s := by
          rw [hstar]
    _ = (star (phase q) * phase q) •
        (star (M.chiProduct s) * M.chiProduct s) := by
          rw [interactionOperator, star_smul, smul_mul_smul_comm]
    _ = (star (phase q) * phase q) • (1 : A) := by
          rw [M.chiProduct_star_mul_self]
  change (star (phase q) * phase q) • (1 : A) = 1
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

private theorem chiProduct_extend_eq_smul
    (hq : 0 < q) (C : InteractionIndex N (q - 1)) (j : Outside C) :
    ∃ c : ℂ, M.chiProduct (extendInteraction hq C j) =
      c • (M.χ j.1 * M.chiProduct C) := by
  have hperm : List.Perm
      (orderedIndices (extendInteraction hq C j))
      (j.1 :: orderedIndices C) := by
    apply (List.perm_ext_iff_of_nodup (by simp [orderedIndices])
      (by simp [orderedIndices, j.2])).2
    intro i
    simp [orderedIndices, extendInteraction]
  simpa [chiProduct] using
    M.listProduct_eq_smul_of_perm _ _ hperm

theorem extendInteraction_anticommute
    (hq0 : 0 < q) (hq : Even q)
    (C : InteractionIndex N (q - 1))
    (j k : Outside C) (hjk : j ≠ k) :
    M.interactionOperator (extendInteraction hq0 C j) *
        M.interactionOperator (extendInteraction hq0 C k) =
      -(M.interactionOperator (extendInteraction hq0 C k) *
        M.interactionOperator (extendInteraction hq0 C j)) := by
  rcases M.chiProduct_extend_eq_smul hq0 C j with ⟨cⱼ, hcⱼ⟩
  rcases M.chiProduct_extend_eq_smul hq0 C k with ⟨cₖ, hcₖ⟩
  let D : A := M.chiProduct C
  have hjmem : j.1 ∉ orderedIndices C := by
    simpa [orderedIndices] using j.2
  have hkmem : k.1 ∉ orderedIndices C := by
    simpa [orderedIndices] using k.2
  have hodd : Odd (q - 1) := by
    rcases hq with ⟨m, rfl⟩
    exact ⟨m - 1, by omega⟩
  have hDⱼ : D * M.χ j.1 = -(M.χ j.1 * D) := by
    have h := M.listProduct_mul_generator j.1 (orderedIndices C) hjmem
    rw [length_orderedIndices, hodd.neg_one_pow] at h
    simpa [D, chiProduct] using h
  have hDₖ : D * M.χ k.1 = -(M.χ k.1 * D) := by
    have h := M.listProduct_mul_generator k.1 (orderedIndices C) hkmem
    rw [length_orderedIndices, hodd.neg_one_pow] at h
    simpa [D, chiProduct] using h
  have hjk' : j.1 ≠ k.1 := by
    intro h
    apply hjk
    exact Subtype.ext h
  have hχ : M.χ j.1 * M.χ k.1 = -(M.χ k.1 * M.χ j.1) :=
    M.anticommute hjk'
  have hbase :
      (M.χ j.1 * D) * (M.χ k.1 * D) =
        -((M.χ k.1 * D) * (M.χ j.1 * D)) := by
    calc
      (M.χ j.1 * D) * (M.χ k.1 * D) =
          M.χ j.1 * (D * M.χ k.1) * D := by simp only [mul_assoc]
      _ = M.χ j.1 * (-(M.χ k.1 * D)) * D := by rw [hDₖ]
      _ = -((M.χ j.1 * M.χ k.1) * (D * D)) := by noncomm_ring
      _ = (M.χ k.1 * M.χ j.1) * (D * D) := by rw [hχ]; simp
      _ = -(M.χ k.1 * (D * M.χ j.1) * D) := by rw [hDⱼ]; noncomm_ring
      _ = -((M.χ k.1 * D) * (M.χ j.1 * D)) := by simp only [mul_assoc]
  rw [interactionOperator, interactionOperator, hcⱼ, hcₖ,
    smul_smul, smul_smul, smul_mul_smul_comm, smul_mul_smul_comm, hbase]
  simpa [D, mul_comm]

end MajoranaSystem

abbrev ChosenPoint (I : InteractionIndex N q) :=
  {j : Fin N // j ∈ I.1}

private def eraseChosenPoint (hq : 0 < q) (I : InteractionIndex N q)
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
      simp [Fintype.card_coe, show ∀ I : InteractionIndex N q,
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

section GibbsDensity

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem gibbsOperator_posDef (β : NNReal) {H : Matrix d d ℂ}
    (hH : star H = H) : (gibbsOperator β H).PosDef := by
  let A : Matrix d d ℂ := -((β : ℝ) : ℂ) • H
  have hA : star A = A := by
    simp [A, hH]
  let B : Matrix d d ℂ := NormedSpace.exp ((2 : ℂ)⁻¹ • A)
  have hB : star B = B := by
    exact (show Matrix.IsHermitian ((2 : ℂ)⁻¹ • A) by
      simpa [Matrix.IsHermitian, hA]).exp.eq
  have hBB : B * B = NormedSpace.exp A := by
    dsimp [B]
    rw [← Matrix.exp_add_of_commute]
    · congr 1
      module
    · exact Commute.refl _
  have hpsd : (NormedSpace.exp A).PosSemidef := by
    rw [Matrix.posSemidef_iff_eq_conjTranspose_mul_self]
    refine ⟨B, ?_⟩
    change NormedSpace.exp A = star B * B
    rw [hB, hBB]
  apply hpsd.posDef_iff_isUnit.mpr
  exact Matrix.isUnit_exp A

theorem partitionFunction_star_eq (β : NNReal) {H : Matrix d d ℂ}
    (hH : star H = H) :
    star (partitionFunction β H) = partitionFunction β H := by
  have hG : star (gibbsOperator β H) = gibbsOperator β H :=
    (gibbsOperator_posDef β hH).isHermitian.eq
  change star (Matrix.trace (gibbsOperator β H)) =
    Matrix.trace (gibbsOperator β H)
  rw [← Matrix.trace_conjTranspose]
  change Matrix.trace (star (gibbsOperator β H)) = _
  rw [hG]

theorem partitionFunction_im_eq_zero (β : NNReal) {H : Matrix d d ℂ}
    (hH : star H = H) : (partitionFunction β H).im = 0 :=
  Complex.conj_eq_iff_im.mp (partitionFunction_star_eq β hH)

theorem partitionFunction_pos [Nonempty d] (β : NNReal)
    {H : Matrix d d ℂ} (hH : star H = H) :
    0 < (partitionFunction β H).re := by
  have h := (gibbsOperator_posDef β hH).trace_pos
  exact (RCLike.pos_iff.mp h).1

/-- The normalized Gibbs matrix, using the real positive partition function. -/
noncomputable def thermalDensity (β : NNReal) (H : Matrix d d ℂ) :
    Matrix d d ℂ :=
  ((partitionFunction β H).re⁻¹ : ℝ) • gibbsOperator β H

theorem thermalDensity_isDensityMatrix [Nonempty d] (β : NNReal)
    {H : Matrix d d ℂ} (hH : star H = H) :
    IsDensityMatrix (thermalDensity β H) := by
  have hZ : 0 < (partitionFunction β H).re := partitionFunction_pos β hH
  constructor
  · exact ((gibbsOperator_posDef β hH).smul (inv_pos.mpr hZ)).posSemidef
  · rw [thermalDensity, Matrix.trace_smul]
    change (((partitionFunction β H).re⁻¹ : ℝ) : ℂ) *
        partitionFunction β H = 1
    have hreal : ((partitionFunction β H).re : ℂ) =
        partitionFunction β H := by
      apply Complex.ext
      · simp
      · simp [partitionFunction_im_eq_zero β hH]
    rw [← hreal]
    simp only [Complex.ofReal_re]
    simp [ne_of_gt hZ]

theorem gibbsState_eq_expectation_thermalDensity [Nonempty d]
    (β : NNReal) {H O : Matrix d d ℂ} (hH : star H = H) :
    gibbsState β H O = expectation (thermalDensity β H) O := by
  have hZ : 0 < (partitionFunction β H).re := partitionFunction_pos β hH
  have hreal : ((partitionFunction β H).re : ℂ) =
      partitionFunction β H := by
    apply Complex.ext
    · simp
    · simp [partitionFunction_im_eq_zero β hH]
  rw [gibbsState, expectation, thermalDensity, Matrix.smul_mul,
    Matrix.trace_smul]
  change Matrix.trace (O * gibbsOperator β H) / partitionFunction β H =
    (((partitionFunction β H).re⁻¹ : ℝ) : ℂ) *
      Matrix.trace (gibbsOperator β H * O)
  rw [← hreal]
  simp only [Complex.ofReal_re]
  field_simp
  simpa [ne_of_gt hZ] using Matrix.trace_mul_comm O (gibbsOperator β H)

end GibbsDensity

section TraceExponentialDerivative

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable def matrixTraceCLM : Matrix d d ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap d ℝ ℂ)

@[simp]
theorem matrixTraceCLM_apply (A : Matrix d d ℂ) :
    matrixTraceCLM A = Matrix.trace A := rfl

private theorem trace_pow_mul_cycle (A B : Matrix d d ℂ)
    {n i : ℕ} (hi : i ≤ n) :
    Matrix.trace (A ^ (n - i) * B * A ^ i) =
      Matrix.trace (B * A ^ n) := by
  calc
    Matrix.trace (A ^ (n - i) * B * A ^ i) =
        Matrix.trace (A ^ i * A ^ (n - i) * B) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (A ^ n * B) := by
      congr 1
      rw [← pow_add, Nat.add_sub_of_le hi]
    _ = Matrix.trace (B * A ^ n) := Matrix.trace_mul_comm _ _

private theorem hasDerivAt_trace_exp_term
    (A B : Matrix d d ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ matrixTraceCLM
        (((((n + 1).factorial : ℝ))⁻¹) •
          (A + s • B) ^ (n + 1)))
      (matrixTraceCLM
        ((((n.factorial : ℝ))⁻¹) •
          (B * (A + t • B) ^ n))) t := by
  have hpath : HasDerivAt (fun s : ℝ ↦ A + s • B) B t := by
    convert (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const B) using 1 <;>
      simp
  have hpow := hpath.fun_pow' (n + 1)
  have hscaled := hpow.const_smul (((n + 1).factorial : ℝ)⁻¹)
  have htrace := (hasDerivAt_const t (matrixTraceCLM (d := d))).clm_apply hscaled
  convert htrace using 1
  simp only [ContinuousLinearMap.zero_apply, zero_add, matrixTraceCLM_apply,
    map_smul, Matrix.trace_sum]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      Matrix.trace
          ((A + t • B) ^ ((n + 1).pred - i) * B *
            (A + t • B) ^ i) =
        Matrix.trace (B * (A + t • B) ^ n) := by
    simpa using trace_pow_mul_cycle (A + t • B) B (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_range]
  push_cast
  rw [Nat.factorial_succ]
  field_simp

end TraceExponentialDerivative

/-- The Euclidean space of real SYK couplings. -/
abbrev CouplingSpace (N q : ℕ) :=
  EuclideanSpace ℝ (InteractionIndex N q)

/-- The product standard Gaussian measure transported to coupling space. -/
noncomputable def standardGaussianMeasure (N q : ℕ) :
    Measure (CouplingSpace N q) :=
  (Measure.pi fun _ : InteractionIndex N q => gaussianReal 0 1).map
    (WithLp.toLp 2)

/-- The normalization multiplying each Gaussian coupling. -/
noncomputable def couplingScale (P : Params) (𝒥 : ℝ) : ℝ :=
  𝒥 * Real.sqrt ((P.q - 1).factorial / (P.N : ℝ) ^ (P.q - 1))

/-- The normalized SYK Hamiltonian. -/
noncomputable def normalizedHamiltonian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) : Matrix d d ℂ :=
  hamiltonian P M (fun I => couplingScale P 𝒥 * J I)

/-- The real logarithm of the real part of the partition function. -/
noncomputable def logPartition
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) : ℝ :=
  Real.log
    (partitionFunction P.inverseTemperature
      (normalizedHamiltonian P M 𝒥 J)).re

/--
The Gaussian concentration input isolated by the blueprint.  Mathlib does not
currently provide this theorem in the required finite-dimensional form, so the
final SYK theorem accepts this proposition as a hypothesis.
-/
def GaussianLipschitzConcentration {E : Type*}
    [MeasurableSpace E] [PseudoMetricSpace E]
    (γ : Measure E) : Prop :=
  ∀ (F : E → ℝ) (L t : ℝ),
    0 < L → 0 < t → LipschitzWith L.toNNReal F →
      γ {x | |F x - ∫ y, F y ∂γ| > t} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2)))

/-- The Lipschitz constant obtained from the SYK sum-of-squares estimate. -/
noncomputable def simpleLipschitzConstant (P : Params) (𝒥 : ℝ) : ℝ≥0 :=
  Real.toNNReal (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ))

/--
The two-sided superconcentration estimate.  Its only analytic input not
available in mathlib is `GaussianLipschitzConcentration`; the SYK gradient
estimate is supplied in the reusable `hLip` hypothesis.
-/
theorem logPartition_two_sided_tail
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
    (γ : Measure (CouplingSpace P.N P.q))
    (hγ : GaussianLipschitzConcentration
      (E := CouplingSpace P.N P.q) γ)
    (hLip : LipschitzWith (simpleLipschitzConstant P 𝒥)
      (logPartition P M 𝒥))
    (t : ℝ) (ht : 0 < t) :
    γ {J | |logPartition P M 𝒥 J -
        ∫ K, logPartition P M 𝒥 K ∂γ| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2))) := by
  have hq : 0 < (P.q : ℝ) := by exact_mod_cast P.q_pos
  have hsqrt : 0 < Real.sqrt (P.q : ℝ) := Real.sqrt_pos.2 hq
  let L : ℝ := |P.β| * 𝒥 / Real.sqrt (P.q : ℝ)
  have hL : 0 < L := div_pos (mul_pos (abs_pos.mpr hβ) h𝒥) hsqrt
  have hLip' : LipschitzWith L.toNNReal (logPartition P M 𝒥) := by
    simpa [L, simpleLipschitzConstant] using hLip
  have htail := hγ (logPartition P M 𝒥) L t hL ht hLip'
  have hq0 : (P.q : ℝ) ≠ 0 := ne_of_gt hq
  have hsqrt0 : Real.sqrt (P.q : ℝ) ≠ 0 := ne_of_gt hsqrt
  have hβ0 : P.β ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  have h𝒥0 : 𝒥 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h𝒥)
  have hsqrt_sq : Real.sqrt (P.q : ℝ) ^ 2 = (P.q : ℝ) :=
    Real.sq_sqrt hq.le
  have hLsq : L ^ 2 = P.β ^ 2 * 𝒥 ^ 2 / (P.q : ℝ) := by
    dsimp [L]
    rw [div_pow, mul_pow, sq_abs, hsqrt_sq]
  have hexponent :
      -t ^ 2 / (2 * L ^ 2) =
        -(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2) := by
    rw [hLsq]
    field_simp
  rwa [hexponent] at htail

/-- The same estimate for the product standard Gaussian coupling measure. -/
theorem logPartition_two_sided_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
    (hγ : GaussianLipschitzConcentration
      (standardGaussianMeasure P.N P.q))
    (hLip : LipschitzWith (simpleLipschitzConstant P 𝒥)
      (logPartition P M 𝒥))
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P M 𝒥 J -
          ∫ K, logPartition P M 𝒥 K
            ∂standardGaussianMeasure P.N P.q| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2))) := by
  exact logPartition_two_sided_tail P M 𝒥 h𝒥 hβ
    (standardGaussianMeasure P.N P.q) hγ hLip t ht

end SYK
