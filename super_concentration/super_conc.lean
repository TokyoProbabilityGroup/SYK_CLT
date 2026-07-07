import SYK.Gaussian_concentration.gaussian_concentration
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds

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

omit [DecidableEq d] in
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

omit [DecidableEq d] in
theorem expectation_im_eq_zero
    {ρ A : Matrix d d ℂ} (hρ : IsDensityMatrix ρ) (hA : star A = A) :
    (expectation ρ A).im = 0 := by
  have h := expectation_star_eq hρ hA
  exact Complex.conj_eq_iff_im.mp h

omit [DecidableEq d] in
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
    have hnonneg : 0 ≤ NormedSpace.exp A := by
      rw [CStarAlgebra.nonneg_iff_eq_star_mul_self]
      refine ⟨B, ?_⟩
      change NormedSpace.exp A = star B * B
      rw [hB, hBB]
    exact Matrix.nonneg_iff_posSemidef.mp hnonneg
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

omit [DecidableEq d] in
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
    convert (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const B) using 1
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
  have hsum :
      ∑ i ∈ Finset.range (n + 1),
          Matrix.trace
            ((A + t • B) ^ ((n + 1).pred - i) * B *
              (A + t • B) ^ i) =
        ∑ _i ∈ Finset.range (n + 1),
          Matrix.trace (B * (A + t • B) ^ n) := by
    exact Finset.sum_congr rfl fun i hi ↦ hterm i hi
  rw [hsum]
  rw [Finset.sum_const, Finset.card_range]
  rw [Nat.factorial_succ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp
  push_cast
  ring

theorem hasDerivAt_trace_exp_affine [Nonempty d]
    (A B : Matrix d d ℂ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ Matrix.trace (NormedSpace.exp (A + s • B)))
      (Matrix.trace (B * NormedSpace.exp (A + t • B))) t := by
  let C : ℝ → Matrix d d ℂ := fun s ↦ A + s • B
  let g : ℕ → ℝ → ℂ := fun n s ↦ matrixTraceCLM
    ((((n + 1).factorial : ℝ)⁻¹) • C s ^ (n + 1))
  let g' : ℕ → ℝ → ℂ := fun n s ↦ matrixTraceCLM
    (((n.factorial : ℝ)⁻¹) • (B * C s ^ n))
  let R : ℝ := ‖A‖ + (|t| + 1) * ‖B‖
  let K : ℝ := ‖matrixTraceCLM (d := d)‖ * ‖B‖
  let u : ℕ → ℝ := fun n ↦ K * ‖((n.factorial : ℝ)⁻¹)‖ * R ^ n
  have hR : 0 ≤ R := by positivity
  have hK : 0 ≤ K := by positivity
  have hu : Summable u := by
    have h := NormedSpace.norm_expSeries_summable'
      (𝕂 := ℝ) (𝔸 := ℝ) R
    have h' := h.mul_left K
    simpa [u, norm_smul, abs_of_nonneg hR, mul_assoc] using h'
  have hCnorm {y : ℝ} (hy : y ∈ Set.Ioo (t - 1) (t + 1)) : ‖C y‖ ≤ R := by
    have hyt : |y - t| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have hyabs : |y| ≤ |t| + 1 := by
      calc
        |y| = |t + (y - t)| := by ring_nf
        _ ≤ |t| + |y - t| := abs_add_le _ _
        _ ≤ |t| + 1 := by linarith
    calc
      ‖C y‖ = ‖A + y • B‖ := rfl
      _ ≤ ‖A‖ + ‖y • B‖ := norm_add_le _ _
      _ = ‖A‖ + |y| * ‖B‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ R := by
        dsimp [R]
        gcongr
  have hg (n : ℕ) (y : ℝ) (_hy : y ∈ Set.Ioo (t - 1) (t + 1)) :
      HasDerivAt (g n) (g' n y) y := by
    simpa [g, g', C] using hasDerivAt_trace_exp_term A B n y
  have hg_bound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (t - 1) (t + 1)) :
      ‖g' n y‖ ≤ u n := by
    have hpow : ‖C y ^ n‖ ≤ R ^ n := by
      exact (norm_pow_le (C y) n).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hCnorm hy) n)
    calc
      ‖g' n y‖ = ‖matrixTraceCLM
          (((n.factorial : ℝ)⁻¹) • (B * C y ^ n))‖ := rfl
      _ ≤ ‖matrixTraceCLM (d := d)‖ *
          ‖((n.factorial : ℝ)⁻¹) • (B * C y ^ n)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖matrixTraceCLM (d := d)‖ *
          (‖((n.factorial : ℝ)⁻¹)‖ * ‖B * C y ^ n‖) := by
        rw [norm_smul]
      _ ≤ ‖matrixTraceCLM (d := d)‖ *
          (‖((n.factorial : ℝ)⁻¹)‖ * (‖B‖ * ‖C y ^ n‖)) := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ ‖matrixTraceCLM (d := d)‖ *
          (‖((n.factorial : ℝ)⁻¹)‖ * (‖B‖ * R ^ n)) := by
        gcongr
      _ = u n := by simp [u, K]; ring
  have hg0 : Summable fun n ↦ g n t := by
    have htail : Summable fun n : ℕ ↦
        (((n + 1).factorial : ℝ)⁻¹) • C t ^ (n + 1) := by
      exact (NormedSpace.expSeries_summable' (𝕂 := ℝ) (C t)).comp_injective
        Nat.succ_injective
    rcases htail with ⟨a, ha⟩
    refine ⟨matrixTraceCLM (d := d) a, ?_⟩
    simpa [g, Function.comp_def] using
      ha.map (matrixTraceCLM (d := d)) (matrixTraceCLM (d := d)).continuous
  have htmem : t ∈ Set.Ioo (t - 1) (t + 1) := by constructor <;> linarith
  have htailDeriv : HasDerivAt (fun s ↦ ∑' n, g n s) (∑' n, g' n t) t :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      hg hg_bound htmem hg0 htmem
  have hfull (s : ℝ) : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • C s ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (C s)
  have hfun (s : ℝ) :
      Matrix.trace (NormedSpace.exp (C s)) =
        Matrix.trace (1 : Matrix d d ℂ) + ∑' n, g n s := by
    rw [show NormedSpace.exp (C s) =
        ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • C s ^ n by
      simpa using congrFun (NormedSpace.exp_eq_tsum ℝ) (C s)]
    change matrixTraceCLM (d := d)
      (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • C s ^ n) = _
    rw [ContinuousLinearMap.map_tsum (matrixTraceCLM (d := d)) (hfull s)]
    have htrace : Summable fun n : ℕ ↦ matrixTraceCLM (d := d)
        (((n.factorial : ℝ)⁻¹) • C s ^ n) := by
      rcases hfull s with ⟨a, ha⟩
      exact ⟨matrixTraceCLM (d := d) a,
        ha.map (matrixTraceCLM (d := d)) (matrixTraceCLM (d := d)).continuous⟩
    rw [← htrace.sum_add_tsum_nat_add 1]
    simp [g]
  have hderiv :
      (∑' n, g' n t) =
        Matrix.trace (B * NormedSpace.exp (C t)) := by
    let a : ℕ → Matrix d d ℂ := fun n ↦
      ((n.factorial : ℝ)⁻¹) • C t ^ n
    have ha : Summable a := hfull t
    have hBa : Summable fun n ↦ B * a n := ha.mul_left B
    calc
      (∑' n, g' n t) =
          ∑' n, matrixTraceCLM (d := d) (B * a n) := by
        congr 1
        funext n
        simp [g', a, Algebra.mul_smul_comm]
      _ = matrixTraceCLM (d := d) (∑' n, B * a n) :=
        (ContinuousLinearMap.map_tsum (matrixTraceCLM (d := d)) hBa).symm
      _ = matrixTraceCLM (d := d) (B * ∑' n, a n) := by
        congr 1
        exact (ha.hasSum.mul_left B).tsum_eq
      _ = Matrix.trace (B * NormedSpace.exp (C t)) := by
        rw [show NormedSpace.exp (C t) = ∑' n, a n by
          simpa [a] using congrFun (NormedSpace.exp_eq_tsum ℝ) (C t)]
        rfl
  have hsum := (hasDerivAt_const t (Matrix.trace (1 : Matrix d d ℂ))).add htailDeriv
  rw [hderiv] at hsum
  convert hsum using 1
  · funext s
    exact hfun s
  · simp [C]

end TraceExponentialDerivative

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

theorem normalizedHamiltonian_affine
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J V : CouplingSpace P.N P.q) (s : ℝ) :
    normalizedHamiltonian P M 𝒥 (J + s • V) =
      normalizedHamiltonian P M 𝒥 J +
        s • normalizedHamiltonian P M 𝒥 V := by
  classical
  simp only [normalizedHamiltonian, hamiltonian]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _hI
  change (((couplingScale P 𝒥 * (J I + s * V I) : ℝ) : ℂ) * phase P.q) •
      M.chiProduct I =
    ((((couplingScale P 𝒥 * J I : ℝ) : ℂ) * phase P.q) • M.chiProduct I) +
      s • ((((couplingScale P 𝒥 * V I : ℝ) : ℂ) * phase P.q) • M.chiProduct I)
  rw [← smul_assoc, ← add_smul]
  congr 1
  rw [Complex.real_smul]
  push_cast
  ring

theorem normalizedHamiltonian_self_adjoint
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) :
    star (normalizedHamiltonian P M 𝒥 J) =
      normalizedHamiltonian P M 𝒥 J := by
  exact hamiltonian_self_adjoint P M _

theorem hasDerivAt_logPartition_line
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J V : CouplingSpace P.N P.q) (s : ℝ) :
    let Hs := normalizedHamiltonian P M 𝒥 (J + s • V)
    let Bs := -((P.β : ℂ)) • normalizedHamiltonian P M 𝒥 V
    HasDerivAt (fun r : ℝ ↦ logPartition P M 𝒥 (J + r • V))
      ((Matrix.trace (Bs * gibbsOperator P.inverseTemperature Hs)).re /
        (partitionFunction P.inverseTemperature Hs).re) s := by
  dsimp only
  let A : Matrix d d ℂ :=
    -((P.β : ℂ)) • normalizedHamiltonian P M 𝒥 J
  let B : Matrix d d ℂ :=
    -((P.β : ℂ)) • normalizedHamiltonian P M 𝒥 V
  have hexp (r : ℝ) :
      -(((P.inverseTemperature : ℝ) : ℂ)) •
          normalizedHamiltonian P M 𝒥 (J + r • V) =
        A + r • B := by
    rw [P.coe_inverseTemperature, normalizedHamiltonian_affine]
    dsimp [A, B]
    module
  have hexp' (r : ℝ) :
      -((((P.inverseTemperature : ℝ) : ℂ)) •
          normalizedHamiltonian P M 𝒥 (J + r • V)) =
        A + r • B := by
    rw [← neg_smul]
    exact hexp r
  have htrace := hasDerivAt_trace_exp_affine A B s
  have hre := (hasDerivAt_const s Complex.reCLM).clm_apply htrace
  have hpos : 0 < (partitionFunction P.inverseTemperature
      (normalizedHamiltonian P M 𝒥 (J + s • V))).re :=
    partitionFunction_pos _ (normalizedHamiltonian_self_adjoint P M 𝒥 _)
  have hpos' : 0 < Complex.reCLM
      (Matrix.trace (NormedSpace.exp (A + s • B))) := by
    have h := hpos
    rw [partitionFunction, gibbsOperator, hexp s] at h
    simpa using h
  have hlog := hre.log (ne_of_gt hpos')
  convert hlog using 1
  · funext r
    simp only [logPartition, partitionFunction, gibbsOperator,
      Complex.reCLM_apply]
    rw [hexp r]
  · simp only [B, partitionFunction, gibbsOperator, Complex.reCLM_apply]
    rw [hexp s]
    simp [B, smul_smul, smul_neg]

/-- The Lipschitz constant obtained from the SYK sum-of-squares estimate. -/
noncomputable def simpleLipschitzConstant (P : Params) (𝒥 : ℝ) : ℝ≥0 :=
  Real.toNNReal (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ))

/--
The two-sided superconcentration estimate for the product standard Gaussian
coupling measure. The SYK gradient estimate is supplied in the reusable
`hLip` hypothesis.
-/
theorem logPartition_two_sided_tail
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
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
  have hq : 0 < (P.q : ℝ) := by exact_mod_cast P.q_pos
  have hsqrt : 0 < Real.sqrt (P.q : ℝ) := Real.sqrt_pos.2 hq
  let L : ℝ := |P.β| * 𝒥 / Real.sqrt (P.q : ℝ)
  have hL : 0 < L := div_pos (mul_pos (abs_pos.mpr hβ) h𝒥) hsqrt
  have hLip' : LipschitzWith L.toNNReal (logPartition P M 𝒥) := by
    simpa [L, simpleLipschitzConstant] using hLip
  have htail :=
    gaussian_lipschitz_concentration P.N P.q
      (logPartition P M 𝒥) L t hL ht hLip'
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

/--
The normalization constant absorbs the sum-of-squares SYK bound:
`couplingScale · √(C(N,q-1)/q) ≤ 𝒥 / √q`.
-/
theorem couplingScale_mul_sqrt_choose_le
    (P : Params) (𝒥 : ℝ) (h𝒥 : 0 ≤ 𝒥) :
    couplingScale P 𝒥 *
        Real.sqrt ((Nat.choose P.N (P.q - 1) : ℝ) / (P.q : ℝ)) ≤
      𝒥 / Real.sqrt (P.q : ℝ) := by
  unfold couplingScale; ring_nf; norm_num [ h𝒥 ] ;
  -- Cancel out the common terms $\mathcal{J}$ and $\sqrt{q}$ from both sides.
  suffices h_suff : Real.sqrt ((P.q - 1).factorial * (P.N.choose (P.q - 1))) ≤ Real.sqrt (P.N ^ (P.q - 1)) by
    field_simp at *;
    rw [ div_le_div_iff₀ ];
    · rw [ Real.sqrt_mul <| by positivity ] at h_suff ; nlinarith [ show 0 ≤ 𝒥 * Real.sqrt P.q by positivity ];
    · exact mul_pos ( Real.sqrt_pos.mpr ( pow_pos ( Nat.cast_pos.mpr ( by linarith [ P.q_pos, P.q_le_N ] ) ) _ ) ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith [ P.q_pos, P.q_le_N ] ) ) );
    · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr P.q_pos );
  refine Real.sqrt_le_sqrt ?_;
  rw_mod_cast [ ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow _ _;

/--
Cauchy–Schwarz combined with the SYK sum-of-squares bound controls the
directional gradient of the (normalized) SYK energy in any density matrix.
-/
theorem abs_beta_expectation_normHam_le
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 ≤ 𝒥)
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ)
    (V : CouplingSpace P.N P.q) :
    |P.β * (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re|
      ≤ (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ)) * ‖V‖ := by
  -- By definition of $c$, we have $c = couplingScale P 𝒥$.
  set c := couplingScale P 𝒥;
  -- By linearity of expectation, we have:
  have h_exp_linear : (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re = c * ∑ I : InteractionIndex P.N P.q, V I * (expectation ρ (M.interactionOperator I)).re := by
    unfold normalizedHamiltonian expectation;
    simp +decide [ hamiltonian, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ];
    simp +decide [ phase, MajoranaSystem.interactionOperator ];
    exact Finset.sum_congr rfl fun _ _ => by ring;
  -- By the properties of the expectation and the definition of $c$, we have:
  have h_exp_bound : |∑ I : InteractionIndex P.N P.q, V I * (expectation ρ (M.interactionOperator I)).re| ≤ ‖V‖ * Real.sqrt ((Nat.choose P.N (P.q - 1) : ℝ) / P.q) := by
    have h_exp_bound : (∑ I : InteractionIndex P.N P.q, V I * (expectation ρ (M.interactionOperator I)).re) ^ 2 ≤ (∑ I : InteractionIndex P.N P.q, V I ^ 2) * (∑ I : InteractionIndex P.N P.q, (expectation ρ (M.interactionOperator I)).re ^ 2) := by
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _;
    have h_exp_bound : (∑ I : InteractionIndex P.N P.q, (expectation ρ (M.interactionOperator I)).re ^ 2) ≤ (Nat.choose P.N (P.q - 1) : ℝ) / P.q := by
      have := syk_sum_sq_expectation_le P.q_pos P.q_even M ρ hρ;
      refine' le_trans _ this;
      exact Finset.sum_le_sum fun i _ => by simp +decide [ Complex.normSq, Complex.sq_norm ] ; nlinarith only;
    rw [ ← Real.sqrt_sq_eq_abs, EuclideanSpace.norm_eq ];
    rw [ ← Real.sqrt_mul ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; exact Real.sqrt_le_sqrt <| by simpa using le_trans ‹_› <| mul_le_mul_of_nonneg_left h_exp_bound <| Finset.sum_nonneg fun _ _ => sq_nonneg _;
  -- By combining the results from h_exp_linear and h_exp_bound, we get:
  have h_combined : |P.β * (expectation ρ (normalizedHamiltonian P M 𝒥 V)).re| ≤ |P.β| * c * ‖V‖ * Real.sqrt ((Nat.choose P.N (P.q - 1) : ℝ) / P.q) := by
    rw [ h_exp_linear, abs_mul, abs_mul, abs_of_nonneg ( show 0 ≤ c by exact mul_nonneg h𝒥 ( Real.sqrt_nonneg _ ) ) ] ; nlinarith [ abs_nonneg P.β, show 0 ≤ |P.β| * c by exact mul_nonneg ( abs_nonneg _ ) ( mul_nonneg h𝒥 ( Real.sqrt_nonneg _ ) ) ];
  refine le_trans h_combined ?_;
  convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( couplingScale_mul_sqrt_choose_le P 𝒥 h𝒥 ) ( abs_nonneg P.β ) ) ( norm_nonneg V ) using 1 ; ring;
  ring

/--
The directional derivative of `logPartition` along `V`, expressed as a
thermal expectation of the (normalized) SYK energy.
-/
theorem logPartition_line_deriv_eq
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J V : CouplingSpace P.N P.q) (s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ logPartition P M 𝒥 (J + r • V))
      (-P.β * (expectation
        (thermalDensity P.inverseTemperature
          (normalizedHamiltonian P M 𝒥 (J + s • V)))
        (normalizedHamiltonian P M 𝒥 V)).re) s := by
  convert hasDerivAt_logPartition_line P M 𝒥 J V s using 1;
  unfold expectation thermalDensity; simp +decide [ Matrix.trace_smul ] ; ring_nf;
  rw [ Matrix.trace_mul_comm ]

/-- The SYK log-partition function is Lipschitz with the stated constant. -/
theorem logPartition_lipschitz
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 ≤ 𝒥) :
    LipschitzWith (simpleLipschitzConstant P 𝒥)
      (logPartition P M 𝒥) := by
  apply LipschitzWith.of_dist_le_mul;
  intro x y;
  -- Let $V := x - y$ and $g := fun r : ℝ => logPartition P M 𝒥 (y + r • V)$.
  set V : CouplingSpace P.N P.q := x - y
  set g : ℝ → ℝ := fun r => logPartition P M 𝒥 (y + r • V);
  -- By the properties of the derivative and the Lipschitz constant, we have:
  have h_deriv_bound : ∀ r : ℝ, |deriv g r| ≤ (|P.β| * 𝒥 / Real.sqrt (P.q : ℝ)) * ‖V‖ := by
    intro r
    have h_deriv : deriv g r = -P.β * (expectation (thermalDensity P.inverseTemperature (normalizedHamiltonian P M 𝒥 (y + r • V))) (normalizedHamiltonian P M 𝒥 V)).re := by
      convert HasDerivAt.deriv ( logPartition_line_deriv_eq P M 𝒥 y V r ) using 1;
    have := abs_beta_expectation_normHam_le P M 𝒥 h𝒥 ( thermalDensity P.inverseTemperature ( normalizedHamiltonian P M 𝒥 ( y + r • V ) ) ) ( thermalDensity_isDensityMatrix P.inverseTemperature ( normalizedHamiltonian_self_adjoint P M 𝒥 _ ) ) V; simp_all +decide [ abs_mul, abs_neg ] ;
  -- By the Mean Value Theorem, there exists some $c \in (0, 1)$ such that $g(1) - g(0) = g'(c)$.
  have h_mvt : ∃ c ∈ Set.Ioo 0 1, g 1 - g 0 = deriv g c := by
    have := exists_deriv_eq_slope g zero_lt_one;
    exact this ( continuousOn_of_forall_continuousAt fun r hr => by exact DifferentiableAt.continuousAt <| by exact ( logPartition_line_deriv_eq P M 𝒥 y V r |> HasDerivAt.differentiableAt ) ) ( fun r hr => by exact DifferentiableAt.differentiableWithinAt <| by exact ( logPartition_line_deriv_eq P M 𝒥 y V r |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by norm_num at hc₂; linarith ⟩;
  simp +zetaDelta at *;
  obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt; rw [ dist_eq_norm ] ; rw [ simpleLipschitzConstant ] ; simp +decide [ hc₂ ] ;
  exact le_trans ( h_deriv_bound c ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( norm_nonneg _ ) ) |> le_trans <| by rw [ dist_eq_norm ] ;

/-- For an empty state space the log-partition function is identically zero. -/
theorem logPartition_eq_zero_of_isEmpty
    {d : Type*} [Fintype d] [DecidableEq d] [IsEmpty d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (J : CouplingSpace P.N P.q) :
    logPartition P M 𝒥 J = 0 := by
  unfold logPartition; simp +decide [ partitionFunction ] ;

/-- The same estimate for the product standard Gaussian coupling measure. -/
theorem logPartition_two_sided_tail_standardGaussian
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (𝒥 : ℝ) (h𝒥 : 0 < 𝒥) (hβ : P.β ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    standardGaussianMeasure P.N P.q
        {J | |logPartition P M 𝒥 J -
          ∫ K, logPartition P M 𝒥 K
            ∂standardGaussianMeasure P.N P.q| > t} ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(P.q : ℝ) * t ^ 2 / (2 * P.β ^ 2 * 𝒥 ^ 2))) := by
  rcases isEmpty_or_nonempty d with hd | hd
  · -- Empty state space: `logPartition` is identically zero, so the tail set
    -- is empty because `t > 0`.
    have hconst : ∀ K : CouplingSpace P.N P.q, logPartition P M 𝒥 K = 0 :=
      fun K => logPartition_eq_zero_of_isEmpty P M 𝒥 K
    have hset :
        {J : CouplingSpace P.N P.q | |logPartition P M 𝒥 J -
            ∫ K, logPartition P M 𝒥 K
              ∂standardGaussianMeasure P.N P.q| > t} = ∅ := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_lt]
      simp only [hconst, integral_zero, sub_zero, abs_zero]
      exact ht.le
    rw [hset]
    simp
  · exact logPartition_two_sided_tail P M 𝒥 h𝒥 hβ
      (logPartition_lipschitz P M 𝒥 h𝒥.le) t ht
end SYK
