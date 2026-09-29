import SYK.CLT.Lemmas.Rademacher
import SYK.CLT.Lemmas.CliffordSignParity
import SYK.CLT.Lemmas.GaussianHermiteOrthogonality
import Mathlib.Data.Nat.Choose.Multinomial

open Finset Real

namespace SYK.CLT.Rademacher

#check Finset.sum_subtype
#check Finset.sum_attach
#check Finset.prod_ite
#check Finset.prod_filter
#check multiIndices_degree
#check Finset.prod_pow

lemma chaos_eq_sum_interactionIndex (N q : ℕ) (ε : Fin N → Bool) :
    chaos N q ε =
      ∑ I : InteractionIndex N q, ∏ x ∈ I.1, rad (ε x) := by
  classical
  unfold chaos
  simpa only [InteractionIndex] using
    (Finset.sum_subtype ((Finset.univ : Finset (Fin N)).powersetCard q)
      (fun I => by simp) (fun I => ∏ x ∈ I, rad (ε x)))

lemma interactionMonomial_eq_vertexProduct (N q : ℕ)
    (α : InteractionIndex N q → ℕ) (ε : Fin N → Bool) :
    (∏ I : InteractionIndex N q,
        (∏ x ∈ I.1, rad (ε x)) ^ α I) =
      ∏ x : Fin N, rad (ε x) ^ (∑ I with x ∈ I.1, α I) := by
  classical
  calc
    (∏ I : InteractionIndex N q,
        (∏ x ∈ I.1, rad (ε x)) ^ α I) =
        ∏ I : InteractionIndex N q,
          ∏ x : Fin N, if x ∈ I.1 then rad (ε x) ^ α I else 1 := by
            apply Finset.prod_congr rfl
            intro I _
            rw [← Finset.prod_filter]
            simp_rw [← Finset.prod_pow]
            simp
    _ = ∏ x : Fin N,
          ∏ I : InteractionIndex N q,
            if x ∈ I.1 then rad (ε x) ^ α I else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ x : Fin N, rad (ε x) ^ (∑ I with x ∈ I.1, α I) := by
          apply Finset.prod_congr rfl
          intro x _
          rw [← Finset.prod_filter]
          simp only [← Finset.prod_pow_eq_pow_sum]

lemma radE_vertexProduct (N : ℕ) (m : Fin N → ℕ) :
    radE N (fun ε => ∏ x, rad (ε x) ^ m x) =
      if ∀ x, Even (m x) then 1 else 0 := by
  classical
  unfold radE
  rw [← Fintype.prod_sum (fun x b => rad b ^ m x)]
  by_cases h : ∀ x, Even (m x)
  · rw [if_pos h]
    have hs : ∀ x : Fin N, ∑ b : Bool, rad b ^ m x = 2 := by
      intro x
      rw [show ∑ b : Bool, rad b ^ m x = (2 : ℝ) by
        simp [rad_pow, h x]]
    simp_rw [hs]
    simp [Finset.prod_const]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨x, hx⟩ := h
    have hodd : Odd (m x) := Nat.not_even_iff_odd.mp hx
    have hz : ∑ b : Bool, rad b ^ m x = 0 := by
      simp [rad, hodd.neg_one_pow]
    rw [Finset.prod_eq_zero (Finset.mem_univ x) hz, mul_zero]

open scoped Classical in
lemma radE_interactionMonomial (N q : ℕ)
    (α : InteractionIndex N q → ℕ) :
    radE N (fun ε =>
      ∏ I : InteractionIndex N q,
        (∏ x ∈ I.1, rad (ε x)) ^ α I) =
      if IsEvenMultiIndex α then 1 else 0 := by
  classical
  have hfun : (fun ε : Fin N → Bool => ∏ I : InteractionIndex N q,
      (∏ x ∈ I.1, rad (ε x)) ^ α I) =
      fun ε => ∏ x : Fin N, rad (ε x) ^ (∑ I with x ∈ I.1, α I) := by
    funext ε
    exact interactionMonomial_eq_vertexProduct N q α ε
  rw [hfun]
  have h := radE_vertexProduct N (fun x => ∑ I with x ∈ I.1, α I)
  by_cases he : IsEvenMultiIndex α
  · have he' : ∀ x : Fin N, Even (∑ I with x ∈ I.1, α I) := he
    simpa [he, he'] using h
  · have he' : ¬ ∀ x : Fin N, Even (∑ I with x ∈ I.1, α I) := he
    simpa [he, he'] using h

open scoped Classical in
theorem radE_chaos_pow_eq_sum_multinomial_even (N q r : ℕ) :
    radE N (fun ε => chaos N q ε ^ r) =
      ∑ α ∈ (multiIndices_degree (ι := InteractionIndex N q) r).filter IsEvenMultiIndex,
        (Nat.multinomial Finset.univ α : ℝ) := by
  classical
  let w : (Fin N → Bool) → InteractionIndex N q → ℝ :=
    fun ε I => ∏ x ∈ I.1, rad (ε x)
  have hindices :
      Finset.piAntidiag (Finset.univ : Finset (InteractionIndex N q)) r =
        multiIndices_degree (ι := InteractionIndex N q) r := by
    ext α
    rw [Finset.mem_piAntidiag, mem_multiIndices_degree]
    constructor
    · intro h
      simpa using h.1
    · intro h
      exact ⟨by simpa using h, by simp⟩
  have hexpand (ε : Fin N → Bool) :
      chaos N q ε ^ r =
        ∑ α ∈ multiIndices_degree (ι := InteractionIndex N q) r,
          (Nat.multinomial Finset.univ α : ℝ) * ∏ I, w ε I ^ α I := by
    rw [chaos_eq_sum_interactionIndex]
    have h := Finset.sum_pow_eq_sum_piAntidiag
      (Finset.univ : Finset (InteractionIndex N q)) (w ε) r
    simpa only [hindices] using h
  rw [show (fun ε => chaos N q ε ^ r) = fun ε =>
      ∑ α ∈ multiIndices_degree (ι := InteractionIndex N q) r,
        (Nat.multinomial Finset.univ α : ℝ) * ∏ I, w ε I ^ α I by
      funext ε
      exact hexpand ε]
  rw [radE_sum]
  simp_rw [radE_const_mul]
  dsimp [w]
  simp_rw [radE_interactionMonomial]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]

open scoped Classical in
theorem even_multiIndex_sum_eq_radE_chaos_pow_div_factorial
    (N q r : ℕ) :
    (∑ α ∈ (multiIndices_degree (ι := InteractionIndex N q) r).filter IsEvenMultiIndex,
      (∏ I : InteractionIndex N q, ((α I).factorial : ℝ))⁻¹) =
      ((r.factorial : ℝ)⁻¹ * radE N (fun ε => chaos N q ε ^ r)) := by
  classical
  rw [radE_chaos_pow_eq_sum_multinomial_even, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [Finset.mem_filter, mem_multiIndices_degree] at hα
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (InteractionIndex N q)) α
  rw [hα.1] at hspec
  have hspecR :
      (∏ I : InteractionIndex N q, ((α I).factorial : ℝ)) *
        (Nat.multinomial Finset.univ α : ℝ) = (r.factorial : ℝ) := by
    exact_mod_cast hspec
  have hprod : (∏ I : InteractionIndex N q, ((α I).factorial : ℝ)) ≠ 0 := by
    positivity
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

end SYK.CLT.Rademacher
