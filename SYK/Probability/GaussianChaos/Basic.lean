import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Hermite products and symmetries of finite product Gaussians

These definitions and sign/permutation identities apply to any finite coordinate
set. The Majorana gauge and vertex-parity results are in `CliffordSignParity`;
the coefficient integration-by-parts formulas are in
`SYK.Probability.GaussianChaos.CoefficientIBP`.
Entry points: `SYK.GaussianChaos.hermiteMulti`, `SYK.GaussianChaos.gaussianCouplings`,
`integral_gaussianCouplings_signed_perm`.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SYK.GaussianChaos

/-- The degree-two probabilists' Hermite polynomial evaluated on the real line. -/
theorem hermite_two_eval (x : ℝ) :
    Polynomial.aeval x (Polynomial.hermite 2) = x ^ 2 - 1 := by
  rw [show 2 = 1 + 1 by decide, Polynomial.hermite_succ, Polynomial.hermite_one]
  simp
  ring

/-- The multivariate (probabilists') Hermite polynomial `H_α(g) = ∏_I He_{α_I}(g_I)`. -/
noncomputable def hermiteMulti {ι : Type*} [Fintype ι] (α : ι → ℕ) (g : ι → ℝ) : ℝ :=
  ∏ I, Polynomial.aeval (g I) (Polynomial.hermite (α I))

/-- The law of the couplings: i.i.d. standard Gaussians. -/
noncomputable def gaussianCouplings (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance gaussianCouplings_isProbability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (gaussianCouplings ι) := by
  unfold gaussianCouplings
  infer_instance

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

end SYK.GaussianChaos
