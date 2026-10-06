import SYK.CLT.Lemmas.GaussianQuadraticObservable

/-! # Fourth moments of centered Gaussian squares -/

open MeasureTheory ProbabilityTheory

namespace SYK.CLT

private theorem hermite_four_eval (x : ℝ) :
    Polynomial.aeval x (Polynomial.hermite 4) = x ^ 4 - 6 * x ^ 2 + 3 := by
  norm_num [Polynomial.hermite_succ, Polynomial.hermite_one]
  rw [map_ofNat]
  ring

private theorem hermite_two_eval_fourth (x : ℝ) :
    Polynomial.aeval x (Polynomial.hermite 2) = x ^ 2 - 1 := by
  rw [show 2 = 1 + 1 by decide, Polynomial.hermite_succ,
    Polynomial.hermite_one]
  simp
  ring

private theorem integrable_hermite_pair_real (n m : ℕ) :
    Integrable (fun x : ℝ =>
      Polynomial.aeval x (Polynomial.hermite n) *
        Polynomial.aeval x (Polynomial.hermite m))
      (gaussianReal 0 1) := by
  have h := integrable_hermiteMulti_mul (ι := Unit)
    (fun _ => n) (fun _ => m)
  have hp := measurePreserving_eval (fun _ : Unit => gaussianReal 0 1) ()
  apply (hp.integrable_comp (by fun_prop)).mp
  simpa [SYK.hermiteMulti, SYK.gaussianCouplings, Function.comp_def] using h

private theorem centeredGaussianSquare_pow_four_pointwise (x : ℝ) :
    centeredGaussianSquare x ^ 4 =
      ((Polynomial.aeval x (Polynomial.hermite 4)) ^ 2 +
        8 * Polynomial.aeval x (Polynomial.hermite 4) *
          Polynomial.aeval x (Polynomial.hermite 2) +
        4 * Polynomial.aeval x (Polynomial.hermite 4) +
        16 * (Polynomial.aeval x (Polynomial.hermite 2)) ^ 2 +
        16 * Polynomial.aeval x (Polynomial.hermite 2) + 4) / 4 := by
  rw [hermite_four_eval, hermite_two_eval_fourth]
  unfold centeredGaussianSquare
  rw [div_pow]
  have hsqrt : Real.sqrt 2 ^ 4 = (4 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt]
  ring

/-- A centered Gaussian square normalized to variance one has fourth moment `15`. -/
theorem centeredGaussianSquare_fourth_moment :
    (∫ x, centeredGaussianSquare x ^ 4 ∂gaussianReal 0 1) = 15 := by
  let H₂ : ℝ → ℝ := fun x => Polynomial.aeval x (Polynomial.hermite 2)
  let H₄ : ℝ → ℝ := fun x => Polynomial.aeval x (Polynomial.hermite 4)
  have h44 : Integrable (fun x => H₄ x ^ 2) (gaussianReal 0 1) := by
    simpa only [H₄, pow_two] using integrable_hermite_pair_real 4 4
  have h42 : Integrable (fun x => H₄ x * H₂ x) (gaussianReal 0 1) := by
    exact integrable_hermite_pair_real 4 2
  have h22 : Integrable (fun x => H₂ x ^ 2) (gaussianReal 0 1) := by
    simpa only [H₂, pow_two] using integrable_hermite_pair_real 2 2
  have h4 : Integrable H₄ (gaussianReal 0 1) := by
    simpa [H₄, Polynomial.hermite_zero] using integrable_hermite_pair_real 4 0
  have h2 : Integrable H₂ (gaussianReal 0 1) := by
    simpa [H₂, Polynomial.hermite_zero] using integrable_hermite_pair_real 2 0
  have e44 : (∫ x, H₄ x ^ 2 ∂gaussianReal 0 1) = 24 := by
    have h := hermite_pair_integral_real 4 4
    simpa only [H₄, pow_two, if_pos rfl, if_true,
      show ((4 : ℕ).factorial : ℝ) = 24 by norm_num] using h
  have e42 : (∫ x, H₄ x * H₂ x ∂gaussianReal 0 1) = 0 := by
    simpa [H₄, H₂] using hermite_pair_integral_real 4 2
  have e22 : (∫ x, H₂ x ^ 2 ∂gaussianReal 0 1) = 2 := by
    simpa [H₂, pow_two] using hermite_pair_integral_real 2 2
  have e4 : (∫ x, H₄ x ∂gaussianReal 0 1) = 0 := by
    simpa [H₄, Polynomial.hermite_zero] using hermite_pair_integral_real 4 0
  have e2 : (∫ x, H₂ x ∂gaussianReal 0 1) = 0 := by
    simpa [H₂, Polynomial.hermite_zero] using hermite_pair_integral_real 2 0
  calc
    (∫ x, centeredGaussianSquare x ^ 4 ∂gaussianReal 0 1) =
        ∫ x, (H₄ x ^ 2 + 8 * H₄ x * H₂ x + 4 * H₄ x +
          16 * H₂ x ^ 2 + 16 * H₂ x + 4) / 4 ∂gaussianReal 0 1 := by
          congr 1
          funext x
          simpa [H₂, H₄] using centeredGaussianSquare_pow_four_pointwise x
    _ = 15 := by
      rw [integral_div]
      have hB : Integrable (fun x => 8 * (H₄ x * H₂ x)) (gaussianReal 0 1) :=
        h42.const_mul 8
      have hC : Integrable (fun x => 4 * H₄ x) (gaussianReal 0 1) :=
        h4.const_mul 4
      have hD : Integrable (fun x => 16 * H₂ x ^ 2) (gaussianReal 0 1) :=
        h22.const_mul 16
      have hE : Integrable (fun x => 16 * H₂ x) (gaussianReal 0 1) :=
        h2.const_mul 16
      have hAB := h44.add hB
      have hABC := hAB.add hC
      have hABCD := hABC.add hD
      have hABCDE := hABCD.add hE
      simp only [mul_assoc]
      have eABCDE :
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x) + 4 * H₄ x +
            16 * H₂ x ^ 2 + 16 * H₂ x + 4 ∂gaussianReal 0 1) =
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x) + 4 * H₄ x +
            16 * H₂ x ^ 2 + 16 * H₂ x ∂gaussianReal 0 1) + 4 := by
        simpa only [Pi.add_apply, integral_const, probReal_univ, one_smul] using
          (integral_add hABCDE (integrable_const 4))
      have eABCD :
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x) + 4 * H₄ x +
            16 * H₂ x ^ 2 + 16 * H₂ x ∂gaussianReal 0 1) =
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x) + 4 * H₄ x +
            16 * H₂ x ^ 2 ∂gaussianReal 0 1) +
          (∫ x, 16 * H₂ x ∂gaussianReal 0 1) := by
        simpa only [Pi.add_apply] using integral_add hABCD hE
      have eABC :
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x) + 4 * H₄ x +
            16 * H₂ x ^ 2 ∂gaussianReal 0 1) =
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x) + 4 * H₄ x
            ∂gaussianReal 0 1) +
          (∫ x, 16 * H₂ x ^ 2 ∂gaussianReal 0 1) := by
        simpa only [Pi.add_apply] using integral_add hABC hD
      have eAB :
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x) + 4 * H₄ x
            ∂gaussianReal 0 1) =
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x)
            ∂gaussianReal 0 1) +
          (∫ x, 4 * H₄ x ∂gaussianReal 0 1) := by
        simpa only [Pi.add_apply] using integral_add hAB hC
      have eA :
          (∫ x, H₄ x ^ 2 + 8 * (H₄ x * H₂ x)
            ∂gaussianReal 0 1) =
          (∫ x, H₄ x ^ 2 ∂gaussianReal 0 1) +
          (∫ x, 8 * (H₄ x * H₂ x) ∂gaussianReal 0 1) := by
        simpa only [Pi.add_apply] using integral_add h44 hB
      rw [eABCDE, eABCD, eABC, eAB, eA]
      norm_num [integral_const_mul, e44, e42, e4, e22, e2]

/-- The fourth-moment calculation also supplies the `L⁴` input for finite sums. -/
theorem centeredGaussianSquare_memLp_four :
    MemLp centeredGaussianSquare 4 (gaussianReal 0 1) := by
  have h_int : Integrable (fun x => centeredGaussianSquare x ^ 4)
      (gaussianReal 0 1) :=
    Integrable.of_integral_ne_zero (by rw [centeredGaussianSquare_fourth_moment]; norm_num)
  have h_norm : Integrable (fun x => ‖centeredGaussianSquare x‖ ^ 4)
      (gaussianReal 0 1) := by
    convert h_int using 1
    funext x
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  apply (integrable_norm_rpow_iff (by fun_prop) (by norm_num) (by norm_num)).mp
  simpa using h_norm

theorem centeredGaussianSquares_sum_memLp_four {ι : Type*} [Fintype ι] :
    MemLp (fun g : ι → ℝ => ∑ i : ι, centeredGaussianSquare (g i)) 4
      (gaussianCouplings ι) := by
  classical
  apply memLp_finsetSum Finset.univ
  intro i _
  have hmap : Measure.map (fun g : ι → ℝ => g i) (gaussianCouplings ι) =
      gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq
  have h := centeredGaussianSquare_memLp_four
  rw [← hmap] at h
  simpa only [Function.comp_def] using h.comp_of_map
    ((by fun_prop : Measurable (fun g : ι → ℝ => g i)).aemeasurable)

end SYK.CLT
