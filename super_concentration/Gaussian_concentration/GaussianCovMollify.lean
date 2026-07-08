import SYK.super_concentration.Gaussian_concentration.GaussianConcentrationAux

/-!
# Mollification of Lipschitz functions

To pass from the smooth Gaussian covariance bound to the general Lipschitz case we approximate
an `L`-Lipschitz function `F` by a sequence of `C¹` functions with the same Lipschitz constant,
obtained by convolving `F` with a normalized `ContDiffBump`.  The key output is
`SYK.exists_smooth_lipschitz_approx`.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SYK

/-
Approximation of an `L`-Lipschitz function on a finite-dimensional Euclidean space by a
sequence of `C¹` functions with gradient bounded by `L`, uniform linear growth, and pointwise
convergence.  Obtained by convolution with a normalized `ContDiffBump` of shrinking radius.
-/
lemma exists_smooth_lipschitz_approx {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : LipschitzWith L.toNNReal F) :
    ∃ Fn : ℕ → EuclideanSpace ℝ ι → ℝ,
      (∀ n, ContDiff ℝ 1 (Fn n)) ∧
      (∀ n x, ‖gradient (Fn n) x‖ ≤ L) ∧
      (∀ n x, |Fn n x| ≤ (|F 0| + L) + L * ‖x‖) ∧
      (∀ x, Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (F x))) := by
  obtain ⟨Fn, hFn⟩ : ∃ (Fn : ℕ → (EuclideanSpace ℝ ι → ℝ)),
      (∀ n, ContDiff ℝ 1 (Fn n)) ∧
      (∀ n, LipschitzWith L.toNNReal (Fn n)) ∧
      (∀ n x, |Fn n x| ≤ |F 0| + L + L * ‖x‖) ∧
      (∀ x, Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (F x))) := by
        have : ∀ n : ℕ, ∃ ψ : ContDiffBump (0 : EuclideanSpace ℝ ι), ψ.rIn = 1 / (n + 2) ∧ ψ.rOut = 2 / (n + 2) := by
          intro n
          use ⟨1 / (n + 2), 2 / (n + 2), by positivity, by rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩;
        choose ψ hψ using this;
        refine' ⟨ fun n => convolution ( ( ψ n ).normed volume ) F ( ContinuousLinearMap.lsmul ℝ ℝ ) volume, _, _, _, _ ⟩;
        · intro n;
          apply_rules [ HasCompactSupport.contDiff_convolution_left ];
          · exact ( ψ n ).hasCompactSupport_normed;
          · exact ContDiffBump.contDiff_normed _;
          · exact hLip.continuous.locallyIntegrable;
        · intro n;
          refine' LipschitzWith.of_dist_le_mul _;
          intro x y;
          simp +decide [ convolution_def ];
          rw [ dist_eq_norm, ← MeasureTheory.integral_sub ];
          · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
            refine' fun a => ( ψ n ).normed volume a * ( L.toNNReal * dist x y );
            · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
            · exact MeasureTheory.Integrable.mul_const ( ContDiffBump.integrable_normed _ ) _;
            · filter_upwards [ ] with a;
              rw [ ← mul_sub, norm_mul, Real.norm_of_nonneg ( by exact ( ψ n ).nonneg_normed _ ) ];
              exact mul_le_mul_of_nonneg_left ( hLip.dist_le_mul _ _ ) ( by exact ( ψ n ).nonneg_normed _ ) |> le_trans <| by simp +decide [ dist_eq_norm ] ;
            · rw [ MeasureTheory.integral_mul_const, ( ψ n ).integral_normed ] ; aesop;
          · refine' Continuous.integrable_of_hasCompactSupport _ _;
            · exact Continuous.mul ( ContDiffBump.continuous_normed _ ) ( hLip.continuous.comp ( continuous_const.sub continuous_id' ) );
            · have h_compact_support : HasCompactSupport (fun t => (ψ n).normed volume t) := by
                convert ( ψ n ).hasCompactSupport_normed; all_goals infer_instance;
              exact h_compact_support.mono fun t ht => by aesop;
          · refine' Continuous.integrable_of_hasCompactSupport _ _;
            · exact Continuous.mul ( ContDiffBump.continuous_normed _ ) ( hLip.continuous.comp ( continuous_const.sub continuous_id' ) );
            · have h_compact_support : HasCompactSupport (fun t => (ψ n).normed volume t) := by
                convert ( ψ n ).hasCompactSupport_normed; all_goals infer_instance;
              exact h_compact_support.mono fun x hx => by aesop;
        · intro n x
          have h_bound : ∀ t ∈ Metric.ball (0 : EuclideanSpace ℝ ι) ((ψ n).rOut), |F (x - t)| ≤ |F 0| + L + L * ‖x‖ := by
            intro t ht
            have h_bound : |F (x - t)| ≤ |F 0| + L * ‖x - t‖ := by
              have := hLip.dist_le_mul ( x - t ) 0;
              simp_all +decide [ dist_eq_norm ];
              exact abs_le.mpr ⟨ by cases abs_cases ( F 0 ) <;> linarith [ abs_le.mp this ], by cases abs_cases ( F 0 ) <;> linarith [ abs_le.mp this ] ⟩;
            have h_bound : ‖x - t‖ ≤ ‖x‖ + ‖t‖ := by
              exact norm_sub_le x t;
            have h_bound : ‖t‖ ≤ 1 := by
              simp_all +decide [ Metric.mem_ball ];
              exact ht.le.trans ( by rw [ div_le_iff₀ ] <;> linarith );
            nlinarith [ abs_nonneg ( F 0 ), abs_nonneg ( F ( x - t ) ) ];
          have h_integral_bound : ∫ t, |(ψ n).normed volume t * F (x - t)| ∂volume ≤ ∫ t, (ψ n).normed volume t * (|F 0| + L + L * ‖x‖) ∂volume := by
            refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
            · exact Filter.Eventually.of_forall fun t => abs_nonneg _;
            · exact MeasureTheory.Integrable.mul_const ( ContDiffBump.integrable_normed _ ) _;
            · filter_upwards [ ] with t;
              by_cases ht : t ∈ Metric.ball 0 (ψ n).rOut;
              · rw [ abs_mul, abs_of_nonneg ( show 0 ≤ ( ψ n ).normed volume t from _ ) ];
                · exact mul_le_mul_of_nonneg_left ( h_bound t ht ) ( by exact ( ψ n ).nonneg_normed t );
                · exact ( ψ n ).nonneg_normed t;
              · rw [ show ( ψ n ).normed volume t = 0 from _ ] ; norm_num;
                exact not_not.mp fun h => ht <| by simpa using ( ψ n ).support_normed_eq.subset <| by simpa using h;
          refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : EuclideanSpace ℝ ι → ℝ ) ) ( h_integral_bound.trans _ );
          rw [ MeasureTheory.integral_mul_const, ContDiffBump.integral_normed ] ; norm_num;
        · apply ContDiffBump.convolution_tendsto_right_of_continuous;
          · simpa only [ hψ ] using tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
          · exact hLip.continuous;
  refine' ⟨ Fn, hFn.1, _, hFn.2.2.1, hFn.2.2.2 ⟩;
  intro n x
  have h_grad : ‖fderiv ℝ (Fn n) x‖ ≤ L := by
    convert norm_fderiv_le_of_lipschitz ℝ ( hFn.2.1 n ) using 1;
    rw [ Real.coe_toNNReal _ hL ]
  simp [gradient, h_grad]

/-
Dominated-convergence transfer of the three relevant integrals along a uniformly
linearly-bounded, pointwise-convergent approximating sequence.
-/
lemma tendsto_integrals_of_approx {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (Fn : ℕ → EuclideanSpace ℝ ι → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hcont : ∀ n, Continuous (Fn n))
    (hbound : ∀ n x, |Fn n x| ≤ C + L * ‖x‖)
    (htend : ∀ x, Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (F x))) (s : ℝ) :
    Filter.Tendsto (fun n => ∫ x, Fn n x ∂(standardGaussianMeasureOnEuclidean ι))
        Filter.atTop (nhds (∫ x, F x ∂(standardGaussianMeasureOnEuclidean ι)))
      ∧ Filter.Tendsto (fun n => ∫ x, Real.exp (s * Fn n x) ∂(standardGaussianMeasureOnEuclidean ι))
        Filter.atTop (nhds (∫ x, Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι)))
      ∧ Filter.Tendsto (fun n => ∫ x, Fn n x * Real.exp (s * Fn n x) ∂(standardGaussianMeasureOnEuclidean ι))
        Filter.atTop (nhds (∫ x, F x * Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι))) := by
  refine' ⟨ _, _, _ ⟩;
  · refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => C + L * ‖x‖;
    · exact fun n => ( hcont n |> Continuous.aestronglyMeasurable );
    · refine' MeasureTheory.Integrable.add _ _;
      · exact MeasureTheory.integrable_const _;
      · have h_integrable : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖) (standardGaussianMeasureOnEuclidean ι) := by
          convert integrable_exp_mul_norm 1 |> fun h => h.mono' _ _ using 1;
          · exact Continuous.aestronglyMeasurable ( continuous_norm );
          · filter_upwards [ ] with x using by simpa using le_trans ( by norm_num ) ( Real.add_one_le_exp _ ) ;
        exact h_integrable.const_mul L;
    · exact fun n => Filter.Eventually.of_forall ( hbound n );
    · exact Filter.Eventually.of_forall htend;
  · refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => Real.exp ( |s| * ( C + L * ‖x‖ ) );
    · exact fun n => Continuous.aestronglyMeasurable ( Real.continuous_exp.comp ( continuous_const.mul ( hcont n ) ) );
    · convert integrable_exp_mul_norm ( |s| * L ) |> fun h => h.const_mul ( Real.exp ( |s| * C ) ) using 1 ; ext ; ring;
      rw [ ← Real.exp_add ];
    · intro n; filter_upwards [ ] with x; rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( hbound n x ) ] ) ;
    · exact Filter.Eventually.of_forall fun x => Real.continuous_exp.continuousAt.tendsto.comp ( Filter.Tendsto.mul tendsto_const_nhds ( htend x ) );
  · refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => ( C + L * ‖x‖ ) * Real.exp ( |s| * ( C + L * ‖x‖ ) );
    · exact fun n => Continuous.aestronglyMeasurable ( by exact Continuous.mul ( hcont n ) ( Real.continuous_exp.comp ( continuous_const.mul ( hcont n ) ) ) );
    · have h_integrable : Integrable (fun x => (C + L * ‖x‖) * Real.exp (|s| * L * ‖x‖)) (standardGaussianMeasureOnEuclidean ι) := by
        have h_integrable : Integrable (fun x => ‖x‖ * Real.exp (|s| * L * ‖x‖)) (standardGaussianMeasureOnEuclidean ι) := by
          convert integrable_exp_mul_norm ( |s| * L + 1 ) |> fun h => h.mono' _ _ using 1;
          · exact Continuous.aestronglyMeasurable ( by continuity );
          · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ add_mul, one_mul, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp ( |s| * L * ‖x‖ ), Real.add_one_le_exp ‖x‖, norm_nonneg x, show 0 ≤ |s| * L * ‖x‖ by positivity ] ;
        simp_all +decide [ add_mul, mul_assoc ];
        refine' MeasureTheory.Integrable.add _ _;
        · have h_integrable : Integrable (fun x => Real.exp (|s| * L * ‖x‖)) (standardGaussianMeasureOnEuclidean ι) := by
            convert integrable_exp_mul_norm ( |s| * L ) using 1;
          simpa only [ mul_assoc ] using h_integrable.const_mul C;
        · exact h_integrable.const_mul L;
      convert h_integrable.const_mul ( Real.exp ( |s| * C ) ) using 2 ; ring;
      simp only [mul_assoc, ← Real.exp_add];
    · intro n
      simp [hbound];
      filter_upwards [ ] with x using mul_le_mul ( hbound n x ) ( Real.exp_le_exp.mpr ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( hbound n x ) ] ) ) ( by positivity ) ( by positivity );
    · exact Filter.Eventually.of_forall fun x => Filter.Tendsto.mul ( htend x ) ( Real.continuous_exp.continuousAt.tendsto.comp ( tendsto_const_nhds.mul ( htend x ) ) )

end SYK
