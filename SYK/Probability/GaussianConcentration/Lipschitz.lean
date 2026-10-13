import SYK.Probability.GaussianConcentration.Smooth
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Probability.Moments.SubGaussian

/-!
# Mollification of Lipschitz functions

To pass from the smooth Gaussian covariance bound to the general Lipschitz case we approximate
an `L`-Lipschitz function `F` by a sequence of `C¹` functions with the same Lipschitz constant,
obtained by convolving `F` with a normalized `ContDiffBump`.  The key output is
`SYK.GaussianConcentration.exists_smooth_lipschitz_approx`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SYK.GaussianConcentration

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
        have : ∀ n : ℕ, ∃ ψ : ContDiffBump (0 : EuclideanSpace ℝ ι),
          ψ.rIn = 1 / (n + 2) ∧ ψ.rOut = 2 / (n + 2) := by
          intro n
          use ⟨1 / (n + 2), 2 / (n + 2), by positivity, by rw [div_lt_div_iff_of_pos_right
                                                            (by positivity)]; norm_num⟩;
        choose ψ hψ using this;
        refine ⟨ fun n => convolution ( ( ψ n ).normed volume ) F ( ContinuousLinearMap.lsmul ℝ ℝ )
          volume, ?_, ?_, ?_, ?_ ⟩;
        · intro n;
          apply_rules [ HasCompactSupport.contDiff_convolution_left ];
          · exact ( ψ n ).hasCompactSupport_normed;
          · exact ContDiffBump.contDiff_normed _;
          · exact hLip.continuous.locallyIntegrable;
        · intro n;
          refine LipschitzWith.of_dist_le_mul ?_;
          intro x y;
          simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
            Real.coe_toNNReal'];
          rw [ dist_eq_norm, ← MeasureTheory.integral_sub ];
          · refine le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans
              ( MeasureTheory.integral_mono_of_nonneg
                (g := fun a => ( ψ n ).normed volume a * ( L.toNNReal * dist x y )) ?_ ?_ ?_ ) ?_ );
            · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
            · exact MeasureTheory.Integrable.mul_const ( ContDiffBump.integrable_normed _ ) _;
            · filter_upwards [ ] with a;
              rw [ ← mul_sub, norm_mul, Real.norm_of_nonneg ( by exact ( ψ n ).nonneg_normed _ ) ];
              exact mul_le_mul_of_nonneg_left ( hLip.dist_le_mul _ _ )
                ( by exact ( ψ n ).nonneg_normed _ ) |> le_trans <| by simp
                                                                        [ dist_eq_norm ] ;
            · rw [ MeasureTheory.integral_mul_const, ( ψ n ).integral_normed ]
              simp only [one_mul, Real.coe_toNNReal', le_refl]
          · refine Continuous.integrable_of_hasCompactSupport ?_ ?_;
            · exact Continuous.mul ( ContDiffBump.continuous_normed _ ) ( hLip.continuous.comp
                ( continuous_const.sub continuous_id' ) );
            · have h_compact_support : HasCompactSupport (fun t => (ψ n).normed volume t) := by
                convert ( ψ n ).hasCompactSupport_normed; all_goals infer_instance;
              exact h_compact_support.mono fun t ht => Function.support_mul_subset_left _ _ ht
          · refine Continuous.integrable_of_hasCompactSupport ?_ ?_;
            · exact Continuous.mul ( ContDiffBump.continuous_normed _ ) ( hLip.continuous.comp
                ( continuous_const.sub continuous_id' ) );
            · have h_compact_support : HasCompactSupport (fun t => (ψ n).normed volume t) := by
                convert ( ψ n ).hasCompactSupport_normed; all_goals infer_instance;
              exact h_compact_support.mono fun x hx => Function.support_mul_subset_left _ _ hx
        · intro n x
          have h_bound : ∀ t ∈ Metric.ball (0 : EuclideanSpace ℝ ι) ((ψ n).rOut),
            |F (x - t)| ≤ |F 0| + L + L * ‖x‖ := by
            intro t ht
            have h_bound : |F (x - t)| ≤ |F 0| + L * ‖x - t‖ := by
              have := hLip.dist_le_mul ( x - t ) 0;
              simp_all only [one_div, Metric.mem_ball, dist_eq_norm, sub_zero,
                Real.norm_eq_abs, Real.coe_toNNReal', sup_of_le_left, ge_iff_le];
              exact abs_le.mpr ⟨ by cases abs_cases ( F 0 ) <;> linarith [ abs_le.mp this ],
                                     by cases abs_cases ( F 0 ) <;> linarith [ abs_le.mp this ] ⟩;
            have h_bound : ‖x - t‖ ≤ ‖x‖ + ‖t‖ := by
              exact norm_sub_le x t;
            have h_bound : ‖t‖ ≤ 1 := by
              simp_all only [one_div, Metric.mem_ball, dist_zero_right];
              exact ht.le.trans ( by rw [ div_le_iff₀ ] <;> linarith );
            nlinarith [ abs_nonneg ( F 0 ), abs_nonneg ( F ( x - t ) ) ];
          have h_integral_bound : ∫ t, |(ψ n).normed volume t * F (x - t)| ∂volume ≤ ∫ t,
            (ψ n).normed volume t * (|F 0| + L + L * ‖x‖) ∂volume := by
            refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_;
            · exact Filter.Eventually.of_forall fun t => abs_nonneg _;
            · exact MeasureTheory.Integrable.mul_const ( ContDiffBump.integrable_normed _ ) _;
            · filter_upwards [ ] with t;
              by_cases ht : t ∈ Metric.ball 0 (ψ n).rOut;
              · rw [ abs_mul, abs_of_nonneg ( show 0 ≤ ( ψ n ).normed volume t from _ ) ];
                · exact mul_le_mul_of_nonneg_left ( h_bound t ht ) ( by exact ( ψ n ).nonneg_normed
                                                                         t );
                · exact ( ψ n ).nonneg_normed t;
              · have hz : ( ψ n ).normed volume t = 0 :=
                  not_not.mp fun h => ht <|
                    by simpa using ( ψ n ).support_normed_eq.subset <| by simpa using h
                rw [ hz ]
                norm_num
          refine le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : EuclideanSpace ℝ ι →
            ℝ ) ) ( h_integral_bound.trans ?_ );
          rw [ MeasureTheory.integral_mul_const, ContDiffBump.integral_normed ] ; norm_num;
        · apply ContDiffBump.convolution_tendsto_right_of_continuous;
          · simpa only [ hψ ] using tendsto_const_nhds.div_atTop
              ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
          · exact hLip.continuous;
  refine ⟨ Fn, hFn.1, ?_, hFn.2.2.1, hFn.2.2.2 ⟩;
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
      ∧ Filter.Tendsto (fun n => ∫ x, Fn n x * Real.exp (s * Fn n x)
        ∂(standardGaussianMeasureOnEuclidean ι))
        Filter.atTop (nhds (∫ x, F x * Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι)))
          := by
  refine ⟨ ?_, ?_, ?_ ⟩;
  · refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => C + L * ‖x‖) ?_ ?_ ?_ ?_;
    · exact fun n => ( hcont n |> Continuous.aestronglyMeasurable );
    · refine MeasureTheory.Integrable.add ?_ ?_;
      · exact MeasureTheory.integrable_const _;
      · have h_integrable : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖)
          (standardGaussianMeasureOnEuclidean ι) := by
          convert integrable_exp_mul_norm 1 |> fun h => h.mono' _ _ using 1;
          · exact Continuous.aestronglyMeasurable ( continuous_norm );
          · filter_upwards [ ] with x using by simpa using le_trans ( by norm_num )
                                                ( Real.add_one_le_exp _ ) ;
        exact h_integrable.const_mul L;
    · exact fun n => Filter.Eventually.of_forall ( hbound n );
    · exact Filter.Eventually.of_forall htend;
  · refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => Real.exp ( |s| * ( C + L * ‖x‖ ) )) ?_ ?_ ?_ ?_;
    · exact fun n => Continuous.aestronglyMeasurable ( Real.continuous_exp.comp
        ( continuous_const.mul ( hcont n ) ) );
    · convert integrable_exp_mul_norm ( |s| * L ) |> fun h => h.const_mul ( Real.exp ( |s| * C ) )
        using 1 ; ext ; rw [ ← Real.exp_add ] ; congr 1 ; ring
    · intro n; filter_upwards [ ] with x; rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ;
        exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( hbound n
                                        x ) ] ) ;
    · exact Filter.Eventually.of_forall fun x => Real.continuous_exp.continuousAt.tendsto.comp
        ( Filter.Tendsto.mul tendsto_const_nhds ( htend x ) );
  · refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => ( C + L * ‖x‖ ) * Real.exp ( |s| * ( C + L * ‖x‖ ) )) ?_ ?_ ?_ ?_;
    · exact fun n => Continuous.aestronglyMeasurable
        ( by exact Continuous.mul ( hcont n ) ( Real.continuous_exp.comp ( continuous_const.mul
              ( hcont n ) ) ) );
    · have h_integrable : Integrable (fun x => (C + L * ‖x‖) * Real.exp (|s| * L * ‖x‖))
        (standardGaussianMeasureOnEuclidean ι) := by
        have h_integrable : Integrable (fun x => ‖x‖ * Real.exp (|s| * L * ‖x‖))
          (standardGaussianMeasureOnEuclidean ι) := by
          convert integrable_exp_mul_norm ( |s| * L + 1 ) |> fun h => h.mono' _ _ using 1;
          · exact Continuous.aestronglyMeasurable ( by continuity );
          · filter_upwards [ ] with x using by
              rw [ Real.norm_of_nonneg ( by positivity ) ]
              rw [ add_mul, one_mul, Real.exp_add ]
              nlinarith [ Real.add_one_le_exp ( |s| * L * ‖x‖ ), Real.add_one_le_exp ‖x‖,
                norm_nonneg x, show 0 ≤ |s| * L * ‖x‖ by positivity ]
        simp_all only [mul_assoc, add_mul];
        refine MeasureTheory.Integrable.add ?_ ?_;
        · have h_integrable : Integrable (fun x => Real.exp (|s| * L * ‖x‖))
            (standardGaussianMeasureOnEuclidean ι) := by
            convert integrable_exp_mul_norm ( |s| * L ) using 1;
          simpa only [ mul_assoc ] using h_integrable.const_mul C;
        · exact h_integrable.const_mul L;
      convert h_integrable.const_mul ( Real.exp ( |s| * C ) ) using 2
      rw [ mul_add, Real.exp_add, ← mul_assoc |s| L ]; ring
    · intro n
      simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp];
      filter_upwards [ ] with x using mul_le_mul ( hbound n x ) ( Real.exp_le_exp.mpr
        ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( hbound n x ) ] ) ) ( by positivity )
        ( by positivity );
    · exact Filter.Eventually.of_forall fun x => Filter.Tendsto.mul ( htend x )
        ( Real.continuous_exp.continuousAt.tendsto.comp ( tendsto_const_nhds.mul ( htend x ) ) )

/-- The sharp Gaussian covariance bound for an `L`-Lipschitz function, obtained from the
smooth bound by mollification and dominated convergence. -/
lemma gaussian_cov_bound {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  obtain ⟨Fn, hCD, hgrad, hbound, htend⟩ :=
    exists_smooth_lipschitz_approx F L hL.le hLip
  obtain ⟨hmean, hexp, hweighted⟩ := tendsto_integrals_of_approx
    F Fn (|F 0| + L) L (by positivity) hL.le
    (fun n => (hCD n).continuous) hbound htend s
  convert le_of_tendsto_of_tendsto'
    (Filter.Tendsto.abs (hweighted.sub (hmean.mul hexp)))
    (hexp.const_mul (L ^ 2 * |s|)) _ using 1
  exact fun n => gaussian_cov_bound_smooth _ _ hL.le (hCD n) (hgrad n) s

/-- The centered Lipschitz function of a standard Gaussian vector satisfies the
moment-generating-function estimate with variance proxy `L ^ 2`. -/
theorem product_standardGaussian_mgf_le
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
        (standardGaussianMeasureOnEuclidean ι) t ≤
      Real.exp (L ^ 2 * t ^ 2 / 2) :=
  herbst_of_cov_bound F L hLip (gaussian_cov_bound F L hL hLip) t

/-- A function with Lipschitz constant zero is constant. -/
lemma eq_const_of_lipschitz_zero {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hLip : LipschitzWith (0 : ℝ≥0) F) (x : EuclideanSpace ℝ ι) :
    F x = F 0 := by
  apply dist_eq_zero.mp
  apply le_antisymm
  · simpa using hLip.dist_le_mul x 0
  · exact dist_nonneg

/-- Centering a zero-Lipschitz function under the standard Gaussian measure
gives the zero function. -/
theorem centered_eq_zero_of_lipschitz_zero {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ)
    (hLip : LipschitzWith (0 : ℝ≥0) F) (x : EuclideanSpace ℝ ι) :
    F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι = 0 := by
  have hconst : ∀ y, F y = F 0 := fun y => eq_const_of_lipschitz_zero F hLip y
  have hmean : ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι = F 0 := by
    simp_rw [hconst]
    simp
  rw [hconst x, hmean, sub_self]

/-- The centered Lipschitz function of a standard Gaussian vector has a
sub-Gaussian moment-generating function with parameter `L ^ 2`, including
the degenerate case `L = 0`. -/
theorem product_standardGaussian_hasSubgaussianMGF
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : LipschitzWith L.toNNReal F) :
    HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
      (Real.toNNReal (L ^ 2)) (standardGaussianMeasureOnEuclidean ι) := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst L
    have hcenter :
        (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) =
          (fun _ => 0) := by
      funext x
      exact centered_eq_zero_of_lipschitz_zero F (by simpa using hLip) x
    simp [hcenter]
  · refine ⟨fun t => ?_, fun t => ?_⟩
    · apply integrable_exp_smul_lipschitz
        (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) L
      simpa only [add_zero] using hLip.sub
        (LipschitzWith.const (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι))
    · have hmgf := product_standardGaussian_mgf_le F L hLpos hLip t
      have hcoe : ((Real.toNNReal (L ^ 2) : ℝ≥0) : ℝ) = L ^ 2 :=
        Real.coe_toNNReal _ (sq_nonneg L)
      rw [hcoe]
      exact hmgf

/-- Upper-tail concentration for a positive Lipschitz constant. -/
theorem product_standardGaussian_upper_tail
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  set μ := standardGaussianMeasureOnEuclidean ι
  have hsg := product_standardGaussian_hasSubgaussianMGF F L hL.le hLip
  have hchern := hsg.measure_ge_le (ε := t) ht.le
  have hcoe : ((Real.toNNReal (L ^ 2) : ℝ≥0) : ℝ) = L ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg L)
  rw [hcoe] at hchern
  have hsubset :
      {x | F x - ∫ y, F y ∂μ > t} ⊆
        {x | t ≤ F x - ∫ y, F y ∂μ} := by
    intro x hx
    change t < F x - ∫ y, F y ∂μ at hx
    change t ≤ F x - ∫ y, F y ∂μ
    exact le_of_lt hx
  calc
    μ {x | F x - ∫ y, F y ∂μ > t}
        ≤ μ {x | t ≤ F x - ∫ y, F y ∂μ} := measure_mono hsubset
    _ = ENNReal.ofReal (μ.real {x | t ≤ F x - ∫ y, F y ∂μ}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
          ENNReal.ofReal_le_ofReal hchern

/-- Lower-tail concentration for a positive Lipschitz constant. -/
theorem product_standardGaussian_lower_tail
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  convert product_standardGaussian_upper_tail (fun x => -F x) L t hL ht hLip.neg using 2
  · simp only [sub_eq_neg_add]
    rw [MeasureTheory.integral_neg]
    ext
    simp [add_comm]

theorem abs_gt_iff_pos_or_neg {a t : ℝ} : |a| > t ↔ a > t ∨ -a > t := by
  rw [abs_eq_max_neg, gt_iff_lt, gt_iff_lt, gt_iff_lt, lt_max_iff, lt_neg]

/-- Two-sided Gaussian concentration for a positive Lipschitz constant. -/
theorem euclidean_lipschitz_gaussian_concentration
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | |F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  have hexp : (0 : ℝ) ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := Real.exp_nonneg _
  have hsubset :
      {x | |F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι| > t} ⊆
        {x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} ∪
          {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t} := by
    intro x hx
    rcases abs_gt_iff_pos_or_neg.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [neg_sub] using h)
  calc
    standardGaussianMeasureOnEuclidean ι
          {x | |F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι| > t}
        ≤ standardGaussianMeasureOnEuclidean ι
            ({x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} ∪
              {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t}) :=
          measure_mono hsubset
    _ ≤ standardGaussianMeasureOnEuclidean ι
            {x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} +
          standardGaussianMeasureOnEuclidean ι
            {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t} :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) +
          ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
          add_le_add (product_standardGaussian_upper_tail F L t hL ht hLip)
            (product_standardGaussian_lower_tail F L t hL ht hLip)
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
          rw [← ENNReal.ofReal_add hexp hexp]
          congr 1
          ring

end SYK.GaussianConcentration
