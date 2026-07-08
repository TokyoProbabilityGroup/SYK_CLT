import SYK.super_concentration.Gaussian_concentration.GaussianConcentrationAux
import SYK.super_concentration.Gaussian_concentration.GaussianCovSmooth
import SYK.super_concentration.Gaussian_concentration.GaussianCovMollify

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK

/-
The sharp Gaussian covariance bound for a `C¹` function with globally bounded gradient
(the smooth case, proved via rotation invariance of `μ.prod μ` and Gaussian integration by
parts).  The general Lipschitz case follows by mollification.
-/
lemma gaussian_cov_bound_smooth {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  rw [ gaussian_cov_repr F L hL hF hgrad s ];
  rw [ intervalIntegral.integral_of_le Real.pi_div_two_pos.le ];
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun θ => |Real.sin θ| * ( |s| * L ^ 2 * ∫ x, Real.exp ( s * F x ) ∂standardGaussianMeasureOnEuclidean ι );
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · exact Continuous.integrableOn_Ioc ( by continuity );
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with θ hθ;
    simpa only [ norm_mul, Real.norm_eq_abs ] using mul_le_mul_of_nonneg_left ( gaussian_cov_H_bound F L hL hF hgrad s θ ) ( abs_nonneg _ );
  · rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ abs_of_nonneg ( Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le ( by linarith [ Real.pi_pos, hx.2 ] ) ) ], ← intervalIntegral.integral_of_le Real.pi_div_two_pos.le ] ; norm_num ; ring_nf ; norm_num

/-
**The sharp Gaussian covariance bound** for an `L`-Lipschitz `F`:
`|Cov(F, e^{sF})| ≤ L² |s| ∫ e^{sF}` against the standard Gaussian.  This is the last
remaining analytic input to `product_standardGaussian_mgf_le`.  It reduces to the smooth
case `gaussian_cov_bound_smooth` (proved via rotation invariance of `μ.prod μ` and the
Gaussian integration-by-parts lemma `gaussian_ibp`) by mollifying `F` into a sequence of
`C¹` functions with the same Lipschitz constant and passing to the limit by dominated
convergence.  The supporting infrastructure (`gaussian_ibp`, `map_rotation_fst`,
`gradient_exp_smul`, `contDiff_abs_le_of_gradient_le`, the mean-zero and integrability
lemmas) is fully proved; the smooth-case assembly and the mollification limit remain.
-/
lemma gaussian_cov_bound {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  obtain ⟨Fn, hCD, hgr, hbd, htd⟩ := SYK.exists_smooth_lipschitz_approx F L hL.le hLip;
  obtain ⟨t1, t2, t3⟩ := SYK.tendsto_integrals_of_approx F Fn (|F 0| + L) L (by positivity) hL.le (fun n => (hCD n).continuous) hbd htd s;
  convert le_of_tendsto_of_tendsto' ( Filter.Tendsto.abs ( t3.sub ( t1.mul t2 ) ) ) ( t2.const_mul ( L ^ 2 * |s| ) ) _ using 1;
  exact fun n => gaussian_cov_bound_smooth _ _ hL.le ( hCD n ) ( hgr n ) s

/-- The centered Lipschitz function of a standard Gaussian vector has a sub-Gaussian
moment-generating function with parameter `L ^ 2`.  This is Herbst's conclusion from the
Gaussian logarithmic Sobolev inequality: for every `t`,
`𝔼[exp (t (F - 𝔼 F))] ≤ exp (L² t² / 2)`.

This is the analytic heart of Gaussian concentration and is not currently available in
Mathlib; a full proof requires the Gaussian log-Sobolev inequality (or the equivalent
Ornstein–Uhlenbeck semigroup interpolation) together with Rademacher's theorem
(`LipschitzWith.ae_differentiableAt`) giving `‖∇F‖ ≤ L` almost everywhere. -/
theorem product_standardGaussian_mgf_le
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
        (standardGaussianMeasureOnEuclidean ι) t ≤
      Real.exp (L ^ 2 * t ^ 2 / 2) :=
  herbst_of_cov_bound F L hL hLip (gaussian_cov_bound F L hL hLip) t

/-- The centered Lipschitz function of a standard Gaussian vector has a sub-Gaussian
moment-generating function with parameter `L ^ 2`. -/
theorem product_standardGaussian_hasSubgaussianMGF
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) :
    HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
      (Real.toNNReal (L ^ 2)) (standardGaussianMeasureOnEuclidean ι) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · -- Integrability of `exp (t · (F - ∫ F))`.
    have hbound : ∀ x : EuclideanSpace ℝ ι, |F x| ≤ |F 0| + L * ‖x‖ := by
      intro x
      have h := hLip.dist_le_mul x 0
      simp only [dist_eq_norm, sub_zero, Real.coe_toNNReal L hL.le] at h
      cases abs_cases (F x) <;> cases abs_cases (F 0) <;>
        [skip; skip; skip; skip] <;> nlinarith [abs_le.mp h, norm_nonneg x]
    set μ := standardGaussianMeasureOnEuclidean ι
    have hdom := (integrable_exp_mul_norm (ι := ι) (|t| * L)).const_mul
      (Real.exp (|t| * |F 0| + |t| * |∫ y, F y ∂μ|))
    refine hdom.mono' ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul
        ((hLip.continuous).sub continuous_const))).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hFx : F x - ∫ y, F y ∂μ ≤ |F 0| + L * ‖x‖ + |∫ y, F y ∂μ| := by
        have := abs_le.mp (hbound x)
        have h2 := neg_abs_le (∫ y, F y ∂μ)
        nlinarith [this.1, this.2]
      have hneg : -(|F 0| + L * ‖x‖ + |∫ y, F y ∂μ|) ≤ F x - ∫ y, F y ∂μ := by
        have := abs_le.mp (hbound x)
        have h2 := le_abs_self (∫ y, F y ∂μ)
        nlinarith [this.1, this.2]
      have hnn : (0:ℝ) ≤ L * ‖x‖ := mul_nonneg hL.le (norm_nonneg x)
      rcases abs_cases t with ⟨ht, _⟩ | ⟨ht, _⟩ <;> rw [ht] <;> nlinarith [hFx, hneg, hnn]
  · -- The moment-generating-function bound, from the deep Herbst inequality.
    have hmgf := product_standardGaussian_mgf_le F L hL hLip t
    have hcoe : ((Real.toNNReal (L ^ 2) : ℝ≥0) : ℝ) = L ^ 2 :=
      Real.coe_toNNReal _ (sq_nonneg L)
    rw [hcoe]
    exact hmgf

/-- Upper-tail concentration for Lipschitz functions of a standard Gaussian vector. -/
theorem product_standardGaussian_upper_tail
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  set μ := standardGaussianMeasureOnEuclidean ι with hμ
  have hsg := product_standardGaussian_hasSubgaussianMGF F L hL hLip
  have hchern := hsg.measure_ge_le (ε := t) ht.le
  have hcoe : ((Real.toNNReal (L ^ 2) : ℝ≥0) : ℝ) = L ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg L)
  rw [hcoe] at hchern
  -- `hchern : μ.real {ω | t ≤ F ω - ∫ F} ≤ exp (-t ^ 2 / (2 * L ^ 2))`
  have hsubset :
      {x | F x - ∫ y, F y ∂μ > t} ⊆
        {x | t ≤ F x - ∫ y, F y ∂μ} := by
    intro x hx
    simp only [Set.mem_setOf_eq, gt_iff_lt] at hx ⊢
    exact le_of_lt hx
  calc
    μ {x | F x - ∫ y, F y ∂μ > t}
        ≤ μ {x | t ≤ F x - ∫ y, F y ∂μ} := measure_mono hsubset
    _ = ENNReal.ofReal (μ.real {x | t ≤ F x - ∫ y, F y ∂μ}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
          ENNReal.ofReal_le_ofReal hchern

/-- Lower-tail concentration for Lipschitz functions of a standard Gaussian vector. -/
theorem product_standardGaussian_lower_tail
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  convert product_standardGaussian_upper_tail ( fun x => -F x ) L t hL ht ( hLip.neg ) using 2 ; simp +decide [ sub_eq_neg_add ];
  rw [ MeasureTheory.integral_neg ] ; ext ; simp +decide [ add_comm ]

theorem abs_gt_iff_pos_or_neg {a t : ℝ} : |a| > t ↔ a > t ∨ -a > t := by
  rw [ abs_eq_max_neg, gt_iff_lt, gt_iff_lt, gt_iff_lt, lt_max_iff, lt_neg ]

/-- Two-sided Gaussian concentration on a finite-dimensional Euclidean space. -/
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
          rw [← ENNReal.ofReal_add hexp hexp]; congr 1; ring

/-- Gaussian concentration for the product standard Gaussian on the SYK coupling space. -/
theorem gaussian_lipschitz_concentration
    (N q : ℕ) (F : CouplingSpace N q → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasure N q
        {x | |F x - ∫ y, F y ∂standardGaussianMeasure N q| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  simpa using
    euclidean_lipschitz_gaussian_concentration
      (ι := ({s : Finset (Fin N) // s.card = q})) F L t hL ht hLip

end SYK
