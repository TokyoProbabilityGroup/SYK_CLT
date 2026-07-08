import GaussianConcentrationAux

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK

/-- Per-coordinate Gaussian integration by parts: the tensorized one-dimensional Stein
identity along coordinate `i`. -/
lemma gaussian_ibp_coord {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ ι → ℝ) (i : ι)
    (hg : ContDiff ℝ 1 g)
    (C c : ℝ) (hgb : ∀ w, |g w| ≤ C * Real.exp (c * ‖w‖))
    (hgradb : ∀ w, ‖gradient g w‖ ≤ C * Real.exp (c * ‖w‖)) :
    ∫ w, w i * g w ∂(standardGaussianMeasureOnEuclidean ι)
      = ∫ w, (gradient g w) i ∂(standardGaussianMeasureOnEuclidean ι) := by
  classical
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  obtain ⟨hI1, hI2⟩ := gaussian_ibp_integrable g i hg C c hgb hgradb
  have hmeas : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    WithLp.measurable_toLp 2 _
  have hC : 0 ≤ C := le_trans (abs_nonneg (g 0)) (by simpa using hgb 0)
  have hcd : ContDiff ℝ 1 (fun z : ι → ℝ => g (WithLp.toLp 2 z)) :=
    hg.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.contDiff
  have hnorm : ∀ y : ι → ℝ, ‖WithLp.toLp 2 y‖ ≤ ∑ j, |y j| := by
    intro y
    rw [EuclideanSpace.norm_eq]
    have hsum_nonneg : (0:ℝ) ≤ ∑ j, |y j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 : ∑ j, ‖(WithLp.toLp 2 y) j‖ ^ 2 = ∑ j, |y j| ^ 2 :=
      Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs]
    have hle : ∑ j, ‖(WithLp.toLp 2 y) j‖ ^ 2 ≤ (∑ j, |y j|) ^ 2 := by
      rw [h1]; exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _
    calc Real.sqrt (∑ j, ‖(WithLp.toLp 2 y) j‖ ^ 2)
        ≤ Real.sqrt ((∑ j, |y j|) ^ 2) := Real.sqrt_le_sqrt hle
      _ = ∑ j, |y j| := Real.sqrt_sq hsum_nonneg
  have hexpmono : ∀ y : ι → ℝ, c * ‖WithLp.toLp 2 y‖ ≤ |c| * ∑ j, |y j| := fun y =>
    (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hnorm y) (abs_nonneg c))
  have hcoord : ∀ (x : EuclideanSpace ℝ ι) (j : ι), |x j| ≤ ‖x‖ := by
    intro x j
    rw [EuclideanSpace.norm_eq,
        show |x j| = Real.sqrt (|x j|^2) from (Real.sqrt_sq (abs_nonneg _)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [show |x j|^2 = ‖x j‖^2 by rw [Real.norm_eq_abs]]
    exact Finset.single_le_sum (f := fun k => ‖x k‖^2) (fun k _ => by positivity) (Finset.mem_univ j)
  have hhb' : ∀ y : ι → ℝ, |g (WithLp.toLp 2 y)| ≤ C * Real.exp (|c| * ∑ j, |y j|) := fun y =>
    (hgb _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexpmono y)) hC)
  have hdb' : ∀ (y : ι → ℝ) (j : ι),
      |fderiv ℝ (fun z => g (WithLp.toLp 2 z)) y (Pi.single j 1)|
        ≤ C * Real.exp (|c| * ∑ k, |y k|) := by
    intro y j
    rw [← gradient_toLp_coord_eq_fderiv g hgd y j]
    exact (hcoord _ j).trans ((hgradb _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexpmono y)) hC))
  have eq3 := pi_gaussian_stein_coord (fun z => g (WithLp.toLp 2 z)) i hcd C |c|
    (abs_nonneg c) hC hhb' hdb'
  have hμ : standardGaussianMeasureOnEuclidean ι
      = (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2) := rfl
  rw [hμ, integral_map hmeas.aemeasurable (by rw [← hμ]; exact hI1.aestronglyMeasurable),
      integral_map hmeas.aemeasurable (by rw [← hμ]; exact hI2.aestronglyMeasurable)]
  simp only [gradient_toLp_coord_eq_fderiv g hgd]
  exact eq3


/-
**`n`-dimensional Gaussian integration by parts.**  For a `C¹` function `g` on
`EuclideanSpace ℝ ι` whose value and gradient grow no faster than `C e^{c‖w‖}`, and any fixed
vector `v`, integration against the standard Gaussian satisfies
`∫ ⟪v, w⟫ g w = ∫ ⟪v, ∇g w⟫`.  This is the tensorization of the one-dimensional Stein
identity `gaussianReal_stein` over the coordinates (Fubini for the product measure).
-/
lemma gaussian_ibp {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ ι → ℝ)
    (v : EuclideanSpace ℝ ι) (hg : ContDiff ℝ 1 g)
    (C c : ℝ) (hgb : ∀ w, |g w| ≤ C * Real.exp (c * ‖w‖))
    (hgradb : ∀ w, ‖gradient g w‖ ≤ C * Real.exp (c * ‖w‖)) :
    ∫ w, (inner ℝ v w) * g w ∂(standardGaussianMeasureOnEuclidean ι)
      = ∫ w, (inner ℝ v (gradient g w)) ∂(standardGaussianMeasureOnEuclidean ι) := by
  have hcoord := fun i => gaussian_ibp_coord g i hg C c hgb hgradb
  have hint := fun i => gaussian_ibp_integrable g i hg C c hgb hgradb
  -- `⟪v, w⟫ = ∑ i, v i * w i` and `⟪v, ∇g w⟫ = ∑ i, v i * (∇g w) i`; use linearity of the
  -- integral and the per-coordinate identity.
  simp +decide only [inner];
  simp +decide only [Finset.sum_mul];
  rw [ MeasureTheory.integral_finset_sum, MeasureTheory.integral_finset_sum ];
  · simp_all +decide [ mul_assoc, MeasureTheory.integral_const_mul ];
    exact Finset.sum_congr rfl fun i _ => by rw [ show ( fun w => w.ofLp i * ( v.ofLp i * g w ) ) = fun w => v.ofLp i * ( w.ofLp i * g w ) by ext; ring, show ( fun w => ( gradient g w ).ofLp i * v.ofLp i ) = fun w => v.ofLp i * ( gradient g w ).ofLp i by ext; ring, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hcoord i ] ;
  · simp_all +decide [ inner, Finset.mul_sum _ _ _ ];
    exact fun i => ( ‹∀ i, Integrable ( fun w => w.ofLp i * g w ) ( standardGaussianMeasureOnEuclidean ι ) ∧ Integrable ( fun w => ( gradient g w ).ofLp i ) ( standardGaussianMeasureOnEuclidean ι ) › i ).2.mul_const _;
  · simp +decide [ inner, mul_assoc ];
    exact fun i => by simpa only [ mul_left_comm, mul_assoc ] using ( ‹∀ i, Integrable ( fun w => w.ofLp i * g w ) ( standardGaussianMeasureOnEuclidean ι ) ∧ Integrable ( fun w => ( gradient g w ).ofLp i ) ( standardGaussianMeasureOnEuclidean ι ) › i |>.1 ).const_mul ( v.ofLp i ) ;

/-- A `C¹` function with gradient bounded by `L` grows at most linearly. -/
lemma contDiff_abs_le_of_gradient_le {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (x : EuclideanSpace ℝ ι) :
    |F x| ≤ |F 0| + L * ‖x‖ := by
  have hfd : ∀ y, ‖fderiv ℝ F y‖ ≤ L := by
    intro y
    have hh : ‖gradient F y‖ = ‖fderiv ℝ F y‖ := by
      rw [gradient]; exact LinearIsometryEquiv.norm_map _ _
    rw [← hh]; exact hgrad y
  have hlip : LipschitzWith L.toNNReal F := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by norm_num))
    intro y
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal L hL]
    exact hfd y
  have hb := hlip.dist_le_mul x 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero, Real.coe_toNNReal L hL, Real.norm_eq_abs] at hb
  have h2 := abs_le.mp hb
  cases abs_cases (F x) <;> cases abs_cases (F 0) <;> nlinarith [norm_nonneg x]

/-- The gradient of `x ↦ exp (s * F x)`. -/
lemma gradient_exp_smul {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : ContDiff ℝ 1 F) (s : ℝ) (x : EuclideanSpace ℝ ι) :
    gradient (fun y => Real.exp (s * F y)) x = (s * Real.exp (s * F x)) • gradient F x := by
  have hd : HasFDerivAt F (fderiv ℝ F x) x :=
    (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hexp : HasFDerivAt (fun y => Real.exp (s * F y))
      ((s * Real.exp (s * F x)) • fderiv ℝ F x) x := by
    have h1 : HasFDerivAt (fun y => s * F y) (s • fderiv ℝ F x) x := hd.const_mul s
    have h2 := h1.exp
    convert h2 using 1
    ext v; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  rw [gradient, gradient, hexp.fderiv, map_smul]

/-- Projecting the rotation-invariant product Gaussian onto its first coordinate returns the
standard Gaussian: `(μ.prod μ).map ((rotation θ ·).1) = μ`.  In particular the affine
combination `cos θ • a + sin θ • b` has law `μ`. -/
lemma map_rotation_fst {ι : Type*} [Fintype ι] (θ : ℝ) :
    (((standardGaussianMeasureOnEuclidean ι).prod
        (standardGaussianMeasureOnEuclidean ι)).map
          (fun p => (ContinuousLinearMap.rotation θ p).1))
      = standardGaussianMeasureOnEuclidean ι := by
  have hmean : (standardGaussianMeasureOnEuclidean ι)[id] = 0 :=
    standardGaussianMeasureOnEuclidean_integral_id
  have hrot := IsGaussian.map_rotation_eq_self hmean θ
  have hfstcomp :
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (ContinuousLinearMap.rotation θ p).1)
        = Prod.fst ∘ (ContinuousLinearMap.rotation θ) := rfl
  rw [hfstcomp, ← Measure.map_map measurable_fst
      (ContinuousLinearMap.rotation θ).continuous.measurable, hrot]
  have h := Measure.fst_prod (μ := standardGaussianMeasureOnEuclidean ι)
    (ν := standardGaussianMeasureOnEuclidean ι)
  exact h

/-- The sharp Gaussian covariance bound for a `C¹` function with globally bounded gradient
(the smooth case, proved via rotation invariance of `μ.prod μ` and Gaussian integration by
parts).  The general Lipschitz case follows by mollification. -/
lemma gaussian_cov_bound_smooth {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  sorry

/-- **The sharp Gaussian covariance bound** for an `L`-Lipschitz `F`:
`|Cov(F, e^{sF})| ≤ L² |s| ∫ e^{sF}` against the standard Gaussian.  This is the last
remaining analytic input to `product_standardGaussian_mgf_le`.  It reduces to the smooth
case `gaussian_cov_bound_smooth` (proved via rotation invariance of `μ.prod μ` and the
Gaussian integration-by-parts lemma `gaussian_ibp`) by mollifying `F` into a sequence of
`C¹` functions with the same Lipschitz constant and passing to the limit by dominated
convergence.  The supporting infrastructure (`gaussian_ibp`, `map_rotation_fst`,
`gradient_exp_smul`, `contDiff_abs_le_of_gradient_le`, the mean-zero and integrability
lemmas) is fully proved; the smooth-case assembly and the mollification limit remain. -/
lemma gaussian_cov_bound {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  sorry

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