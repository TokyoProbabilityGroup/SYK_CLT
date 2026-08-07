import SYK.super_concentration.Gaussian_concentration.GaussianConcentrationAux

/-!
# Smooth-case Gaussian covariance bound: supporting lemmas

This file develops the covariance interpolation identity used to prove the sharp
Gaussian covariance bound `SYK.gaussian_cov_bound_smooth`.

Let `μ = standardGaussianMeasureOnEuclidean ι` and, for a `C¹` function `F` with
`‖∇F‖ ≤ L`, write `G x = exp (s * F x)`.  The covariance
`Cov = ∫ F·G - (∫ F)(∫ G)` is represented as
`Cov = ∫₀^{π/2} sin θ · (∫∫ ⟪∇G x, ∇F (cos θ • x - sin θ • y)⟫ dμ dμ) dθ`
via rotation invariance of `μ.prod μ` and the Gaussian integration-by-parts lemma
`gaussian_ibp`.  The bound then follows from Cauchy–Schwarz and `∫₀^{π/2} sin = 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace
open intervalIntegral

namespace SYK

variable {ι : Type*} [Fintype ι]

/-! ## Infrastructure moved from gaussian_concentration.lean -/

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
    simpa only [smul_smul, mul_comm] using h1.exp
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


/-
The rotation `(a,b) ↦ (cos θ • a + sin θ • b, -(sin θ • a) + cos θ • b)` preserves the
product standard Gaussian measure.
-/
lemma rotation_measurePreserving (θ : ℝ) :
    MeasurePreserving (ContinuousLinearMap.rotation θ)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι))
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
  refine' ⟨ _, _ ⟩;
  · fun_prop;
  · convert IsGaussian.map_rotation_eq_self _ _;
    · infer_instance;
    · infer_instance;
    · infer_instance;
    · infer_instance;
    · convert standardGaussianMeasureOnEuclidean_integral_id using 1

/-
Gradient of `F` composed with the affine map `z ↦ c • x - d • z`.
-/
lemma gradient_affine_comp (F : EuclideanSpace ℝ ι → ℝ) (hF : Differentiable ℝ F)
    (c d : ℝ) (x y : EuclideanSpace ℝ ι) :
    gradient (fun z => F (c • x - d • z)) y = (-d) • gradient F (c • x - d • y) := by
  have haff : HasFDerivAt (fun z : EuclideanSpace ℝ ι => c • x - d • z)
      (0 - d • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) y :=
    (hasFDerivAt_const (c • x) y).sub ((hasFDerivAt_id y).const_smul d)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp y haff
  have hmap :
      fderiv ℝ F (c • x - d • y) ∘L
          (0 - d • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) =
        (-d) • fderiv ℝ F (c • x - d • y) := by
    ext v
    simp
  have hcomp' : HasFDerivAt (fun z => F (c • x - d • z))
      ((-d) • fderiv ℝ F (c • x - d • y)) y := by
    simpa only [Function.comp_def, hmap] using hcomp
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt, map_smul, toDual_gradient]
  exact hcomp'

/-
The covariance rewritten as a double integral over the product measure.
-/
lemma gaussian_cov_eq_double (f g : EuclideanSpace ℝ ι → ℝ)
    (hf : Integrable f (standardGaussianMeasureOnEuclidean ι))
    (hg : Integrable g (standardGaussianMeasureOnEuclidean ι))
    (hfg : Integrable (fun x => f x * g x) (standardGaussianMeasureOnEuclidean ι)) :
    (∫ x, f x * g x ∂(standardGaussianMeasureOnEuclidean ι))
        - (∫ x, f x ∂(standardGaussianMeasureOnEuclidean ι))
          * (∫ x, g x ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ a, ∫ b, f a * (g a - g b)
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  norm_num [ mul_sub ];
  convert ( MeasureTheory.integral_sub ( hfg ) _ ) using 1;
  rw [ MeasureTheory.integral_sub hfg ];
  any_goals exact fun x => f x * ∫ y, g y ∂standardGaussianMeasureOnEuclidean ι;
  · rw [ MeasureTheory.integral_mul_const ];
  · exact hf.mul_const _;
  · convert MeasureTheory.integral_sub _ _ using 3;
    · rw [ MeasureTheory.integral_sub, MeasureTheory.integral_const_mul ] <;> norm_num;
      · rw [ MeasureTheory.integral_const_mul ];
      · exact MeasureTheory.integrable_const _;
      · exact hg.const_mul _;
    · exact hfg;
    · exact hf.mul_const _;
  · exact hf.mul_const _

/-
Fundamental theorem of calculus along the rotation path `θ ↦ cos θ • a + sin θ • b`.
-/
lemma gaussian_path_ftc (g : EuclideanSpace ℝ ι → ℝ) (hg : ContDiff ℝ 1 g)
    (a b : EuclideanSpace ℝ ι) :
    g a - g b = - ∫ θ in (0:ℝ)..(Real.pi/2),
      inner ℝ (gradient g (Real.cos θ • a + Real.sin θ • b))
        (-Real.sin θ • a + Real.cos θ • b) := by
  -- By the fundamental theorem of calculus, the integral of the derivative of $h$ over $[0, \pi/2]$ is $h(\pi/2) - h(0)$.
  have h_ftc : ∫ θ in (0 : ℝ)..Real.pi / 2, deriv (fun θ => g (Real.cos θ • a + Real.sin θ • b)) θ = g b - g a := by
    rw [ intervalIntegral.integral_deriv_eq_sub ];
    · simp +decide;
    · exact fun x hx => DifferentiableAt.comp x ( hg.contDiffAt.differentiableAt ( by norm_num ) ) ( DifferentiableAt.add ( DifferentiableAt.smul ( Real.differentiableAt_cos ) ( differentiableAt_const _ ) ) ( DifferentiableAt.smul ( Real.differentiableAt_sin ) ( differentiableAt_const _ ) ) );
    · apply Continuous.intervalIntegrable
      have hcurve : ContDiff ℝ 1
          (fun θ : ℝ => g (Real.cos θ • a + Real.sin θ • b)) := by
        apply hg.comp
        exact (Real.contDiff_cos.smul contDiff_const).add
          (Real.contDiff_sin.smul contDiff_const)
      exact hcurve.continuous_deriv (by norm_num)
  -- By definition of the gradient, we know that the derivative of $g$ along the path is given by the inner product of the gradient and the direction vector.
  have h_grad : ∀ θ, deriv (fun θ => g (Real.cos θ • a + Real.sin θ • b)) θ = ⟪gradient g (Real.cos θ • a + Real.sin θ • b), (-Real.sin θ) • a + (Real.cos θ) • b⟫_ℝ := by
    intro θ
    have hpath : HasDerivAt (fun t : ℝ => Real.cos t • a + Real.sin t • b)
        ((-Real.sin θ) • a + Real.cos θ • b) θ :=
      (Real.hasDerivAt_cos θ).smul_const a |>.add
        ((Real.hasDerivAt_sin θ).smul_const b)
    have hcomp := hg.differentiable (by norm_num) |>.differentiableAt.hasFDerivAt.comp θ
      hpath.hasFDerivAt
    have hcomp' : HasFDerivAt
        (fun t => g (Real.cos t • a + Real.sin t • b))
        (fderiv ℝ g (Real.cos θ • a + Real.sin θ • b) ∘L
          ContinuousLinearMap.toSpanSingleton ℝ
            ((-Real.sin θ) • a + Real.cos θ • b)) θ := by
      simpa only [Function.comp_def] using hcomp
    have hderiv := hcomp'.hasDerivAt.deriv
    rw [← toDual_gradient] at hderiv
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      InnerProductSpace.toDual_apply_apply] using hderiv
  aesop

/-
Integrability of the change-of-variables covariance integrand
`ψ (x,y) = F(cos θ•x - sin θ•y) · ⟪∇G x, y⟫` on the product Gaussian measure.
-/
lemma integrable_cov_psi (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        F (Real.cos θ • p.1 - Real.sin θ • p.2) *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) p.1) p.2)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun p => ( |F 0| + L * ‖p.1‖ + L * ‖p.2‖ ) * ( |s| * L * Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖p.1‖ ) * ‖p.2‖ );
  · -- The product of integrable functions is integrable.
    have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (|F 0| + L * ‖p.1‖ + L) * (Real.exp (|s| * L * ‖p.1‖)) * (‖p.2‖ + ‖p.2‖^2)) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
      have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι => (|F 0| + L * ‖p‖ + L) * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) ∧ Integrable (fun p : EuclideanSpace ℝ ι => ‖p‖ + ‖p‖^2) (standardGaussianMeasureOnEuclidean ι) := by
        constructor;
        · have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι => ‖p‖ * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
            have h_integrable : ∀ c : ℝ, Integrable (fun p : EuclideanSpace ℝ ι => Real.exp (c * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
              intro c
              apply SYK.integrable_exp_mul_norm;
            have := h_integrable ( |s| * L + 1 );
            refine' this.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( measurable_norm.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_const.mul measurable_norm |> Measurable.aestronglyMeasurable ) );
            · filter_upwards [ ] with p using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ add_mul, one_mul, Real.exp_add ] ; nlinarith [ Real.exp_pos ( |s| * L * ‖p‖ ), Real.exp_pos ‖p‖, Real.add_one_le_exp ‖p‖, mul_nonneg ( abs_nonneg s ) hL ] ;
          have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι => Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
            convert integrable_exp_mul_norm ( |s| * L ) using 1;
          simp_all +decide [ add_mul, mul_assoc ];
          exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add ( h_integrable.const_mul _ ) ( MeasureTheory.Integrable.const_mul ‹_› _ ) ) ( h_integrable.const_mul _ );
        · refine' MeasureTheory.Integrable.add _ _;
          · have := @integrable_exp_mul_norm ι;
            refine' MeasureTheory.Integrable.mono' ( this 1 ) _ _;
            · exact Continuous.aestronglyMeasurable ( continuous_norm );
            · filter_upwards [ ] with x using by simpa using le_trans ( by norm_num ) ( Real.add_one_le_exp _ ) ;
          · convert integrable_exp_mul_norm 2 |> fun h => h.mono' _ _ using 1;
            · exact Continuous.aestronglyMeasurable ( by continuity );
            · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( sq_nonneg _ ) ] ; rw [ two_mul, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp ( ‖x‖ ), Real.add_one_le_exp ( ‖x‖ ), norm_nonneg x ] ;
      exact MeasureTheory.Integrable.mul_prod h_integrable.1 h_integrable.2;
    refine' h_integrable.const_mul ( |s| * L * Real.exp ( |s| * |F 0| ) ) |> fun h => h.mono' _ _;
    · fun_prop;
    · filter_upwards [ ] with p;
      rw [ Real.norm_of_nonneg ( by positivity ) ];
      nlinarith [ show 0 ≤ |s| * L * Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖p.1‖ ) * ‖p.2‖ by positivity, show 0 ≤ |s| * L * Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖p.1‖ ) * ‖p.2‖ ^ 2 by positivity, show 0 ≤ |F 0| * ‖p.2‖ by positivity, show 0 ≤ L * ‖p.1‖ * ‖p.2‖ by positivity, show 0 ≤ L * ‖p.2‖ ^ 2 by positivity ];
  · refine' Measurable.aestronglyMeasurable _;
    refine' Measurable.mul _ _;
    · exact hF.continuous.measurable.comp (by fun_prop)
    · -- The gradient of a continuously differentiable function is continuous, hence measurable.
      have h_grad_cont : Continuous (fun x => gradient (fun z => Real.exp (s * F z)) x) := by
        refine' Continuous.comp ( LinearIsometryEquiv.continuous _ ) _;
        fun_prop;
      fun_prop;
  · refine' Filter.Eventually.of_forall _;
    intro p
    have h_abs : |F (Real.cos θ • p.1 - Real.sin θ • p.2)| ≤ |F 0| + L * ‖p.1‖ + L * ‖p.2‖ := by
      have h_triangle : ‖Real.cos θ • p.1 - Real.sin θ • p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
        exact le_trans ( norm_sub_le _ _ ) ( add_le_add ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_cos_le_one _ ) ) ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_sin_le_one _ ) ) );
      have := contDiff_abs_le_of_gradient_le F L hL hF hgrad ( Real.cos θ • p.1 - Real.sin θ • p.2 ) ; simp_all +decide [ mul_add, add_assoc ] ; nlinarith;
    have h_grad : ‖gradient (fun z => Real.exp (s * F z)) p.1‖ ≤ |s| * L * Real.exp (|s| * |F 0|) * Real.exp (|s| * L * ‖p.1‖) := by
      have h_grad : ‖gradient (fun z => Real.exp (s * F z)) p.1‖ = |s| * Real.exp (s * F p.1) * ‖gradient F p.1‖ := by
        rw [ gradient_exp_smul F hF s p.1 ] ; norm_num [ norm_smul, abs_mul ];
      have h_exp : Real.exp (s * F p.1) ≤ Real.exp (|s| * |F 0|) * Real.exp (|s| * L * ‖p.1‖) := by
        rw [ ← Real.exp_add ];
        have h_exp : |F p.1| ≤ |F 0| + L * ‖p.1‖ := by
          apply contDiff_abs_le_of_gradient_le F L hL hF hgrad p.1;
        exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> cases abs_cases ( F p.1 ) <;> nlinarith [ abs_le.mp h_exp ] );
      nlinarith [ show 0 ≤ |s| * Real.exp ( s * F p.1 ) by positivity, show 0 ≤ |s| * L by positivity, hgrad p.1 ]
    generalize_proofs at *;
    simp_all +decide [ abs_mul, inner_self_eq_norm_sq_to_K ];
    exact mul_le_mul h_abs ( by simpa [ abs_mul ] using abs_real_inner_le_norm ( gradient ( fun z => Real.exp ( s * F z ) ) p.1 ) p.2 |> le_trans <| mul_le_mul_of_nonneg_right h_grad <| norm_nonneg _ ) ( by positivity ) ( by positivity )

/-
Integrability of the original covariance integrand
`Φ (a,b) = F a · ⟪∇G(cos θ•a+sin θ•b), -sin θ•a+cos θ•b⟫` on the product Gaussian measure.
-/
lemma integrable_cov_Phi (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        F p.1 *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • p.1 + Real.sin θ • p.2))
            (-Real.sin θ • p.1 + Real.cos θ • p.2))
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
  have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      F (Real.cos θ • p.1 - Real.sin θ • p.2) *
        inner ℝ (gradient (fun z => Real.exp (s * F z)) p.1) p.2)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
        apply_rules [ integrable_cov_psi ];
  have h_rotation : MeasurePreserving (ContinuousLinearMap.rotation θ)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι))
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) :=
    rotation_measurePreserving θ
  have h_integrable_map : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪gradient (fun z => Real.exp (s * F z)) p.1, p.2⟫_ℝ) ((Measure.prod (standardGaussianMeasureOnEuclidean ι) (standardGaussianMeasureOnEuclidean ι)).map (ContinuousLinearMap.rotation θ)) := by
    rw [h_rotation.map_eq]
    exact h_integrable
  convert h_integrable_map.comp_measurable
      (ContinuousLinearMap.rotation θ).continuous.measurable using 1;
  · ext ⟨x, y⟩
    simp only [Function.comp_apply, ContinuousLinearMap.rotation_apply]
    congr 1
    apply congr_arg F
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      x.ofLp i = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * x.ofLp i := by
        rw [Real.sin_sq_add_cos_sq]
        ring
      _ = Real.cos θ * (Real.cos θ * x.ofLp i + Real.sin θ * y.ofLp i) -
          Real.sin θ * (-Real.sin θ * x.ofLp i + Real.cos θ * y.ofLp i) := by ring

/-
Change of variables by the rotation on the product Gaussian measure: rewriting the
covariance integrand `F a · ⟪∇G(cos θ•a+sin θ•b), -sin θ•a+cos θ•b⟫` as
`F(cos θ•x - sin θ•y) · ⟪∇G x, y⟫`.  Here `G z = exp (s * F z)`.
-/
lemma gaussian_cov_change_of_var (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    (∫ a, ∫ b, F a *
        inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
          (-Real.sin θ • a + Real.cos θ • b)
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ x, ∫ y, F (Real.cos θ • x - Real.sin θ • y) *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x) y
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  have h_psi_integrable : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
    convert integrable_cov_psi F L hL hF hgrad s θ using 1;
  have h_psi_integrable : ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) = ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F p.1 * ⟪(gradient (fun z => Real.exp (s * F z)) (Real.cos θ • p.1 + Real.sin θ • p.2)), -Real.sin θ • p.1 + Real.cos θ • p.2⟫_ℝ ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) := by
    have h_psi_integrable : ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) = ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ ∂(Measure.map (ContinuousLinearMap.rotation θ) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι))) := by
      rw [ rotation_measurePreserving θ |>.map_eq ];
    rw [ h_psi_integrable, MeasureTheory.integral_map ];
    · simp +decide [ ContinuousLinearMap.rotation ];
      congr with p ; ring;
      rw [ show Real.cos θ • Real.cos θ • p.1 + Real.cos θ • Real.sin θ • p.2 - ( - ( Real.sin θ • Real.sin θ • p.1 ) + Real.sin θ • Real.cos θ • p.2 ) = p.1 by ext i; simpa using by ring_nf; rw [ Real.sin_sq, Real.cos_sq ] ; ring ] ; ring;
    · exact Continuous.aemeasurable ( by continuity );
    · refine' MeasureTheory.Integrable.aestronglyMeasurable _;
      rw [ rotation_measurePreserving θ |>.map_eq ] ; assumption;
  convert h_psi_integrable.symm using 1;
  · erw [ MeasureTheory.integral_prod ];
    convert integrable_cov_Phi F L hL hF hgrad s θ using 1;
  · rw [ MeasureTheory.integral_prod ];
    assumption

/-
Gaussian integration by parts in the `y`-variable, applied to the change-of-variables
form.  Here `G z = exp (s * F z)`.
-/
lemma gaussian_cov_ibp_step (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    (∫ x, ∫ y, F (Real.cos θ • x - Real.sin θ • y) *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x) y
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = - Real.sin θ * ∫ x, ∫ y,
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
            (gradient F (Real.cos θ • x - Real.sin θ • y))
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  have hpointwise : ∀ x, ∫ y, F (Real.cos θ • x - Real.sin θ • y) * ⟪gradient (fun z => Real.exp (s * F z)) x, y⟫_ℝ ∂standardGaussianMeasureOnEuclidean ι = -Real.sin θ * ∫ y, ⟪gradient (fun z => Real.exp (s * F z)) x, gradient F (Real.cos θ • x - Real.sin θ • y)⟫_ℝ ∂standardGaussianMeasureOnEuclidean ι := by
    intro x;
    convert gaussian_ibp ( fun y => F ( Real.cos θ • x - Real.sin θ • y ) ) ( gradient ( fun z => Real.exp ( s * F z ) ) x ) ( show ContDiff ℝ 1 ( fun y => F ( Real.cos θ • x - Real.sin θ • y ) ) from ?_ ) ( |F 0| + L * ‖x‖ + L ) 1 ?_ ?_ using 1;
    · ac_rfl;
    · rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; rw [ gradient_affine_comp ] ; ring;
      · simp +decide [ inner_smul_right ];
      · exact ContDiff.differentiable_one hF;
    · fun_prop;
    · intro w
      have h_bound : |F (Real.cos θ • x - Real.sin θ • w)| ≤ |F 0| + L * ‖Real.cos θ • x - Real.sin θ • w‖ := by
        apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
      have h_bound : ‖Real.cos θ • x - Real.sin θ • w‖ ≤ ‖x‖ + ‖w‖ := by
        exact le_trans ( norm_sub_le _ _ ) ( add_le_add ( by simpa [ norm_smul ] using mul_le_of_le_one_left ( norm_nonneg x ) ( Real.abs_cos_le_one θ ) ) ( by simpa [ norm_smul ] using mul_le_of_le_one_left ( norm_nonneg w ) ( Real.abs_sin_le_one θ ) ) );
      nlinarith [ abs_nonneg ( F 0 ), Real.add_one_le_exp ( 1 * ‖w‖ ), Real.one_le_exp ( show 0 ≤ 1 * ‖w‖ by positivity ), mul_nonneg hL ( norm_nonneg x ), mul_nonneg hL ( norm_nonneg w ) ];
    · -- By definition of $G$, we know that its gradient is $(-\sin \theta) \cdot \nabla F(\cos \theta \cdot x - \sin \theta \cdot y)$.
      have h_grad_G : ∀ w, gradient (fun y => F (Real.cos θ • x - Real.sin θ • y)) w = (-Real.sin θ) • gradient F (Real.cos θ • x - Real.sin θ • w) := by
        apply_rules [ gradient_affine_comp ];
        fun_prop;
      intro w
      rw [h_grad_G w]
      simp [norm_smul];
      refine' le_trans ( mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_sin_le_one _ ) ) _;
      refine' le_trans ( hgrad _ ) _;
      exact le_trans ( by nlinarith [ abs_nonneg ( F 0 ), norm_nonneg x ] ) ( le_mul_of_one_le_right ( by positivity ) ( Real.one_le_exp ( norm_nonneg w ) ) );
  rw [ ← MeasureTheory.integral_const_mul, funext hpointwise ]

/-- Per-angle covariance identity: change of variables (rotation) followed by Gaussian
integration by parts in the second variable.  Here `G z = exp (s * F z)`. -/
lemma gaussian_cov_per_theta (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    (∫ a, ∫ b, F a *
        inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
          (-Real.sin θ • a + Real.cos θ • b)
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = - Real.sin θ * ∫ x, ∫ y,
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
            (gradient F (Real.cos θ • x - Real.sin θ • y))
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  rw [gaussian_cov_change_of_var F L hL hF hgrad s θ,
      gaussian_cov_ibp_step F L hL hF hgrad s θ]

/-
Joint integrability of the covariance integrand over `((a,b), θ)` where `θ` ranges over
the finite interval `Ioc 0 (π/2)`.  Used for the Fubini swap.
-/
set_option maxHeartbeats 1000000 in
lemma integrable_cov_joint (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    Integrable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × ℝ =>
        F q.1.1 *
          inner ℝ (gradient (fun z => Real.exp (s * F z))
              (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2))
            (-Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2))
      (((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)).prod
        (volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2)))) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun q => ( |s| * L * Real.exp ( |s| * |F 0| ) ) * ( ( |F 0| + L * ‖q.1.1‖ ) * Real.exp ( |s| * L * ‖q.1.1‖ ) * ( 1 + ‖q.1.1‖ ) ) * ( ( 1 + ‖q.1.2‖ ) * Real.exp ( |s| * L * ‖q.1.2‖ ) );
  · have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) => ((|F 0| + L * ‖p.1‖) * Real.exp (|s| * L * ‖p.1‖) * (1 + ‖p.1‖)) * ((1 + ‖p.2‖) * Real.exp (|s| * L * ‖p.2‖))) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
      have h_integrable : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (1 + ‖p‖) ^ a * Real.exp (b * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
        intro a b ha hb
        have h_integrable : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ ι => Real.exp ((a + b) * ‖p‖) * 2 ^ a) (standardGaussianMeasureOnEuclidean ι) := by
          exact MeasureTheory.Integrable.mul_const ( integrable_exp_mul_norm _ ) _;
        refine' h_integrable.mono' _ _;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Measurable.pow_const ( by exact measurable_const.add ( measurable_norm ) ) _ ) ( by exact Real.continuous_exp.measurable.comp ( by exact measurable_const.mul ( measurable_norm ) ) ) );
        · filter_upwards [ ] with p
          have h_bound : (1 + ‖p‖) ^ a ≤ 2 ^ a * Real.exp (a * ‖p‖) := by
            have h_bound : (1 + ‖p‖) ≤ 2 * Real.exp (‖p‖) := by
              linarith [ Real.add_one_le_exp ‖p‖, norm_nonneg p ];
            exact le_trans ( Real.rpow_le_rpow ( by positivity ) h_bound ( by positivity ) ) ( by rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.exp_mul ] ; ring_nf; norm_num );
          rw [ Real.norm_of_nonneg ( by positivity ) ];
          calc
            (1 + ‖p‖) ^ a * Real.exp (b * ‖p‖)
                ≤ (2 ^ a * Real.exp (a * ‖p‖)) * Real.exp (b * ‖p‖) :=
              mul_le_mul_of_nonneg_right h_bound (Real.exp_nonneg _)
            _ = Real.exp ((a + b) * ‖p‖) * 2 ^ a := by
              rw [add_mul, Real.exp_add]
              ring
      have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (|F 0| + L * ‖p‖) * Real.exp (|s| * L * ‖p‖) * (1 + ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
        have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (1 + ‖p‖) ^ 2 * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
          exact_mod_cast h_integrable 2 ( |s| * L ) ( by norm_num ) ( by positivity );
        refine' h_integrable.const_mul ( |F 0| + L ) |> fun h => h.mono' _ _;
        · fun_prop;
        · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact le_of_sub_nonneg ( by ring_nf; positivity ) ;
      have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (1 + ‖p‖) * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
        convert ‹∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Integrable ( fun p : EuclideanSpace ℝ ι => ( 1 + ‖p‖ ) ^ a * Real.exp ( b * ‖p‖ ) ) ( standardGaussianMeasureOnEuclidean ι ) › 1 ( |s| * L ) zero_le_one ( mul_nonneg ( abs_nonneg s ) hL ) using 1 ; norm_num;
      convert MeasureTheory.Integrable.mul_prod ‹Integrable ( fun p : EuclideanSpace ℝ ι => ( |F 0| + L * ‖p‖ ) * Real.exp ( |s| * L * ‖p‖ ) * ( 1 + ‖p‖ ) ) ( standardGaussianMeasureOnEuclidean ι ) › ‹Integrable ( fun p : EuclideanSpace ℝ ι => ( 1 + ‖p‖ ) * Real.exp ( |s| * L * ‖p‖ ) ) ( standardGaussianMeasureOnEuclidean ι ) › using 1;
    convert h_integrable.const_mul ( |s| * L * Real.exp ( |s| * |F 0| ) ) |> MeasureTheory.Integrable.comp_fst <| MeasureTheory.Measure.restrict ( MeasureTheory.MeasureSpace.volume ) ( Set.Ioc 0 ( Real.pi / 2 ) ) using 1 ; ext ; ring!;
  · have h_measurable : Continuous (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × ℝ => F q.1.1 * ⟪gradient (fun z => Real.exp (s * F z)) (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2), -Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2⟫_ℝ) := by
      refine' Continuous.mul ( hF.continuous.comp continuous_fst.fst ) _;
      have h_cont : Continuous (fun q : EuclideanSpace ℝ ι => gradient (fun z => Real.exp (s * F z)) q) := by
        refine' Continuous.comp ( LinearIsometryEquiv.continuous _ ) _;
        fun_prop;
      fun_prop;
    exact h_measurable.aestronglyMeasurable
  · refine' Filter.Eventually.of_forall _;
    intro q
    have h_bound : ‖gradient (fun z => Real.exp (s * F z)) (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)‖ ≤ |s| * L * Real.exp (|s| * |F 0|) * Real.exp (|s| * L * ‖q.1.1‖) * Real.exp (|s| * L * ‖q.1.2‖) := by
      have h_bound : ‖gradient (fun z => Real.exp (s * F z)) (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)‖ ≤ |s| * L * Real.exp (|s| * |F 0| + |s| * L * ‖Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2‖) := by
        rw [ gradient_exp_smul ];
        · rw [ norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ];
          rw [ mul_right_comm ];
          gcongr;
          · exact hgrad _;
          · have h_bound : |F (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)| ≤ |F 0| + L * ‖Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2‖ := by
              apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
            cases abs_cases s <;> cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp h_bound ];
        · exact hF;
      have h_bound : ‖Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2‖ ≤ ‖q.1.1‖ + ‖q.1.2‖ := by
        exact le_trans ( norm_add_le _ _ ) ( add_le_add ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_cos_le_one _ ) ) ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_sin_le_one _ ) ) );
      simp_all +decide [ mul_assoc, ← Real.exp_add ];
      exact le_trans ‹_› ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ abs_nonneg s, mul_nonneg ( abs_nonneg s ) hL ] ) <| by positivity ) <| by positivity );
    have h_bound : |F q.1.1| ≤ |F 0| + L * ‖q.1.1‖ := by
      apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
    have h_bound : ‖-Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2‖ ≤ (1 + ‖q.1.1‖) * (1 + ‖q.1.2‖) := by
      refine' le_trans ( norm_add_le _ _ ) _;
      norm_num [ norm_smul ];
      nlinarith [ abs_nonneg ( Real.sin q.2 ), abs_nonneg ( Real.cos q.2 ), Real.abs_sin_le_one q.2, Real.abs_cos_le_one q.2, norm_nonneg q.1.1, norm_nonneg q.1.2 ];
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |F q.1.1| * |⟪gradient (fun z => Real.exp (s * F z))
          (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2),
          -Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2⟫_ℝ|
          ≤ |F q.1.1| *
              (‖gradient (fun z => Real.exp (s * F z))
                  (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)‖ *
                ‖-Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ ≤ (|F 0| + L * ‖q.1.1‖) *
            ((|s| * L * Real.exp (|s| * |F 0|) *
                Real.exp (|s| * L * ‖q.1.1‖) *
                Real.exp (|s| * L * ‖q.1.2‖)) *
              ((1 + ‖q.1.1‖) * (1 + ‖q.1.2‖))) := by
            gcongr
      _ = (|s| * L * Real.exp (|s| * |F 0|)) *
            ((|F 0| + L * ‖q.1.1‖) * Real.exp (|s| * L * ‖q.1.1‖) *
              (1 + ‖q.1.1‖)) *
            ((1 + ‖q.1.2‖) * Real.exp (|s| * L * ‖q.1.2‖)) := by ring

lemma gaussian_cov_fubini_swap (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    (∫ a, ∫ b, F a * (∫ θ in (0:ℝ)..(Real.pi/2),
        inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
          (-Real.sin θ • a + Real.cos θ • b))
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ θ in (0:ℝ)..(Real.pi/2), ∫ a, ∫ b, F a *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
            (-Real.sin θ • a + Real.cos θ • b)
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  -- Apply Fubini's theorem to interchange the order of integration.
  have h_fubini : ∀ {f : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × ℝ → ℝ}, MeasureTheory.Integrable f (((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)).prod (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) → ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, ∫ θ in Set.Ioc 0 (Real.pi / 2), f (p, θ) ∂volume ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) = ∫ θ in Set.Ioc 0 (Real.pi / 2), ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, f (p, θ) ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) ∂volume := by
    intro f hf;
    apply_rules [ MeasureTheory.integral_integral_swap ];
  convert h_fubini ( integrable_cov_joint F L hL hF hgrad s ) using 1;
  · rw [ MeasureTheory.integral_prod ];
    · simp +decide only [intervalIntegral.integral_of_le Real.pi_div_two_pos.le, MeasureTheory.integral_const_mul];
    · convert ( integrable_cov_joint F L hL hF hgrad s ).integral_prod_left using 1;
  · rw [ intervalIntegral.integral_of_le Real.pi_div_two_pos.le ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun θ hθ => _;
    erw [ MeasureTheory.integral_prod ];
    convert integrable_cov_Phi F L hL hF hgrad s θ using 1

/-
The covariance interpolation representation: `Cov = ∫₀^{π/2} sin θ · H θ dθ` where
`H θ = ∫∫ ⟪∇G x, ∇F (cos θ • x - sin θ • y)⟫`.
-/
lemma gaussian_cov_repr (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    (∫ x, F x * Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι))
        - (∫ x, F x ∂(standardGaussianMeasureOnEuclidean ι))
          * (∫ x, Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ θ in (0:ℝ)..(Real.pi/2), Real.sin θ *
          ∫ x, ∫ y, inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
            (gradient F (Real.cos θ • x - Real.sin θ • y))
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  rw [ gaussian_cov_eq_double ];
  · convert congr_arg Neg.neg ( gaussian_cov_fubini_swap F L hL hF hgrad s ) using 1;
    · rw [ ← MeasureTheory.integral_neg ];
      congr! 2;
      rw [ ← MeasureTheory.integral_neg ] ; congr ; ext ;
      rename_i a b;
      rw [ gaussian_path_ftc ( fun z => Real.exp ( s * F z ) ) ( by fun_prop ) a b ] ; ring;
    · rw [ ← intervalIntegral.integral_neg ] ; congr ; ext θ ; rw [ gaussian_cov_per_theta F L hL hF hgrad s θ ] ; ring;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => |F 0| + L * Real.exp ( ‖x‖ );
    · refine' MeasureTheory.Integrable.add _ _;
      · simp +decide [ MeasureTheory.integrable_const_iff ];
      · refine' MeasureTheory.Integrable.const_mul _ _;
        convert integrable_exp_mul_norm 1 using 1;
        norm_num;
    · exact hF.continuous.aestronglyMeasurable;
    · filter_upwards [ ] with x using le_trans ( contDiff_abs_le_of_gradient_le F L hL hF hgrad x ) ( by nlinarith [ Real.add_one_le_exp ‖x‖, norm_nonneg x ] );
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => Real.exp ( |s| * ( |F 0| + L * ‖x‖ ) );
    · convert integrable_exp_mul_norm ( |s| * L ) |> fun h => h.const_mul ( Real.exp ( |s| * |F 0| ) ) using 1 ; ext ; ring;
      rw [ ← Real.exp_add ];
    · exact Continuous.aestronglyMeasurable ( by exact Real.continuous_exp.comp ( continuous_const.mul hF.continuous ) );
    · have h_bound : ∀ x, |F x| ≤ |F 0| + L * ‖x‖ := by
        apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
      filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( h_bound x ) ] ) ;
  · have h_integrable : ∃ C c, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |F x * Real.exp (s * F x)| ≤ C * Real.exp (c * ‖x‖) := by
      have h_integrable : ∃ C c, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |F x| ≤ C * Real.exp (c * ‖x‖) := by
        use |F 0| + L, 1;
        have := contDiff_abs_le_of_gradient_le F L hL hF hgrad;
        exact ⟨ by positivity, by positivity, fun x => le_trans ( this x ) ( by nlinarith [ abs_nonneg ( F 0 ), Real.add_one_le_exp ( 1 * ‖x‖ ), norm_nonneg x ] ) ⟩;
      have h_integrable : ∃ C c, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |Real.exp (s * F x)| ≤ C * Real.exp (c * ‖x‖) := by
        use Real.exp (|s| * |F 0|), |s| * L;
        simp +decide [ ← Real.exp_add ];
        exact ⟨ Real.exp_nonneg _, mul_nonneg ( abs_nonneg _ ) hL, fun x => by cases abs_cases s <;> cases abs_cases ( F 0 ) <;> cases abs_cases ( F x ) <;> nlinarith [ contDiff_abs_le_of_gradient_le F L hL hF hgrad x ] ⟩;
      obtain ⟨ C₁, c₁, hC₁, hc₁, h₁ ⟩ := ‹∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |F x| ≤ C * Real.exp ( c * ‖x‖ ) ›
      obtain ⟨ C₂, c₂, hC₂, hc₂, h₂ ⟩ := h_integrable
      use C₁ * C₂, c₁ + c₂;
      simp_all +decide [ abs_mul, add_mul, Real.exp_add ];
      exact ⟨ mul_nonneg hC₁ hC₂, add_nonneg hc₁ hc₂, fun x => by nlinarith [ h₁ x, h₂ x, abs_nonneg ( F x ), Real.exp_pos ( s * F x ), mul_le_mul_of_nonneg_left ( h₂ x ) ( abs_nonneg ( F x ) ) ] ⟩;
    obtain ⟨ C, c, hC, hc, h ⟩ := h_integrable;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => C * Real.exp ( c * ‖x‖ );
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm c ) _;
    · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( hF.continuous ) ( Real.continuous_exp.comp ( continuous_const.mul hF.continuous ) ) );
    · exact Filter.Eventually.of_forall h

/-
Pointwise bound on the inner double integral `H θ`.
-/
lemma gaussian_cov_H_bound (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    |∫ x, ∫ y, inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
          (gradient F (Real.cos θ • x - Real.sin θ • y))
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι)|
      ≤ |s| * L ^ 2 * ∫ x, Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι) := by
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : EuclideanSpace ℝ ι → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun x => |s| * L ^ 2 * Real.exp ( s * F x );
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · refine' MeasureTheory.Integrable.const_mul _ _;
    have h_integrable : ∀ x, |F x| ≤ |F 0| + L * ‖x‖ := by
      intro x;
      have h_abs_le : ∀ x, |F x| ≤ |F 0| + L * ‖x‖ := by
        intro x
        have h_abs_le_aux : ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv (fun t => F (t • x)) t| ≤ L * ‖x‖ := by
          intro t ht
          have h_deriv : deriv (fun t => F (t • x)) t = (fderiv ℝ F (t • x)) x := by
            rw [ deriv ];
            erw [ fderiv_comp ] <;> norm_num [ hF.contDiffAt.differentiableAt ];
            exact congr_arg _ ( HasDerivAt.deriv ( by simpa using HasDerivAt.smul_const ( hasDerivAt_id t ) x ) );
          have := hgrad ( t • x ) ; simp_all +decide [ gradient ] ;
          exact le_trans ( by simpa using ( fderiv ℝ F ( t • x ) |> ContinuousLinearMap.le_opNorm ) x ) ( mul_le_mul_of_nonneg_right ( hgrad _ ) ( norm_nonneg _ ) )
        have := exists_deriv_eq_slope ( f := fun t => F ( t • x ) ) zero_lt_one;
        simp +zetaDelta at *;
        exact this ( Continuous.continuousOn <| by exact hF.continuous.comp ( continuous_id.smul continuous_const ) ) ( fun t ht => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.comp t ( hF.contDiffAt.differentiableAt ( by norm_num ) ) <| differentiableAt_id.smul_const _ ) |> fun ⟨ c, hc₁, hc₂ ⟩ => abs_le.mpr ⟨ by cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp ( h_abs_le_aux c hc₁.1.le hc₁.2.le ) ], by cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp ( h_abs_le_aux c hc₁.1.le hc₁.2.le ) ] ⟩;
      exact h_abs_le x;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => Real.exp ( |s| * ( |F 0| + L * ‖x‖ ) );
    · convert integrable_exp_mul_norm ( |s| * L ) |> fun h => h.const_mul ( Real.exp ( |s| * |F 0| ) ) using 2 ; ring;
      rw [ ← Real.exp_add ];
    · exact Continuous.aestronglyMeasurable ( by exact Real.continuous_exp.comp ( continuous_const.mul hF.continuous ) );
    · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> cases abs_cases ( F x ) <;> nlinarith [ h_integrable x ] ) ;
  · refine' Filter.Eventually.of_forall fun x => _;
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun y => ‖gradient ( fun z => Real.exp ( s * F z ) ) x‖ * L;
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
    · exact MeasureTheory.integrable_const _;
    · filter_upwards [ ] with y using by simpa using abs_real_inner_le_norm ( gradient ( fun z => Real.exp ( s * F z ) ) x ) ( gradient F ( Real.cos θ • x - Real.sin θ • y ) ) |> le_trans <| mul_le_mul_of_nonneg_left ( hgrad _ ) <| norm_nonneg _;
    · have h_grad_exp : gradient (fun z => Real.exp (s * F z)) x = (s * Real.exp (s * F x)) • gradient F x := by
        unfold gradient;
        rw [ fderiv_exp ] <;> norm_num [ hF.contDiffAt.differentiableAt ];
        rw [ fderiv_const_mul ] <;> norm_num [ hF.contDiffAt.differentiableAt ] ; ring;
        rw [ smul_smul, mul_comm ];
      simp_all +decide [ norm_smul, abs_mul ];
      nlinarith [ show 0 ≤ |s| * Real.exp ( s * F x ) * L by positivity, show 0 ≤ |s| * Real.exp ( s * F x ) * ‖gradient F x‖ by positivity, hgrad x, mul_le_mul_of_nonneg_left ( hgrad x ) ( show 0 ≤ |s| * Real.exp ( s * F x ) by positivity ) ];
  · rw [ MeasureTheory.integral_const_mul ]

/-
Interval-integrability of the covariance representation integrand `θ ↦ sin θ · H θ`.
-/
lemma gaussian_cov_sinH_intervalIntegrable (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    IntervalIntegrable (fun θ => Real.sin θ *
        ∫ x, ∫ y, inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
          (gradient F (Real.cos θ • x - Real.sin θ • y))
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      volume 0 (Real.pi/2) := by
  rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_div_two_pos.le ] at *;
  refine' MeasureTheory.Integrable.congr _ _;
  refine' fun θ => ∫ p : ( EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ), - ( F p.1 * inner ℝ ( gradient ( fun z => Real.exp ( s * F z ) ) ( Real.cos θ • p.1 + Real.sin θ • p.2 ) ) ( -Real.sin θ • p.1 + Real.cos θ • p.2 ) ) ∂ ( standardGaussianMeasureOnEuclidean ι |> Measure.prod <| standardGaussianMeasureOnEuclidean ι );
  · exact (integrable_cov_joint F L hL hF hgrad s).neg.integral_prod_right
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with θ hθ;
    have := gaussian_cov_per_theta F L hL hF hgrad s θ;
    rw [ MeasureTheory.integral_neg, MeasureTheory.integral_prod ];
    · linarith;
    · convert integrable_cov_Phi F L hL hF hgrad s θ using 1

end SYK
