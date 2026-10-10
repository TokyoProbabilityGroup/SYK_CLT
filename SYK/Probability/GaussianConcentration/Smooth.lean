import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import SYK.Probability.GaussianConcentration.StandardGaussian

/-!
# Smooth-case Gaussian covariance bound: supporting lemmas

This file develops the covariance interpolation identity used to prove the sharp
Gaussian covariance bound `SYK.GaussianConcentration.gaussian_cov_bound_smooth`.

Let `μ = standardGaussianMeasureOnEuclidean ι` and, for a `C¹` function `F` with
`‖∇F‖ ≤ L`, write `G x = exp (s * F x)`.  The covariance
`Cov = ∫ F·G - (∫ F)(∫ G)` is represented as
`Cov = ∫₀^{π/2} sin θ · (∫∫ ⟪∇G x, ∇F (cos θ • x - sin θ • y)⟫ dμ dμ) dθ`
via rotation invariance of `μ.prod μ` and the Gaussian integration-by-parts lemma
`gaussian_ibp`.  The bound then follows from Cauchy–Schwarz and `∫₀^{π/2} sin = 1`.

The module also proves the multi-index Gaussian Hermite integration by parts used by the CLT
(`lem:Gaussian-Hermite-IBP`): for `f` of class `C^{|α|}` whose partial derivatives `∂^η f`,
`η ≤ α`, grow at most exponentially, `hermiteMulti_ibp_of_expGrowth` identifies the Hermite
coefficient with the expectation of `∂^α f`, and `hermiteMulti_ibp_integrable` gives
integrability of both sides. These are general statements: they supply no derivative bounds
for the SYK partition function and do not apply the formula to `Z_N`; that specialization is
in `SYK/CLT/Chaos/PartitionHigherDerivatives.lean`. The one-coordinate Stein identities are
`gaussianReal_stein` and `pi_gaussian_stein_coord` in `StandardGaussian.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace
open intervalIntegral

namespace SYK.GaussianConcentration

variable {ι : Type*} [Fintype ι]

/-! ## Infrastructure moved from GaussianConcentration.lean -/

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
  have eq3 := pi_gaussian_stein_coord
    (fun z => g (WithLp.toLp 2 z)) i hcd C |c| (abs_nonneg c) hC hhb'
    (fun y => hdb' y i)
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
  rw [ MeasureTheory.integral_finsetSum, MeasureTheory.integral_finsetSum ];
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
  simp only [h_grad] at h_ftc
  rw [h_ftc]
  ring

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
              apply integrable_exp_mul_norm;
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

/-- The sharp Gaussian covariance bound for a `C¹` function with globally bounded
gradient. -/
lemma gaussian_cov_bound_smooth (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  rw [gaussian_cov_repr F L hL hF hgrad s]
  rw [intervalIntegral.integral_of_le Real.pi_div_two_pos.le]
  refine' le_trans (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ))
    (le_trans (MeasureTheory.integral_mono_of_nonneg _ _ _) _)
  refine' fun θ => |Real.sin θ| *
    (|s| * L ^ 2 * ∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact Continuous.integrableOn_Ioc (by continuity)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
    simpa only [norm_mul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left
      (gaussian_cov_H_bound F L hL hF hgrad s θ) (abs_nonneg _)
  · rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun θ hθ => by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le
        (by linarith [Real.pi_pos, hθ.2]))],
      ← intervalIntegral.integral_of_le Real.pi_div_two_pos.le]
    norm_num
    ring_nf
    norm_num

end SYK.GaussianConcentration


/-!
# Iterated Gaussian integration by parts

The theorem `hermiteMulti_ibp_of_expGrowth` proves the general identity in
`lem:Gaussian-Hermite-IBP` of `Paper/sections/gaussian-chaos.tex`, with
exactly its `C^{|α|}` regularity and exponential Euclidean-growth assumptions
for the partial derivatives `η ≤ α`. The creation-operator polynomials agree
with the product of probabilists' Hermite polynomials. Derivative order
independence, the intermediate product bounds, and integrability are proved
here; `ExpIBPChain` is only an internal sufficient condition for iteration.
Applying the lemma to a concrete function such as `Z_N` is left to the users of this module.
-/

open MeasureTheory
open ProbabilityTheory
open scoped Topology

namespace SYK.GaussianConcentration

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative along coordinate `i`, defined using a one-dimensional slice. -/
noncomputable def coordDeriv (i : ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun g => deriv (fun x => f (Function.update g i x)) (g i)

/-- Identify the slice derivative with the Fréchet derivative in the selected
coordinate when the function is continuously differentiable. -/
theorem coordDeriv_eq_fderiv (i : ι)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (g : ι → ℝ) :
    coordDeriv i f g = (fderiv ℝ f g) (Pi.single i 1) := by
  have hupdate : HasDerivAt (fun x => Function.update g i x) (Pi.single i 1) (g i) :=
    hasDerivAt_update g i (g i)
  have h := (hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (g i) hupdate
  simpa [coordDeriv, Function.comp_def] using h.deriv

/-- Exponential-growth Stein identity on a finite product Gaussian. Only the
chosen coordinate derivative needs a growth bound. -/
theorem coord_stein_of_expGrowth
    (h : (ι → ℝ) → ℝ) (i : ι) (hh : ContDiff ℝ 1 h)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hhb : ∀ g, |h g| ≤ C * Real.exp (c * ∑ j, |g j|))
    (hdb : ∀ g, |coordDeriv i h g| ≤ C * Real.exp (c * ∑ j, |g j|)) :
    (∫ g, g i * h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, coordDeriv i h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hdb' : ∀ g, |(fderiv ℝ h g) (Pi.single i 1)| ≤
      C * Real.exp (c * ∑ j, |g j|) := by
    intro g
    simpa [coordDeriv_eq_fderiv i hh g] using hdb g
  simpa only [← coordDeriv_eq_fderiv i hh] using
    SYK.GaussianConcentration.pi_gaussian_stein_coord h i hh C c hc hC hhb hdb'

/-- The bound for the Euclidean norm used for the disorder vector
in the manuscript. -/
theorem euclidean_norm_le_sum_abs (g : ι → ℝ) :
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ ≤ ∑ j, |g j| := by
  classical
  have hsum : (WithLp.toLp 2 g : EuclideanSpace ℝ ι) =
      ∑ j, EuclideanSpace.single j (g j) := by
    ext i
    simp
  calc
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ =
        ‖∑ j, EuclideanSpace.single j (g j)‖ := congrArg norm hsum
    _ ≤ ∑ j, ‖EuclideanSpace.single j (g j)‖ := norm_sum_le _ _
    _ = ∑ j, |g j| := by simp

/-- Every nonnegative real power is bounded by an exponential with linear argument. -/
private theorem pow_le_exp_nat_mul (x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    x ^ n ≤ Real.exp ((n : ℝ) * x) := by
  have h : x ≤ Real.exp x := by
    nlinarith [Real.add_one_le_exp x]
  calc
    x ^ n ≤ (Real.exp x) ^ n := pow_le_pow_left₀ hx h n
    _ = Real.exp ((n : ℝ) * x) := by rw [← Real.exp_nat_mul]

/-- Evaluation of a fixed integer polynomial grows at most exponentially. -/
private theorem polynomial_aeval_exp_bound (p : Polynomial ℤ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧
      ∀ x : ℝ, |Polynomial.aeval x p| ≤ C * Real.exp (c * |x|) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨Cp, cp, hCp, hcp, hp⟩ := hp
      obtain ⟨Cq, cq, hCq, hcq, hq⟩ := hq
      refine ⟨Cp + Cq, max cp cq, by positivity, by positivity, ?_⟩
      intro x
      rw [map_add]
      have hpe : Real.exp (cp * |x|) ≤ Real.exp (max cp cq * |x|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      have hqe : Real.exp (cq * |x|) ≤ Real.exp (max cp cq * |x|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      have hp' := (hp x).trans (mul_le_mul_of_nonneg_left hpe hCp)
      have hq' := (hq x).trans (mul_le_mul_of_nonneg_left hqe hCq)
      nlinarith [abs_add_le (Polynomial.aeval x p) (Polynomial.aeval x q)]
  | monomial n a =>
      refine ⟨|a|, n, abs_nonneg _, by positivity, ?_⟩
      intro x
      simp only [Polynomial.aeval_monomial, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_exp_nat_mul |x| n (abs_nonneg _)) (abs_nonneg _)

omit [DecidableEq ι] in
/-- A single coordinate is bounded by the Euclidean norm. -/
private theorem abs_coord_le_euclidean_norm (g : ι → ℝ) (i : ι) :
    |g i| ≤ ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ := by
  simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (WithLp.toLp 2 g : EuclideanSpace ℝ ι) i)

omit [DecidableEq ι] in
/-- A fixed Hermite factor has exponential growth in the disorder norm. -/
theorem hermite_factor_exp_bound (i : ι) (n : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g : ι → ℝ,
      |Polynomial.aeval (g i) (Polynomial.hermite n)| ≤
        C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  obtain ⟨C, c, hC, hc, hp⟩ := polynomial_aeval_exp_bound (Polynomial.hermite n)
  refine ⟨C, c, hC, hc, ?_⟩
  intro g
  exact (hp (g i)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (abs_coord_le_euclidean_norm g i) hc)) hC)

/-- A finite product of Hermite factors has exponential Euclidean growth. -/
theorem hermite_product_exp_bound (α : ι → ℕ) (s : Finset ι) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g : ι → ℝ,
      |∏ i ∈ s, Polynomial.aeval (g i) (Polynomial.hermite (α i))| ≤
        C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨1, 0, by positivity, le_rfl, ?_⟩
      intro g
      simp
  | @insert i s his ih =>
      obtain ⟨Ci, ci, hCi, hci, hi⟩ := hermite_factor_exp_bound i (α i)
      obtain ⟨Cs, cs, hCs, hcs, hs⟩ := ih
      refine ⟨Ci * Cs, ci + cs, by positivity, by positivity, ?_⟩
      intro g
      simp only [Finset.prod_insert his]
      rw [abs_mul]
      have hprod := mul_le_mul (hi g) (hs g) (abs_nonneg _) (by positivity)
      calc
        |Polynomial.aeval (g i) (Polynomial.hermite (α i))| *
            |∏ j ∈ s, Polynomial.aeval (g j) (Polynomial.hermite (α j))| ≤
          (Ci * Real.exp (ci * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) *
            (Cs * Real.exp (cs * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) := hprod
        _ = (Ci * Cs) * Real.exp ((ci + cs) *
            ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
          rw [add_mul, Real.exp_add]
          ring

/-- Selected-coordinate Stein identity using the Euclidean norm from the
manuscript's exponential-growth condition. -/
theorem coord_stein_of_euclidean_expGrowth
    (h : (ι → ℝ) → ℝ) (i : ι) (hh : ContDiff ℝ 1 h)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hhb : ∀ g, |h g| ≤ C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (hdb : ∀ g, |coordDeriv i h g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, g i * h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, coordDeriv i h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hbound (g : ι → ℝ) :
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) ≤
        C * Real.exp (c * ∑ j, |g j|) := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (euclidean_norm_le_sum_abs g) hc)
  exact coord_stein_of_expGrowth h i hh C c hc hC
    (fun g => (hhb g).trans (hbound g))
    (fun g => (hdb g).trans (hbound g))

/-- Iterate coordinate derivatives in the order given by a list. -/
noncomputable def partialList :
    List ι → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], f => f
  | i :: l, f => partialList l (coordDeriv i f)

omit [Fintype ι] in
/-- Splitting an ordered list of partial derivatives at any prefix. -/
theorem partialList_append (l₁ l₂ : List ι) (f : (ι → ℝ) → ℝ) :
    partialList (l₁ ++ l₂) f = partialList l₂ (partialList l₁ f) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons i l ih =>
      simpa [partialList] using ih (coordDeriv i f)

/-- The coordinate creation operator $g_i-\partial_i$. -/
noncomputable def creation (i : ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun g => g i * f g - coordDeriv i f g

/-- Product rule for the selected coordinate derivative. -/
theorem coordDeriv_mul (i : ι) {f h : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h) (g : ι → ℝ) :
    coordDeriv i (fun x => f x * h x) g =
      coordDeriv i f g * h g + f g * coordDeriv i h g := by
  rw [coordDeriv_eq_fderiv i (hf.mul hh),
    coordDeriv_eq_fderiv i hf, coordDeriv_eq_fderiv i hh,
    fderiv_fun_mul (hf.differentiable (by norm_num) g)
      (hh.differentiable (by norm_num) g)]
  simp [smul_eq_mul]
  ring

/-- Continuity of a coordinate derivative of a continuously differentiable
function. -/
theorem continuous_coordDeriv (i : ι) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (coordDeriv i f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have h : Continuous (fun g => (fderiv ℝ f g) (Pi.single i 1)) :=
    hfd.clm_apply continuous_const
  simpa only [← coordDeriv_eq_fderiv i hf] using h

/-- Coordinate differentiation preserves smoothness of every finite order. -/
theorem contDiff_coordDeriv (i : ι) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (coordDeriv i f) := by
  have hfd : ContDiff ℝ ⊤ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hconst : ContDiff ℝ ⊤
      (fun _ : ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)) := by
    fun_prop
  have h := hfd.clm_apply hconst
  simpa only [← coordDeriv_eq_fderiv i (hf.of_le (by norm_num))] using h

/-- One coordinate derivative reduces a finite differentiability order by
one. -/
theorem contDiff_coordDeriv_succ (i : ι) (n : ℕ)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (coordDeriv i f) := by
  have hfd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hconst : ContDiff ℝ n
      (fun _ : ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)) := by
    fun_prop
  have h := hfd.clm_apply hconst
  simpa only [← coordDeriv_eq_fderiv i (hf.of_le (by norm_num))] using h

/-- Iterating a prescribed list of coordinate derivatives consumes exactly
the length of that list from the differentiability order. -/
theorem contDiff_partialList (l : List ι) (n : ℕ)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (l.length + n) f) :
    ContDiff ℝ n (partialList l f) := by
  induction l generalizing f with
  | nil => simpa [partialList] using hf
  | cons i l ih =>
      have hf' : ContDiff ℝ (l.length + n + 1) f := by
        convert hf using 1
        simp [List.length_cons, add_assoc, add_comm]
      have hd : ContDiff ℝ (l.length + n) (coordDeriv i f) :=
        contDiff_coordDeriv_succ i (l.length + n) hf'
      simpa [partialList] using ih hd

/-- A continuous function with an exponential Euclidean-norm bound is
integrable against the finite product standard Gaussian. -/
theorem integrable_of_euclidean_expBound
    (h : (ι → ℝ) → ℝ) (hh : Continuous h)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hb : ∀ g, |h g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable h (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hbase : Integrable (fun g : ι → ℝ => C * Real.exp (c * ∑ j, |g j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (SYK.GaussianConcentration.integrable_exp_c_sum_abs_pi c).const_mul C
  apply hbase.mono' hh.aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_eq_abs]
  exact (hb g).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (euclidean_norm_le_sum_abs g) hc)) hC)

/-- The same bound remains integrable after multiplication by one Gaussian
coordinate. -/
theorem integrable_coord_mul_of_euclidean_expBound
    (h : (ι → ℝ) → ℝ) (hh : Continuous h) (i : ι)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hb : ∀ g, |h g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable (fun g => g i * h g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hbase : Integrable
      (fun g : ι → ℝ => C * (|g i| * Real.exp (c * ∑ j, |g j|)))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (SYK.GaussianConcentration.integrable_abs_coord_mul_exp_c_sum_abs_pi c i).const_mul C
  apply hbase.mono' ((continuous_apply i).mul hh).aestronglyMeasurable
  filter_upwards [] with g
  change |g i * h g| ≤ C * (|g i| * Real.exp (c * ∑ j, |g j|))
  rw [abs_mul]
  have hbound : |h g| ≤ C * Real.exp (c * ∑ j, |g j|) :=
    (hb g).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (euclidean_norm_le_sum_abs g) hc)) hC)
  calc
    |g i| * |h g| ≤ |g i| * (C * Real.exp (c * ∑ j, |g j|)) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = C * (|g i| * Real.exp (c * ∑ j, |g j|)) := by ring

/-- A creation-operator IBP step obtained from the selected-coordinate
exponential-growth Stein identity. The integrability hypotheses isolate the
linear integral rearrangement; they will follow from growth bounds in the
multi-index application. -/
theorem creation_ibp_of_expGrowth
    (i : ι) (φ ψ : (ι → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hhb : ∀ g, |φ g * ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (hdb : ∀ g, |coordDeriv i (fun x => φ x * ψ x) g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (hA : Integrable (fun g => g i * (φ g * ψ g))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hB : Integrable (fun g => coordDeriv i φ g * ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hD : Integrable (fun g => φ g * coordDeriv i ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    (∫ g, creation i φ g * ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, φ g * coordDeriv i ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let A : (ι → ℝ) → ℝ := fun g => g i * (φ g * ψ g)
  let B : (ι → ℝ) → ℝ := fun g => coordDeriv i φ g * ψ g
  let D : (ι → ℝ) → ℝ := fun g => φ g * coordDeriv i ψ g
  have hstein : (∫ g, A g ∂γ) = ∫ g, B g + D g ∂γ := by
    simpa only [γ, A, B, D, coordDeriv_mul i hφ hψ] using
      coord_stein_of_euclidean_expGrowth
        (fun g => φ g * ψ g) i (hφ.mul hψ) C c hc hC hhb hdb
  calc
    (∫ g, creation i φ g * ψ g ∂γ) = ∫ g, A g - B g ∂γ := by
      congr 1
      funext g
      simp [A, B, creation]
      ring
    _ = (∫ g, A g ∂γ) - ∫ g, B g ∂γ := integral_sub hA hB
    _ = (∫ g, B g + D g ∂γ) - ∫ g, B g ∂γ := by rw [hstein]
    _ = ∫ g, D g ∂γ := by rw [integral_add hB hD]; ring

/-- A creation-operator step from exponential bounds for exactly the three
products that occur in the product rule. No integrability assumptions remain. -/
theorem creation_ibp_of_expProductBounds
    (i : ι) (φ ψ : (ι → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (h0 : ∀ g, |φ g * ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (h1 : ∀ g, |coordDeriv i φ g * ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (h2 : ∀ g, |φ g * coordDeriv i ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, creation i φ g * ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, φ g * coordDeriv i ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h0' : ∀ g, |φ g * ψ g| ≤
      (2 * C) * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro g
    have he : 0 ≤ Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) :=
      Real.exp_nonneg _
    nlinarith [h0 g]
  have hd' : ∀ g, |coordDeriv i (fun x => φ x * ψ x) g| ≤
      (2 * C) * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro g
    rw [coordDeriv_mul i hφ hψ g]
    exact (abs_add_le _ _).trans (by nlinarith [h1 g, h2 g])
  have hA : Integrable (fun g => g i * (φ g * ψ g))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integrable_coord_mul_of_euclidean_expBound
      (fun g => φ g * ψ g) (hφ.continuous.mul hψ.continuous) i C c hc hC h0
  have hB : Integrable (fun g => coordDeriv i φ g * ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integrable_of_euclidean_expBound _
      ((continuous_coordDeriv i hφ).mul hψ.continuous) C c hc hC h1
  have hD : Integrable (fun g => φ g * coordDeriv i ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integrable_of_euclidean_expBound _
      (hφ.continuous.mul (continuous_coordDeriv i hψ)) C c hc hC h2
  exact creation_ibp_of_expGrowth i φ ψ hφ hψ (2 * C) c hc (by positivity)
    h0' hd' hA hB hD

/-- Iterated creation operators applied to the constant function one. -/
noncomputable def hermiteList : List ι → (ι → ℝ) → ℝ
  | [] => fun _ => 1
  | i :: l => creation i (hermiteList l)

/-- Every creation-operator Hermite function is smooth. -/
theorem contDiff_hermiteList (l : List ι) :
    ContDiff ℝ ⊤ (hermiteList l) := by
  induction l with
  | nil => simpa [hermiteList] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ι → ℝ => (1 : ℝ)))
  | cons i l ih =>
      have hcoord : ContDiff ℝ ⊤ (fun g : ι → ℝ => g i) := by fun_prop
      change ContDiff ℝ ⊤
        (fun g => g i * hermiteList l g - coordDeriv i (hermiteList l) g)
      exact (hcoord.mul ih).sub (contDiff_coordDeriv i ih)

/-- A fixed list containing each coordinate `i` exactly `α i` times. -/
noncomputable def multiIndexList (α : ι → ℕ) : List ι := by
  classical
  exact Finset.univ.toList.flatMap (fun i => List.replicate (α i) i)

omit [DecidableEq ι] in
/-- The iteration length is the total order of the multi-index. -/
theorem multiIndexList_length (α : ι → ℕ) :
    (multiIndexList α).length = ∑ i, α i := by
  classical
  simp [multiIndexList, List.length_flatMap]

noncomputable def hermiteMulti (α : ι → ℕ) : (ι → ℝ) → ℝ :=
  hermiteList (multiIndexList α)

noncomputable def partialMulti (α : ι → ℕ)
    (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  partialList (multiIndexList α) f

/-- The analytic conditions used along one specified list of coordinate
derivatives. At each step they concern only the next coordinate and the
current derivative of `f`; no derivative in an unrelated coordinate is
required. -/
def ExpIBPChain : List ι → ((ι → ℝ) → ℝ) → Prop
  | [], _ => True
  | i :: l, f =>
      ∃ C c : ℝ, 0 ≤ c ∧ 0 ≤ C ∧
          (∀ g, |hermiteList l g * f g| ≤
            C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) ∧
          (∀ g, |coordDeriv i (hermiteList l) g * f g| ≤
            C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) ∧
          (∀ g, |hermiteList l g * coordDeriv i f g| ≤
            C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) ∧
          ExpIBPChain l (coordDeriv i f)

/-- Multi-coordinate Gaussian IBP from exponential bounds along precisely
the derivative chain used by the multi-index. -/
theorem hermiteList_ibp_of_expChain (l : List ι)
    {f : (ι → ℝ) → ℝ} (hfSmooth : ContDiff ℝ l.length f)
    (hf : ExpIBPChain l f) :
    (∫ g, hermiteList l g * f g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialList l f g
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  induction l generalizing f with
  | nil => simp [hermiteList, partialList]
  | cons i l ih =>
      rcases hf with ⟨C, c, hc, hC, h0, h1, h2, htail⟩
      have hfOrder : ContDiff ℝ (l.length + 1) f := by
        simpa [List.length_cons] using hfSmooth
      have hψ : ContDiff ℝ 1 f := hfOrder.of_le (by norm_num)
      have hφ : ContDiff ℝ 1 (hermiteList l) :=
        (contDiff_hermiteList l).of_le (by norm_num)
      calc
        (∫ g, hermiteList (i :: l) g * f g
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
            ∫ g, hermiteList l g * coordDeriv i f g
              ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
                simpa [hermiteList] using
                  creation_ibp_of_expProductBounds i (hermiteList l) f
                    hφ hψ C c hc hC h0 h1 h2
        _ = ∫ g, partialList l (coordDeriv i f) g
              ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
          ih (contDiff_coordDeriv_succ i l.length hfOrder) htail
        _ = ∫ g, partialList (i :: l) f g
              ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := rfl

omit [Fintype ι] in
/-- A coordinate derivative of a polynomial depending on that coordinate alone. -/
theorem coordDeriv_aeval (i : ι) (p : Polynomial ℤ) (g : ι → ℝ) :
    coordDeriv i (fun h => Polynomial.aeval (h i) p) g =
      Polynomial.aeval (g i) (Polynomial.derivative p) := by
  classical
  simp [coordDeriv, Polynomial.deriv_aeval]

private def UpdateInvariant (i : ι) (f : (ι → ℝ) → ℝ) : Prop := by
  classical
  exact ∀ g x, f (Function.update g i x) = f g

omit [Fintype ι] in
private theorem coordDeriv_updateInvariant {i j : ι} (hij : i ≠ j)
    {f : (ι → ℝ) → ℝ} (hf : UpdateInvariant i f) :
    UpdateInvariant i (coordDeriv j f) := by
  classical
  intro g x
  unfold coordDeriv
  have hfun : (fun y => f (Function.update (Function.update g i x) j y)) =
      (fun y => f (Function.update g j y)) := by
    funext y
    rw [Function.update_comm hij x y g, hf (Function.update g j y) x]
  rw [hfun]
  simp [Function.update_of_ne hij.symm]

omit [Fintype ι] in
private theorem creation_updateInvariant {i j : ι} (hij : i ≠ j)
    {f : (ι → ℝ) → ℝ} (hf : UpdateInvariant i f) :
    UpdateInvariant i (creation j f) := by
  classical
  intro g x
  simp [creation, hf g x, coordDeriv_updateInvariant hij hf g x,
    Function.update_of_ne hij.symm]

omit [Fintype ι] in
private theorem hermiteList_updateInvariant (i : ι) (l : List ι)
    (hi : i ∉ l) : UpdateInvariant i (hermiteList l) := by
  induction l with
  | nil => intro g x; rfl
  | cons j l ih =>
      simp only [List.mem_cons, not_or] at hi
      exact creation_updateInvariant hi.1 (ih hi.2)

omit [Fintype ι] in
private theorem creation_aeval_mul_invariant (i : ι) (p : Polynomial ℤ)
    (q : (ι → ℝ) → ℝ) (hq : UpdateInvariant i q) (g : ι → ℝ) :
    creation i (fun h => Polynomial.aeval (h i) p * q h) g =
      (g i * Polynomial.aeval (g i) p -
        Polynomial.aeval (g i) (Polynomial.derivative p)) * q g := by
  classical
  have hfun : (fun x => Polynomial.aeval x p * q (Function.update g i x)) =
      (fun x => Polynomial.aeval x p * q g) := by
    funext x
    rw [hq g x]
  simp [creation, coordDeriv, hfun, Polynomial.deriv_aeval]
  ring

omit [Fintype ι] in
private theorem hermiteList_replicate_append (i : ι) (n : ℕ) (l : List ι)
    (hi : i ∉ l) (g : ι → ℝ) :
    hermiteList (List.replicate n i ++ l) g =
      Polynomial.aeval (g i) (Polynomial.hermite n) * hermiteList l g := by
  induction n generalizing g with
  | zero => simp [Polynomial.hermite_zero]
  | succ n ih =>
      change creation i (hermiteList (List.replicate n i ++ l)) g = _
      have hfun : hermiteList (List.replicate n i ++ l) =
          fun h => Polynomial.aeval (h i) (Polynomial.hermite n) * hermiteList l h := by
        funext h
        exact ih h
      rw [hfun, creation_aeval_mul_invariant i (Polynomial.hermite n)
        (hermiteList l) (hermiteList_updateInvariant i l hi) g,
        Polynomial.hermite_succ]
      simp [Polynomial.aeval_X, sub_mul]

omit [Fintype ι] in
private theorem hermiteList_flatMap_replicate (α : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (g : ι → ℝ) :
    hermiteList (l.flatMap (fun i => List.replicate (α i) i)) g =
      (l.map (fun i => Polynomial.aeval (g i) (Polynomial.hermite (α i)))).prod := by
  induction l generalizing g with
  | nil => simp [hermiteList]
  | cons i l ih =>
      obtain ⟨hil, hnodup⟩ := List.nodup_cons.mp hl
      have hnot : i ∉ l.flatMap (fun j => List.replicate (α j) j) := by
        intro h
        obtain ⟨j, hj, hij⟩ := List.mem_flatMap.mp h
        have heq : i = j := (List.mem_replicate.mp hij).2
        exact hil (heq ▸ hj)
      simp only [List.flatMap_cons, List.map_cons, List.prod_cons]
      rw [hermiteList_replicate_append i (α i)
        (l.flatMap (fun j => List.replicate (α j) j)) hnot g,
        ih hnodup g]

/-- The creation-operator Hermite polynomial is the usual product of
probabilists' Hermite polynomials. -/
theorem hermiteMulti_eq_prod (α : ι → ℕ) (g : ι → ℝ) :
    hermiteMulti α g =
      ∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i)) := by
  classical
  unfold hermiteMulti multiIndexList
  rw [hermiteList_flatMap_replicate α Finset.univ.toList
    (Finset.nodup_toList Finset.univ)]
  simp

/-- The multi-index Hermite function itself has exponential growth. -/
theorem hermiteMulti_exp_bound (α : ι → ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g : ι → ℝ,
      |hermiteMulti α g| ≤
        C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hermite_product_exp_bound α Finset.univ
  exact ⟨C, c, hC, hc, fun g => by simpa [hermiteMulti_eq_prod] using hb g⟩

/-- The left-hand side of the Hermite IBP formula is integrable under the
manuscript's exponential bound on `f`. -/
theorem integrable_hermiteMulti_mul_of_expGrowth (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (Cf : ℝ) (hCf : 0 ≤ Cf)
    (hfb : ∀ g, |f g| ≤
      Cf * Real.exp (Cf * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable (fun g => hermiteMulti α g * f g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  obtain ⟨Ch, ch, hCh, hch, hhb⟩ := hermiteMulti_exp_bound α
  have hb : ∀ g, |hermiteMulti α g * f g| ≤
      (Ch * Cf) * Real.exp ((ch + Cf) *
        ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro g
    rw [abs_mul]
    calc
      |hermiteMulti α g| * |f g| ≤
          (Ch * Real.exp (ch * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) *
            (Cf * Real.exp (Cf * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :=
        mul_le_mul (hhb g) (hfb g) (abs_nonneg _) (by positivity)
      _ = (Ch * Cf) * Real.exp ((ch + Cf) *
          ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
        rw [add_mul, Real.exp_add]
        ring
  exact integrable_of_euclidean_expBound _
    ((contDiff_hermiteList (multiIndexList α)).continuous.mul hf)
    (Ch * Cf) (ch + Cf) (by positivity) (by positivity) hb

/-- The exponential-growth chain yields the multi-index formula with the
standard product of probabilists' Hermite polynomials. -/
theorem hermiteMulti_ibp_of_expChain (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hfSmooth : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hf : ExpIBPChain (multiIndexList α) f) :
    (∫ g, (∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i))) * f g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialMulti α f g
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have horder : ContDiff ℝ (multiIndexList α).length f := by
    simpa only [multiIndexList_length] using hfSmooth
  simpa only [← hermiteMulti_eq_prod, hermiteMulti, partialMulti] using
    hermiteList_ibp_of_expChain (multiIndexList α) horder hf

/-- Coordinate derivatives commute for a twice continuously differentiable function. -/
theorem coordDeriv_comm (i j : ι) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    coordDeriv i (coordDeriv j f) = coordDeriv j (coordDeriv i f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have he (k : ι) : coordDeriv k f = fun g => fderiv ℝ f g (Pi.single k 1) :=
    funext (coordDeriv_eq_fderiv k hf1)
  funext g
  rw [coordDeriv_eq_fderiv i (contDiff_coordDeriv_succ j 1 hf),
    coordDeriv_eq_fderiv j (contDiff_coordDeriv_succ i 1 hf), he i, he j]
  simp only [fderiv_clm_apply (hd.differentiable (by norm_num) g)
    (differentiableAt_const _), fderiv_const_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- Reordering partial derivatives needs only as many derivatives as the list length. -/
theorem partialList_perm {l k : List ι} (hp : l.Perm k)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ l.length f) :
    partialList l f = partialList k f := by
  induction hp generalizing f with
  | nil => rfl
  | @cons i l k hp ih =>
      exact ih (contDiff_coordDeriv_succ i l.length hf)
  | swap i j l =>
      simp only [partialList]
      rw [coordDeriv_comm j i (hf.of_le (by
        exact_mod_cast (show 2 ≤ (j :: i :: l).length by simp)))]
  | trans hp hq ih ih' =>
      exact (ih hf).trans (ih' (by simpa only [← hp.length_eq] using hf))

/-- Each coordinate occurs with its prescribed multiplicity. -/
theorem multiIndexList_count (α : ι → ℕ) (i : ι) :
    (multiIndexList α).count i = α i := by
  classical
  simp [multiIndexList, List.count_flatMap, List.count_replicate]

/-- An ordered derivative list represents the multi-index given by its multiplicities. -/
theorem partialList_eq_partialMulti (l : List ι)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ l.length f) :
    partialList l f = partialMulti (fun i => l.count i) f := by
  apply partialList_perm _ hf
  exact List.perm_iff_count.mpr fun i => (multiIndexList_count (fun j => l.count j) i).symm

private def ExpBound (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g,
    |f g| ≤ C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)

omit [DecidableEq ι] in
private theorem ExpBound.const (a : ℝ) : ExpBound (fun _ : ι → ℝ => a) := by
  exact ⟨|a|, 0, abs_nonneg _, le_rfl, by simp⟩

omit [DecidableEq ι] in
private theorem ExpBound.mul {f h : (ι → ℝ) → ℝ}
    (hf : ExpBound f) (hh : ExpBound h) : ExpBound (fun g => f g * h g) := by
  obtain ⟨C, c, hC, hc, hf⟩ := hf
  obtain ⟨D, d, hD, hd, hh⟩ := hh
  refine ⟨C * D, c + d, by positivity, by positivity, ?_⟩
  intro g
  rw [abs_mul]
  calc
    |f g| * |h g| ≤ (C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) *
        (D * Real.exp (d * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :=
      mul_le_mul (hf g) (hh g) (abs_nonneg _) (by positivity)
    _ = _ := by rw [add_mul, Real.exp_add]; ring

omit [DecidableEq ι] in
private theorem ExpBound.sub {f h : (ι → ℝ) → ℝ}
    (hf : ExpBound f) (hh : ExpBound h) : ExpBound (fun g => f g - h g) := by
  obtain ⟨C, c, hC, hc, hf⟩ := hf
  obtain ⟨D, d, hD, hd, hh⟩ := hh
  refine ⟨C + D, max c d, by positivity, by positivity, ?_⟩
  intro g
  have hfc := (hf g).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left c d) (norm_nonneg _))) hC)
  have hhd := (hh g).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right c d) (norm_nonneg _))) hD)
  exact (abs_sub _ _).trans (by nlinarith)

private inductive PolyFunction : ((ι → ℝ) → ℝ) → Prop
  | const (a : ℝ) : PolyFunction (fun _ => a)
  | coord (i : ι) : PolyFunction (fun g => g i)
  | sub {f h} : PolyFunction f → PolyFunction h → PolyFunction (fun g => f g - h g)
  | mul {f h} : PolyFunction f → PolyFunction h → PolyFunction (fun g => f g * h g)

omit [DecidableEq ι] in
private theorem PolyFunction.smooth {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) : ContDiff ℝ ⊤ f := by
  induction hf with
  | const => fun_prop
  | coord => fun_prop
  | sub _ _ hf hh => exact hf.sub hh
  | mul _ _ hf hh => exact hf.mul hh

omit [DecidableEq ι] in
private theorem PolyFunction.expBound {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) : ExpBound f := by
  induction hf with
  | const a => exact ExpBound.const a
  | coord i =>
      simpa [ExpBound, Polynomial.hermite_one] using hermite_factor_exp_bound (ι := ι) i 1
  | sub _ _ hf hh => exact hf.sub hh
  | mul _ _ hf hh => exact hf.mul hh

private theorem PolyFunction.deriv_closed {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) (i : ι) : PolyFunction (coordDeriv i f) := by
  induction hf with
  | const a =>
      change PolyFunction (fun g => deriv (fun _ : ℝ => a) (g i))
      simpa using (PolyFunction.const (ι := ι) 0)
  | coord j =>
      by_cases hij : j = i
      · subst j
        change PolyFunction (fun g => deriv (fun x => (Function.update g i x) i) (g i))
        simpa using (PolyFunction.const (ι := ι) 1)
      · change PolyFunction (fun g => deriv (fun x => (Function.update g i x) j) (g i))
        simpa [Function.update_of_ne hij] using (PolyFunction.const (ι := ι) 0)
  | @sub f h hf hh ihf ihh =>
      have he : coordDeriv i (fun g => f g - h g) =
          fun g => coordDeriv i f g - coordDeriv i h g := by
        funext g
        simp only [coordDeriv_eq_fderiv i ((hf.smooth.sub hh.smooth).of_le (by norm_num)),
          coordDeriv_eq_fderiv i (hf.smooth.of_le (by norm_num)),
          coordDeriv_eq_fderiv i (hh.smooth.of_le (by norm_num)),
          fderiv_fun_sub (hf.smooth.differentiable (by simp) g)
            (hh.smooth.differentiable (by simp) g), sub_apply]
      rw [he]
      exact ihf.sub ihh
  | @mul f h hf hh ihf ihh =>
      have he : coordDeriv i (fun g => f g * h g) =
          fun g => coordDeriv i f g * h g - (-(f g * coordDeriv i h g)) := by
        funext g
        rw [coordDeriv_mul i (hf.smooth.of_le (by norm_num))
          (hh.smooth.of_le (by norm_num))]
        ring
      rw [he]
      exact (ihf.mul hh).sub (by
        simpa using (PolyFunction.const 0).sub (hf.mul ihh))

private theorem polyFunction_hermiteList (l : List ι) : PolyFunction (hermiteList l) := by
  induction l with
  | nil => exact PolyFunction.const 1
  | cons i l ih => exact ((PolyFunction.coord i).mul ih).sub (ih.deriv_closed i)

omit [DecidableEq ι] in
private theorem expBound_enlarge {f : (ι → ℝ) → ℝ} {C c D d : ℝ}
    (hC : 0 ≤ C) (hCD : C ≤ D) (hcd : c ≤ d)
    (hf : ∀ g, |f g| ≤ C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    ∀ g, |f g| ≤ D * Real.exp (d * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  intro g
  exact (hf g).trans (mul_le_mul hCD
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcd (norm_nonneg _)))
    (Real.exp_nonneg _) (hC.trans hCD))

private theorem expIBPChain_of_prefix_bounds (l : List ι) {f : (ι → ℝ) → ℝ}
    (hb : ∀ p : List ι, p.IsPrefix l → ExpBound (partialList p f)) :
    ExpIBPChain l f := by
  induction l generalizing f with
  | nil => trivial
  | cons i l ih =>
      have hf : ExpBound f := hb [] (by simp)
      have hd : ExpBound (coordDeriv i f) := hb [i] (by simp)
      have hp := polyFunction_hermiteList l
      obtain ⟨C₀, c₀, hC₀, hc₀, h₀⟩ := hp.expBound.mul hf
      obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := (hp.deriv_closed i).expBound.mul hf
      obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := hp.expBound.mul hd
      refine ⟨C₀ + C₁ + C₂, c₀ + c₁ + c₂, by positivity, by positivity,
        expBound_enlarge hC₀ (by linarith) (by linarith) h₀,
        expBound_enlarge hC₁ (by linarith) (by linarith) h₁,
        expBound_enlarge hC₂ (by linarith) (by linarith) h₂, ?_⟩
      apply ih
      intro p hp
      exact hb (i :: p) (by simpa using hp)

/-- `lem:Gaussian-Hermite-IBP`: only the partial derivatives indexed by
`η ≤ α` need exponential growth, and finite smoothness of order `|α|` suffices. -/
theorem hermiteMulti_ibp_of_expGrowth (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ g,
      |partialMulti η f g| ≤ C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, (∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i))) * f g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialMulti α f g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  apply hermiteMulti_ibp_of_expChain α hf
  apply expIBPChain_of_prefix_bounds
  intro p hp
  have hcount : (fun i => p.count i) ≤ α := by
    intro i
    rw [← multiIndexList_count α i]
    exact hp.sublist.count_le i
  obtain ⟨C, hC, hb⟩ := hgrowth (fun i => p.count i) hcount
  have hsmooth : ContDiff ℝ p.length f := hf.of_le (by
    exact_mod_cast (hp.length_le.trans_eq (multiIndexList_length α)))
  rw [partialList_eq_partialMulti p hsmooth]
  exact ⟨C, C, hC.le, hC.le, hb⟩

/-- Both expectations in `lem:Gaussian-Hermite-IBP` are genuine integrals
under the manuscript's assumptions, including when `α = 0`. -/
theorem hermiteMulti_ibp_integrable (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ g,
      |partialMulti η f g| ≤ C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable (fun g => (∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i))) * f g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    Integrable (partialMulti α f) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  obtain ⟨C₀, hC₀, h₀⟩ := hgrowth 0 (by simp)
  have hzero : partialMulti (0 : ι → ℕ) f = f := by
    have hnil : ∀ l : List ι, l.flatMap (fun _ => ([] : List ι)) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ l ih => simp [ih]
    simp [partialMulti, multiIndexList, hnil, partialList]
  rw [hzero] at h₀
  obtain ⟨C, hC, hb⟩ := hgrowth α le_rfl
  have hd : Continuous (partialMulti α f) := by
    apply (contDiff_partialList (multiIndexList α) 0 _).continuous
    simpa [multiIndexList_length] using hf
  constructor
  · simpa only [← hermiteMulti_eq_prod] using
      integrable_hermiteMulti_mul_of_expGrowth α hf.continuous C₀ hC₀.le h₀
  · exact integrable_of_euclidean_expBound _ hd C C hC.le hC.le hb

private theorem polyFunction_partialList (l : List ι) {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) : PolyFunction (partialList l f) := by
  induction l generalizing f with
  | nil => exact hf
  | cons i l ih => exact ih (hf.deriv_closed i)

/-- Integration by parts for the pairing of two multivariate Hermite
functions. Their polynomial structure supplies all growth hypotheses. -/
theorem hermiteMulti_pair_ibp (α β : ι → ℕ) :
    (∫ g, hermiteMulti α g * hermiteMulti β g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialMulti α (hermiteMulti β) g
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hβ : PolyFunction (hermiteMulti β) :=
    polyFunction_hermiteList (multiIndexList β)
  have hdiff : ContDiff ℝ (↑(∑ i : ι, α i)) (hermiteMulti β) :=
    hβ.smooth.of_le (by simp)
  have hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ D : ℝ, 0 < D ∧ ∀ g,
      |partialMulti η (hermiteMulti β) g| ≤
        D * Real.exp (D * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro η _
    obtain ⟨C, c, hC, hc, hb⟩ :=
      (polyFunction_partialList (multiIndexList η) hβ).expBound
    let D := max C c + 1
    have hD : 0 < D := by dsimp [D]; positivity
    refine ⟨D, hD, ?_⟩
    simpa only [partialMulti] using
      expBound_enlarge hC (by dsimp [D]; linarith [le_max_left C c])
        (by dsimp [D]; linarith [le_max_right C c]) hb
  simpa only [← hermiteMulti_eq_prod] using
    hermiteMulti_ibp_of_expGrowth α hdiff hgrowth

end SYK.GaussianConcentration
