module

public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate

public section

/-!
# The standard Gaussian on a finite coordinate space

For any finite index type `ι`, `standardGaussianMeasureOnEuclidean ι` is the product
of standard one-dimensional Gaussians transported to `EuclideanSpace ℝ ι`. The file
proves that it is a Gaussian probability measure and the integrability of
exponential-growth functions against it, the Herbst-type step from a covariance bound
to an exponential-moment bound (`herbst_of_cov_bound`), and Stein's identity: in one
dimension (`gaussianReal_stein`) and coordinatewise on the product measure
(`pi_gaussian_stein_coord`). It is independent of the SYK model.

The concentration proof uses the rotation covariance interpolation in `Smooth.lean`,
mollification in `Lipschitz.lean`, and `herbst_of_cov_bound` in this file.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK.GaussianConcentration

/-- One standard Gaussian measure for every finite Euclidean coordinate type.
This is the product of standard one-dimensional Gaussians pushed forward to the
Euclidean (`L²`) structure on the coordinate space.

It equals mathlib's `stdGaussian (EuclideanSpace ℝ ι)` by `map_pi_eq_stdGaussian`. The product
form is kept as the definition on purpose: the coordinatewise Stein identity, the Hermite
expansion and the CLT work in this form, so proofs use `stdGaussian` lemmas only through that
equation. -/
@[expose] noncomputable def standardGaussianMeasureOnEuclidean
    (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2)

/-- The standard Euclidean Gaussian is a probability measure. -/
instance standardGaussianMeasureOnEuclidean_isProbability
    {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (standardGaussianMeasureOnEuclidean ι) := by
  unfold standardGaussianMeasureOnEuclidean
  exact Measure.isProbabilityMeasure_map
    (WithLp.measurable_toLp 2 (ι → ℝ)).aemeasurable

/-- The finite product of standard real Gaussians is a Gaussian measure. -/
instance isGaussian_pi_gaussianReal {ι : Type*} [Fintype ι] :
    IsGaussian (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  -- Transport `stdGaussian` back along the identification `toLp 2` (`map_pi_eq_stdGaussian`).
  have h : (Measure.pi fun _ : ι => gaussianReal 0 1) =
      (stdGaussian (EuclideanSpace ℝ ι)).map
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)) := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id.symm
  rw [h]
  infer_instance

/-- The standard Euclidean Gaussian measure is a Gaussian measure. -/
instance standardGaussianMeasureOnEuclidean_isGaussian {ι : Type*} [Fintype ι] :
    IsGaussian (standardGaussianMeasureOnEuclidean ι) := by
  unfold standardGaussianMeasureOnEuclidean
  rw [show (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm from rfl]
  infer_instance

/--
Exponential-of-norm functions are integrable against the standard Euclidean Gaussian.
By Fernique's theorem, `exp (C ‖x‖²)` is integrable for some `C > 0`, and completing the
square gives `c ‖x‖ ≤ C ‖x‖² + c² / (4C)`.
-/
theorem integrable_exp_mul_norm {ι : Type*} [Fintype ι] (c : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (c * ‖x‖))
      (standardGaussianMeasureOnEuclidean ι) := by
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq
    (standardGaussianMeasureOnEuclidean ι)
  refine (hint.const_mul (Real.exp (c ^ 2 / (4 * C)))).mono' (by fun_prop)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h : 0 ≤ C * (‖x‖ - c / (2 * C)) ^ 2 := by positivity
  have hC' : C ≠ 0 := hC.ne'
  calc c * ‖x‖ = C * ‖x‖ ^ 2 + c ^ 2 / (4 * C) - C * (‖x‖ - c / (2 * C)) ^ 2 := by
        field_simp
        ring
    _ ≤ c ^ 2 / (4 * C) + C * ‖x‖ ^ 2 := by linarith

/-- If Φ is differentiable, Φ(0) = 0, and |Φ'(s) - m| ≤ c |s|, then
Φ(t) ≤ m t + c t² / 2. For s ≥ 0, Φ'(s) - m ≤ c s; for s ≤ 0,
Φ'(s) - m ≥ c s. Thus ψ(s) = Φ(s) - (m s + c s² / 2) is maximized at 0. -/
private lemma quadratic_bound_of_deriv_sub_le {Φ : ℝ → ℝ} {m c : ℝ}
    (hdiff : Differentiable ℝ Φ) (h0 : Φ 0 = 0)
    (hderiv : ∀ s, |deriv Φ s - m| ≤ c * |s|) (t : ℝ) :
    Φ t ≤ m * t + c * t ^ 2 / 2 := by
  let psi : ℝ → ℝ := fun s ↦ Φ s - (m * s + c * s ^ 2 / 2)
  have hpsi_deriv (s : ℝ) : deriv psi s = deriv Φ s - (m + c * s) := by
    have hquad := ((hasDerivAt_id s).const_mul m).add
      (((hasDerivAt_id s).pow 2).const_mul c |>.div_const 2)
    have hsub := (hdiff.differentiableAt.hasDerivAt.sub hquad).deriv
    change deriv (Φ - fun x : ℝ ↦ m * x + c * x ^ 2 / 2) s = _
    have hfun :
        (Φ - fun x : ℝ ↦ m * x + c * x ^ 2 / 2) =
          Φ - ((fun y : ℝ ↦ m * id y) + fun x ↦ c * (id ^ 2) x / 2) := by
      funext x
      change Φ x - (m * x + c * x ^ 2 / 2) =
        Φ x - (m * x + c * x ^ 2 / 2)
      rfl
    rw [hfun, hsub]
    simp only [id_eq, Nat.cast_ofNat, mul_one]
    ring
  by_cases ht : 0 ≤ t
  · have h_antitone : AntitoneOn psi (Set.Icc 0 t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
      · exact hdiff.continuous.continuousOn.sub (by fun_prop)
      · exact hdiff.differentiableOn.sub (by fun_prop)
      · intro x hx
        rw [hpsi_deriv]
        have hb := (abs_le.mp (hderiv x)).2
        have hxIcc : x ∈ Set.Icc 0 t := interior_subset hx
        rw [abs_of_nonneg hxIcc.1] at hb
        linarith
    have hmono := h_antitone (show 0 ∈ Set.Icc 0 t by exact ⟨le_rfl, ht⟩)
      (show t ∈ Set.Icc 0 t by exact ⟨ht, le_rfl⟩) ht
    simp [psi, h0] at hmono
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht
    have h_mvt := exists_deriv_eq_slope psi htneg
      (hdiff.continuous.continuousOn.sub (by fun_prop))
      (hdiff.differentiableOn.sub (by fun_prop))
    obtain ⟨ξ, hξ, hξeq⟩ := h_mvt
    have hb := (abs_le.mp (hderiv ξ)).1
    rw [abs_of_neg hξ.2] at hb
    have hnonneg : 0 ≤ deriv psi ξ := by
      rw [hpsi_deriv]
      linarith
    rw [hξeq, le_div_iff₀ (by linarith : 0 < 0 - t)] at hnonneg
    simp [psi, h0] at hnonneg
    linarith

/-- Every real exponential of a Lipschitz function is Gaussian integrable.
The growth bound uses `L.toNNReal`, so no positivity assumption on `L` is needed. -/
lemma integrable_exp_smul_lipschitz {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ)
    (hLip : LipschitzWith L.toNNReal F) (s : ℝ) :
    Integrable (fun x => Real.exp (s * F x)) (standardGaussianMeasureOnEuclidean ι) := by
  let K : ℝ := L.toNNReal
  have hdom := (integrable_exp_mul_norm (ι := ι) (|s| * K)).const_mul
    (Real.exp (|s| * |F 0|))
  refine hdom.mono'
    (Real.continuous_exp.comp (continuous_const.mul hLip.continuous)).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hdist : |F x - F 0| ≤ K * ‖x‖ := by
    simpa only [Real.dist_eq, dist_zero_right, K] using hLip.dist_le_mul x 0
  have hgrowth : |F x| ≤ |F 0| + K * ‖x‖ := by
    calc
      |F x| = |F x - F 0 + F 0| := congrArg abs (sub_add_cancel (F x) (F 0)).symm
      _ ≤ |F x - F 0| + |F 0| := abs_add_le _ _
      _ ≤ |F 0| + K * ‖x‖ := by
        simpa only [add_comm] using add_le_add_right hdist |F 0|
  calc
    s * F x ≤ |s * F x| := le_abs_self _
    _ = |s| * |F x| := abs_mul _ _
    _ ≤ |s| * (|F 0| + K * ‖x‖) :=
      mul_le_mul_of_nonneg_left hgrowth (abs_nonneg s)
    _ = |s| * |F 0| + |s| * K * ‖x‖ := by ring

/-- For `F` satisfying `LipschitzWith L.toNNReal F`, every real exponent
belongs to its Gaussian integrability set. -/
private lemma integrableExpSet_lipschitz_eq_univ {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ)
    (hLip : LipschitzWith L.toNNReal F) :
    integrableExpSet F (standardGaussianMeasureOnEuclidean ι) = Set.univ := by
  ext s
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact integrable_exp_smul_lipschitz F L hLip s

/--
**Herbst's argument, assembly step.**  Given the sharp Gaussian covariance bound
`|∫ F e^{sF} - (∫ F)(∫ e^{sF})| ≤ L² |s| ∫ e^{sF}` for every `s`, the centered function
`F - ∫ F` has a sub-Gaussian moment-generating function with parameter `L²`.

The cumulant generating function `Φ = cgf F μ` is analytic (hence differentiable) on all of
`ℝ` since every exponential moment is finite; it satisfies `Φ 0 = 0` and
`Φ'(s) = (∫ F e^{sF}) / ∫ e^{sF}`.  The covariance bound gives `|Φ'(s) - ∫ F| ≤ L² |s|`, and
`quadratic_bound_of_deriv_sub_le` yields `Φ t ≤ (∫ F) t + L² t² / 2`, which is exactly the
claimed bound after unfolding `mgf (F - ∫ F) μ t = exp (Φ t - t ∫ F)`.
-/
lemma herbst_of_cov_bound {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ)
    (hLip : LipschitzWith L.toNNReal F)
    (hcov : ∀ s : ℝ,
      |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
          - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
            * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
        ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι))
    (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
        (standardGaussianMeasureOnEuclidean ι) t ≤
      Real.exp (L ^ 2 * t ^ 2 / 2) := by
  -- Let $\Phi(s) = \log \mathbb{E}[e^{sF}]$.
  set Φ : ℝ → ℝ := fun s => Real.log (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean
    ι)
  -- We need to show that $\Phi(t) \leq mt + L^2 t^2 / 2$.
  have hΦ : Φ t ≤ (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι) * t + L^2 * t^2 / 2 := by
    apply quadratic_bound_of_deriv_sub_le
    · have h_analytic : ∀ s : ℝ, AnalyticAt ℝ Φ s := by
        intro s
        apply ProbabilityTheory.analyticAt_cgf
        rw [integrableExpSet_lipschitz_eq_univ F L hLip]
        simp only [interior_univ, Set.mem_univ]
      exact fun s => (h_analytic s |> AnalyticAt.differentiableAt)
    · simp [Φ]
    · intro s
      have h_deriv : deriv Φ s = (∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean
        ι) / (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
        apply ProbabilityTheory.deriv_cgf
        rw [integrableExpSet_lipschitz_eq_univ F L hLip]
        simp only [interior_univ, Set.mem_univ]
      rw [h_deriv, div_sub']
      · rw [abs_div, abs_of_nonneg (show 0 ≤ ∫ x, Real.exp (s * F x)
          ∂standardGaussianMeasureOnEuclidean ι from MeasureTheory.integral_nonneg fun _ =>
          Real.exp_nonneg _)]
        exact div_le_of_le_mul₀ (MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _)
          (by positivity) (by simpa only [mul_comm] using hcov s)
      · refine ne_of_gt (?_)
        rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
        · simp [Function.support, Real.exp_ne_zero]
        · exact Filter.Eventually.of_forall fun x => Real.exp_nonneg _
        · exact integrable_exp_smul_lipschitz F L hLip s
  convert Real.exp_le_exp.mpr (show Φ t - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι) * t ≤
    L ^ 2 * t ^ 2 / 2 from by linarith) using 1
  rw [Real.exp_sub, Real.exp_log]
  · simp only [mgf, mul_sub, Real.exp_sub]
    rw [MeasureTheory.integral_div, mul_comm]
  · apply ProbabilityTheory.mgf_pos
    exact integrable_exp_smul_lipschitz F L hLip t

/-- `exp (c |y|)` is integrable against the one-dimensional standard Gaussian. -/
lemma integrable_exp_abs_gaussianReal (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (c * |y|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal c).add
    (integrable_exp_mul_gaussianReal (-c))).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  cases abs_cases x with
  | inl h =>
      rw [h.1]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
  | inr h =>
      rw [h.1, mul_neg, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)

/-- The standard Gaussian density satisfies `φ' = -x φ`. -/
private lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  have hfun : gaussianPDFReal 0 1 = fun y => (√(2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    ext y
    simp [gaussianPDFReal]
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x :=
    ((hasDerivAt_pow 2 x).neg.div_const 2).congr_deriv (by
      norm_num
      ring)
  simp only [hfun]
  exact (h.exp.const_mul (√(2 * Real.pi))⁻¹).congr_deriv (by ring)

/-- An integrable function for the standard Gaussian, multiplied by the Gaussian density,
is Lebesgue integrable. -/
private lemma integrable_gaussianPDFReal_mul {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using hf

/--
**One-dimensional Gaussian integration by parts (Stein's identity).**  For a `C¹`
function `g` on `ℝ` whose value and derivative grow no faster than `C e^{c|x|}`, integration
against the standard Gaussian satisfies `∫ x * g x dγ = ∫ g' x dγ`.  This follows from the
boundary-free integration-by-parts on `ℝ` together with the identity `φ' = -x φ` for the
Gaussian density `φ`.
-/
lemma gaussianReal_stein (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'cont : Continuous g')
    (C c : ℝ) (hgbound : ∀ x, |g x| ≤ C * Real.exp (c * |x|))
    (hg'bound : ∀ x, |g' x| ≤ C * Real.exp (c * |x|)) :
    ∫ x, x * g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) := by
  have hgcont : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hI_g : Integrable g (gaussianReal 0 1) :=
    ((integrable_exp_abs_gaussianReal c).const_mul C).mono' hgcont.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hgbound x)
  have hI_g' : Integrable g' (gaussianReal 0 1) :=
    ((integrable_exp_abs_gaussianReal c).const_mul C).mono' hg'cont.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hg'bound x)
  have hI_xg : Integrable (fun x => x * g x) (gaussianReal 0 1) := by
    refine ((integrable_exp_abs_gaussianReal (c + 1)).const_mul C).mono' (by fun_prop)
      (ae_of_all _ fun x => ?_)
    have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
    calc ‖x * g x‖ = |x| * |g x| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ Real.exp |x| * (C * Real.exp (c * |x|)) :=
        mul_le_mul hx (hgbound x) (abs_nonneg _) (Real.exp_nonneg _)
      _ = C * Real.exp ((c + 1) * |x|) := by
        rw [add_mul, one_mul, Real.exp_add]
        ring
  -- Write both sides as Lebesgue integrals against the density `φ` and integrate by parts
  -- with `u = g` and `v = φ`, using `φ' = -x φ`.
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := gaussianPDFReal 0 1) (u' := g') (v' := fun x => -(x * gaussianPDFReal 0 1 x))
    (fun x _ => hg x) (fun x _ => hasDerivAt_gaussianPDFReal_zero_one x)
    ((integrable_gaussianPDFReal_mul hI_xg).neg.congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply, Pi.neg_apply]
      ring))
    ((integrable_gaussianPDFReal_mul hI_g').congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      ring))
    ((integrable_gaussianPDFReal_mul hI_g).congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      ring))
  calc ∫ x, gaussianPDFReal 0 1 x * (x * g x)
      = -∫ x, g x * -(x * gaussianPDFReal 0 1 x) := by
        rw [← integral_neg]
        congr 1
        ext x
        ring
    _ = ∫ x, gaussianPDFReal 0 1 x * g' x := by
        rw [key, neg_neg]
        congr 1
        ext x
        ring

/--
The standard Euclidean Gaussian measure is centered: its mean is `0`.
-/
lemma standardGaussianMeasureOnEuclidean_integral_id {ι : Type*} [Fintype ι] :
    (standardGaussianMeasureOnEuclidean ι)[id] = (0 : EuclideanSpace ℝ ι) := by
  rw [standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
  exact integral_id_stdGaussian

/-- `exp (c ∑ⱼ |yⱼ|)` is integrable against the product standard Gaussian. -/
lemma integrable_exp_c_sum_abs_pi {ι : Type*} [Fintype ι] (c : ℝ) :
    Integrable (fun y : ι → ℝ => Real.exp (c * ∑ j, |y j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have : (fun y : ι → ℝ => Real.exp (c * ∑ j, |y j|))
      = (fun y : ι → ℝ => ∏ j, Real.exp (c * |y j|)) := by
    funext y
    rw [← Real.exp_sum, Finset.mul_sum]
  rw [this]
  exact Integrable.fintype_prod (fun j => integrable_exp_abs_gaussianReal c)

/--
`|yᵢ| exp (c ∑ⱼ |yⱼ|)` is integrable against the product standard Gaussian.
-/
lemma integrable_abs_coord_mul_exp_c_sum_abs_pi {ι : Type*} [Fintype ι]
    (c : ℝ) (i : ι) :
    Integrable (fun y : ι → ℝ => |y i| * Real.exp (c * ∑ j, |y j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine (integrable_exp_c_sum_abs_pi (|c| + 1)).mono' (by fun_prop) ?_
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (by positivity)]
  have hsum : |y i| ≤ ∑ j, |y j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i)
  have hsum_nonneg : 0 ≤ ∑ j, |y j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (y j))
  calc
    |y i| * Real.exp (c * ∑ j, |y j|) ≤
        Real.exp |y i| * Real.exp (c * ∑ j, |y j|) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp |y i|])
        (Real.exp_nonneg _)
    _ = Real.exp (|y i| + c * ∑ j, |y j|) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((|c| + 1) * ∑ j, |y j|) := by
      apply Real.exp_le_exp.mpr
      have hc := mul_le_mul_of_nonneg_right (le_abs_self c) hsum_nonneg
      nlinarith

/-- Fubini along the coordinate `i` of the product standard Gaussian: integrate the `i`-th
coordinate first, with the other coordinates fixed. -/
private lemma integral_pi_eq_integral_slice {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    {F : (ι → ℝ) → ℝ} (hF : Integrable F (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ y, F y ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ y : {j // ¬j = i} → ℝ, ∫ x : ℝ, F (fun j => if h : j = i then x else y ⟨j, h⟩)
        ∂(gaussianReal 0 1) ∂(Measure.pi fun _ : {j // ¬j = i} => gaussianReal 0 1) := by
  -- Split off the coordinate `i` with `piEquivPiSubtypeProd`; the factor indexed by
  -- `{j // j = i}` is identified with `ℝ` by `piUnique`.
  let e : ℝ × ({j // ¬j = i} → ℝ) ≃ᵐ (ι → ℝ) :=
    ((MeasurableEquiv.piUnique (fun _ : {j // j = i} => ℝ)).symm.prodCongr
      (MeasurableEquiv.refl _)).trans
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· = i)).symm
  have he : MeasurePreserving e
      ((gaussianReal 0 1).prod (Measure.pi fun _ : {j // ¬j = i} => gaussianReal 0 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    have h1 := ((measurePreserving_piUnique (fun _ : {j // j = i} => gaussianReal 0 1)).symm _).prod
      (MeasurePreserving.id (Measure.pi fun _ : {j // ¬j = i} => gaussianReal 0 1))
    have h2 :=
      (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (· = i)).symm _
    -- `convert` identifies the two `Fintype` instances on `{j // j = i}`.
    exact h2.comp (by
      convert h1
      rfl)
  have happly : ∀ p : ℝ × ({j // ¬j = i} → ℝ),
      e p = fun j => if h : j = i then p.1 else p.2 ⟨j, h⟩ := by
    intro p
    funext j
    change (Equiv.piEquivPiSubtypeProd (· = i) (fun _ => ℝ)).symm
      (uniqueElim p.1, p.2) j = _
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    split_ifs with h
    · simp
    · rfl
  rw [← he.integral_comp' F]
  have hFe : Integrable (F ∘ e) _ := (he.integrable_comp_emb e.measurableEmbedding).2 hF
  rw [integral_prod_symm (fun z => F (e z)) hFe]
  simp only [happly]

/--
**Tensorized Stein identity on the product Gaussian measure.**  For a `C¹` function `h`
on `ι → ℝ` whose value and selected coordinate derivative have exponential growth
`C e^{c ∑ⱼ |yⱼ|}`, integration against the product of standard Gaussians satisfies
`∫ yᵢ h y = ∫ ∂ᵢ h y`.  This is Fubini over the `i`-th coordinate combined with the
one-dimensional Stein identity `gaussianReal_stein`.
-/
lemma pi_gaussian_stein_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : (ι → ℝ) → ℝ) (i : ι)
    (hh : ContDiff ℝ 1 h) (C c : ℝ)
    (hhb : ∀ y, |h y| ≤ C * Real.exp (c * ∑ j, |y j|))
    (hdb : ∀ y,
      |fderiv ℝ h y (Pi.single i 1)| ≤ C * Real.exp (c * ∑ k, |y k|)) :
    ∫ y, y i * h y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      = ∫ y, fderiv ℝ h y (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h_integrable : MeasureTheory.Integrable (fun y : ι → ℝ => y i * h y) (Measure.pi fun _ : ι =>
    gaussianReal 0 1) ∧ MeasureTheory.Integrable (fun y : ι → ℝ => (fderiv ℝ h y) (Pi.single i 1))
    (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    constructor
    · refine MeasureTheory.Integrable.mono' (g := fun y => C * |y i| * Real.exp (c * ∑ j,
        |y j|)) ?_ ?_ ?_
      · convert (integrable_abs_coord_mul_exp_c_sum_abs_pi c i).const_mul C using 2
        ring
      · exact MeasureTheory.AEStronglyMeasurable.mul (measurable_pi_apply i |>
          Measurable.aestronglyMeasurable) (hh.continuous.aestronglyMeasurable)
      · filter_upwards [] with y
        rw [Real.norm_eq_abs, abs_mul]
        simpa only [mul_assoc, mul_left_comm] using
          mul_le_mul_of_nonneg_left (hhb y) (abs_nonneg (y i))
    · refine MeasureTheory.Integrable.mono' (g := fun y => C * Real.exp (c * ∑ j,
        |y j|)) ?_ ?_ ?_
      · exact MeasureTheory.Integrable.const_mul (integrable_exp_c_sum_abs_pi c) _
      · fun_prop
      · exact Filter.Eventually.of_forall hdb
  have h_slice : ∀ y : {j // ¬j = i} → ℝ,
      ∫ x : ℝ, x * h (fun j => if hj : j = i then x else y ⟨j, hj⟩) ∂(gaussianReal 0 1) =
        ∫ x : ℝ, fderiv ℝ h (fun j => if hj : j = i then x else y ⟨j, hj⟩) (Pi.single i 1)
          ∂(gaussianReal 0 1) := by
    intro y
    set Yb : ι → ℝ := fun j => if hj : j = i then 0 else y ⟨j, hj⟩
    have h_Yb : ∀ x, (fun j => if hj : j = i then x else y ⟨j, hj⟩) = Function.update Yb i x := by
      intro x
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Yb, hj]
    simp only [h_Yb]
    have h_G : ∀ x, HasDerivAt (fun t => h (Function.update Yb i t)) ((fderiv ℝ h (Function.update
      Yb i x)) (Pi.single i 1)) x := by
      intro x
      have h_chain : HasDerivAt (fun t => h (Function.update Yb i t)) ((fderiv ℝ h (Function.update
        Yb i x)) (Pi.single i 1)) x := by
        have h_update : HasDerivAt (fun t => Function.update Yb i t) (Pi.single i 1) x :=
          hasDerivAt_update Yb i x
        convert HasFDerivAt.comp_hasDerivAt x
          (hh.contDiffAt.differentiableAt (by norm_num) |> DifferentiableAt.hasFDerivAt)
          h_update using 1 <;> rfl
      exact h_chain
    have h_G_bound : ∀ x, |h (Function.update Yb i x)| ≤ C * Real.exp (c * (|x| + ∑ j,
      |y j|)) ∧ |(fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)| ≤ C * Real.exp (c * (|x| + ∑
      j, |y j|)) := by
      intro x
      have h_sum : ∑ j, |(Function.update Yb i x) j| = |x| + ∑ j, |y j| := by
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
        refine congr_arg₂ (· + ·) ?_ ?_
        · simp
        · refine Finset.sum_bij (fun j hj => ⟨j, by simpa using hj⟩) ?_ ?_ ?_ ?_ <;>
            simp [Function.update_apply]
          simp +contextual [Yb]
      exact ⟨by simpa only [h_sum] using hhb (Function.update Yb i x),
        by simpa only [h_sum] using hdb (Function.update Yb i x)⟩
    have := @gaussianReal_stein
    convert this (fun x => h (Function.update Yb i x)) (fun x => (fderiv ℝ h (Function.update
      Yb i x)) (Pi.single i 1)) h_G _ (C * Real.exp (c * ∑ j, |y j|)) c _ _ using 1
    · fun_prop
    · intro x
      convert (h_G_bound x).1 using 1
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    · intro x
      have hb := (h_G_bound x).2
      rw [mul_assoc, ← Real.exp_add]
      ring_nf at hb ⊢
      exact hb
  rw [integral_pi_eq_integral_slice i h_integrable.1,
    integral_pi_eq_integral_slice i h_integrable.2]
  congr 1
  funext y
  simpa using h_slice y

/--
Transferring the `i`-th gradient coordinate through the `toLp` identification: it becomes
the `i`-th partial derivative of the composed function on `ι → ℝ`.
-/
lemma gradient_toLp_coord_eq_fderiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : EuclideanSpace ℝ ι → ℝ) (hg : Differentiable ℝ g) (y : ι → ℝ) (i : ι) :
    (gradient g (WithLp.toLp 2 y)) i
      = fderiv ℝ (fun z => g (WithLp.toLp 2 z)) y (Pi.single i 1) := by
  rw [gradient]
  rw [show (fun z => g (WithLp.toLp 2 z)) = g ∘ (WithLp.toLp 2) from rfl,
    fderiv_comp] <;> norm_num [hg.differentiableAt, WithLp.ofLp]
  · rw [fderiv]
    rw [fderiv]
    rw [fderivWithin_univ, fderivWithin_univ, show (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ
      ι) = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm from rfl,
      ContinuousLinearEquiv.fderiv]
    norm_num
    rw [← InnerProductSpace.toDual_symm_apply]
    rw [EuclideanSpace.inner_single_right]
    norm_num
  · refine ⟨?_, hasFDerivAt_iff_tendsto.mpr ?_⟩
    · exact (ContinuousLinearEquiv.toContinuousLinearMap (ContinuousLinearEquiv.symm
        (EuclideanSpace.equiv ι ℝ)))
    · simp

/--
The functions w ↦ w_i · g(w) and w ↦ (∇g(w))_i are integrable against the
standard Gaussian when the value and gradient of g have exponential growth.
-/
lemma gaussian_ibp_integrable {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ ι → ℝ)
    (i : ι) (hg : ContDiff ℝ 1 g)
    (C c : ℝ) (hgb : ∀ w, |g w| ≤ C * Real.exp (c * ‖w‖))
    (hgradb : ∀ w, ‖gradient g w‖ ≤ C * Real.exp (c * ‖w‖)) :
    Integrable (fun w => w i * g w) (standardGaussianMeasureOnEuclidean ι)
      ∧ Integrable (fun w => (gradient g w) i) (standardGaussianMeasureOnEuclidean ι) := by
  have hcoord (w : EuclideanSpace ℝ ι) : ‖w i‖ ≤ ‖w‖ := PiLp.norm_apply_le w i
  constructor
  · have hmeas : AEStronglyMeasurable (fun w => w i * g w)
        (standardGaussianMeasureOnEuclidean ι) :=
      (by fun_prop : Continuous (fun w : EuclideanSpace ℝ ι => w i)).aestronglyMeasurable.mul
        hg.continuous.aestronglyMeasurable
    refine ((integrable_exp_mul_norm (c + 1)).const_mul |C|).mono' hmeas ?_
    filter_upwards [] with w
    have hgrowth : ‖g w‖ ≤ |C| * Real.exp (c * ‖w‖) := by
      rw [Real.norm_eq_abs]
      exact (hgb w).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _))
    have hnorm_exp : ‖w‖ ≤ Real.exp ‖w‖ := by
      linarith [Real.add_one_le_exp ‖w‖]
    calc
      ‖w i * g w‖ = ‖w i‖ * ‖g w‖ := norm_mul _ _
      _ ≤ ‖w‖ * (|C| * Real.exp (c * ‖w‖)) :=
        mul_le_mul (hcoord w) hgrowth (norm_nonneg _) (norm_nonneg _)
      _ ≤ Real.exp ‖w‖ * (|C| * Real.exp (c * ‖w‖)) :=
        mul_le_mul_of_nonneg_right hnorm_exp (by positivity)
      _ = |C| * Real.exp ((c + 1) * ‖w‖) := by
        rw [add_mul, one_mul, Real.exp_add]
        ring
  · have hgrad_cont : Continuous (gradient g) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
        (hg.continuous_fderiv one_ne_zero)
    refine ((integrable_exp_mul_norm c).const_mul C).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun w =>
      (PiLp.norm_apply_le (gradient g w) i).trans (hgradb w)

end SYK.GaussianConcentration
