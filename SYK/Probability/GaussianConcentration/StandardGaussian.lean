import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The standard Gaussian on a finite coordinate space

For any finite index type `ι`, `standardGaussianMeasureOnEuclidean ι` is the product
of standard one-dimensional Gaussians transported to `EuclideanSpace ℝ ι`. The file
proves that it is a Gaussian probability measure and the integrability of
exponential-growth functions against it, the Herbst-type step from a covariance bound
to an exponential-moment bound (`herbst_of_cov_bound`), and Stein's identity: in one
dimension (`gaussianReal_stein`) and coordinatewise on the product measure
(`pi_gaussian_stein_coord`). It is independent of the SYK model.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK.GaussianConcentration

/-- One standard Gaussian measure for every finite Euclidean coordinate type.
This is the product of standard one-dimensional Gaussians pushed forward to the
Euclidean (`L²`) structure on the coordinate space. -/
noncomputable def standardGaussianMeasureOnEuclidean
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
  classical
  have hindep : iIndepFun (fun (i : ι) (ω : ι → ℝ) => ω i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    have := iIndepFun_pi (X := fun (_ : ι) (x : ℝ) => x)
      (μ := fun _ : ι => gaussianReal 0 1) (fun _ => measurable_id.aemeasurable)
    simpa using this
  have hlaw : ∀ i : ι, HasGaussianLaw (fun ω : ι → ℝ => ω i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    intro i
    have h0 : (Measure.pi fun _ : ι => gaussianReal 0 1).map (Function.eval i)
        = gaussianReal 0 1 := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq
    have : IsGaussian ((Measure.pi fun _ : ι => gaussianReal 0 1).map (fun ω => ω i)) := by
      rw [show (fun ω : ι → ℝ => ω i) = Function.eval i from rfl, h0]; infer_instance
    exact IsGaussian.hasGaussianLaw
  have h2 : IsGaussian ((Measure.pi fun _ : ι => gaussianReal 0 1).map (fun ω i => ω i)) :=
    (hindep.hasGaussianLaw hlaw).isGaussian_map
  simpa using h2

/-- The standard Euclidean Gaussian measure is a Gaussian measure. -/
instance standardGaussianMeasureOnEuclidean_isGaussian {ι : Type*} [Fintype ι] :
    IsGaussian (standardGaussianMeasureOnEuclidean ι) := by
  unfold standardGaussianMeasureOnEuclidean
  rw [show (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm from rfl]
  infer_instance

/-
Analytic proof outline for the Gaussian concentration estimate.

The standard Gaussian log-Sobolev inequality says that, for locally Lipschitz
$g : \mathbb R^n \to \mathbb R$ with $e^g \in L^1(\gamma_n)$,
$\operatorname{Ent}_{\gamma_n}(e^g) \le
  \frac12 \int |\nabla g|^2 e^g \, d\gamma_n$, where
$\operatorname{Ent}_{\gamma_n}(H) =
  \int H \log H \, d\gamma_n -
  (\int H \, d\gamma_n)\log(\int H \, d\gamma_n)$.
Here $\nabla g$ is the a.e. gradient.

If $F$ is $L$-Lipschitz, Rademacher's theorem gives
$|\nabla F(x)| \le L$ for a.e. $x$. Also
$|F(x)| \le |F(0)| + L|x|$, so $e^{\lambda F} \in L^1(\gamma_n)$
for every $\lambda \in \mathbb R$. Set
$\Phi(\lambda) = \log \mathbb E e^{\lambda F(X)}$.

For $\lambda > 0$, applying log-Sobolev to $g = \lambda F$ gives
$\operatorname{Ent}_{\gamma_n}(e^{\lambda F})
  \le \frac{\lambda^2 L^2}{2}\mathbb E e^{\lambda F(X)}$.
Since
$\Phi'(\lambda) =
  \mathbb E[F(X)e^{\lambda F(X)}] / \mathbb E e^{\lambda F(X)}$,
the entropy identity is
$\operatorname{Ent}_{\gamma_n}(e^{\lambda F}) =
  \mathbb E e^{\lambda F(X)}(\lambda\Phi'(\lambda)-\Phi(\lambda))$.
Thus
$\lambda\Phi'(\lambda)-\Phi(\lambda) \le \lambda^2L^2/2$, hence
$(\Phi(\lambda)/\lambda)' \le L^2/2$.

Integrating from $0$ to $\lambda$ and using
$\lim_{s \downarrow 0}\Phi(s)/s = \mathbb E F(X)$ yields
$\Phi(\lambda) \le \lambda\mathbb E F(X) + \lambda^2L^2/2$, equivalently
$\mathbb E e^{\lambda(F(X)-\mathbb E F(X))} \le e^{\lambda^2L^2/2}$.
Chernoff's bound then gives
$\mathbb P(F(X)-\mathbb E F(X) > t)
  \le \exp(-\lambda t + \lambda^2L^2/2)$, optimized at
$\lambda = t/L^2$, so
$\mathbb P(F(X)-\mathbb E F(X) > t)
  \le \exp(-t^2/(2L^2))$.
Applying the same argument to $-F$ and using the union bound gives
$\mathbb P(|F(X)-\mathbb E F(X)| > t)
  \le 2\exp(-t^2/(2L^2))$.

Exponential-of-norm functions are integrable against the standard Euclidean Gaussian.
This follows from the fact that a standard Gaussian has finite exponential moments of its
Euclidean norm.
-/
theorem integrable_exp_mul_norm {ι : Type*} [Fintype ι] (c : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (c * ‖x‖))
      (standardGaussianMeasureOnEuclidean ι) := by
  unfold standardGaussianMeasureOnEuclidean;
  rw [ MeasureTheory.integrable_map_measure ];
  · refine MeasureTheory.Integrable.mono' (g := fun x => ∏ i, Real.exp ( |c| * |x i| )) ?_ ?_ ?_;
    · have h_integrable : ∀ i : ι, MeasureTheory.Integrable (fun x : ℝ => Real.exp (|c| * |x|))
        (gaussianReal 0 1) := by
        intro i
        have h_integrable : MeasureTheory.Integrable (fun x : ℝ => Real.exp (|c| * |x|))
          (gaussianReal 0 1) := by
          have h_mgf : ∀ s : ℝ, MeasureTheory.Integrable (fun x : ℝ => Real.exp (s * x))
            (gaussianReal 0 1) := by
            intro s
            have h_integrable : ∫ x, Real.exp (s * x) ∂(gaussianReal 0 1) = Real.exp (s^2 / 2) := by
              have := @ProbabilityTheory.mgf_gaussianReal;
              convert @this ℝ _ ( gaussianReal 0 1 ) 0 1 ( fun x => x ) _ s using 1 <;>
                norm_num [mgf, mul_comm]
            exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ;
                        positivity )
          refine MeasureTheory.Integrable.mono' ( h_mgf |c| |> fun h => h.add ( h_mgf ( -|c| ) ) )
            ?_ ?_;
          · exact Continuous.aestronglyMeasurable ( by continuity );
          · filter_upwards [ ] with x using by
              norm_num
              cases abs_cases x <;> simp only [mul_neg, le_add_iff_nonneg_left,
                le_add_iff_nonneg_right, *] <;> positivity
        exact h_integrable;
      have h_prod_integrable : ∀ {f : ι → ℝ → ℝ}, (∀ i,
        MeasureTheory.Integrable (fun x => f i x) (gaussianReal 0 1)) → MeasureTheory.Integrable
        (fun x : ι → ℝ => ∏ i, f i (x i)) (Measure.pi fun _ => gaussianReal 0 1) := by
        exact fun {f} a => Integrable.fintype_prod a;
      exact h_prod_integrable h_integrable;
    · fun_prop (disch := norm_num);
    · simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Function.comp_apply,
        Real.abs_exp, ← Real.exp_sum, Real.exp_le_exp];
      refine Filter.Eventually.of_forall fun x => ?_;
      -- Apply the triangle inequality to the sum.
      have h_triangle : Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := by
        exact Real.sqrt_le_iff.mpr
          ⟨ by
            exact Finset.sum_nonneg fun _ _ => abs_nonneg _ , by
              simpa [ sq, Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun i ( hi : i ∈
                Finset.univ ) => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun i _ =>
                abs_nonneg ( x i ) ) hi ) ( abs_nonneg ( x i ) ) ⟩;
      rw [ ← Finset.mul_sum _ _ _ ];
      cases abs_cases c <;> nlinarith [ Real.sqrt_nonneg ( ∑ i, x i ^ 2 ) ];
  · fun_prop;
  · fun_prop

/-
Real-analysis Grönwall-type core of the Herbst argument.  If `Φ` is differentiable,
vanishes at `0`, and its derivative stays within `c * |s|` of `m` for every `s`, then `Φ`
is dominated by the quadratic `m * t + c * t ^ 2 / 2`.  (The two-sided derivative bound
forces `Φ' - m` to have the sign of `s` at the endpoints, which is exactly what is needed
for both `t ≥ 0` and `t ≤ 0`.)
-/
lemma quadratic_bound_of_deriv_sub_le {Φ : ℝ → ℝ} {m c : ℝ}
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

/-
For a Lipschitz function `F`, the function `exp (s • F)` is integrable against the
standard Gaussian measure, for every real `s`.  This uses the linear growth
`|F x| ≤ |F 0| + L * ‖x‖` together with `integrable_exp_mul_norm`.
-/
lemma integrable_exp_smul_lipschitz {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (s : ℝ) :
    Integrable (fun x => Real.exp (s * F x)) (standardGaussianMeasureOnEuclidean ι) := by
  refine MeasureTheory.Integrable.mono' (g := fun x => Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L
    * ‖x‖ )) ?_ ?_ ?_;
  · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm ( |s| * L ) ) _;
  · exact Continuous.aestronglyMeasurable ( by exact Real.continuous_exp.comp ( continuous_const.mul
                                                ( hLip.continuous ) ) );
  · -- Apply the Lipschitz condition to bound |F x|.
    have h_bound : ∀ x, |F x - F 0| ≤ L * ‖x‖ := by
      intro x
      have hx := hLip.dist_le_mul x 0
      rw [show (L.toNNReal : ℝ) = L by exact Real.coe_toNNReal L hL.le] at hx
      simpa only [Real.dist_eq, dist_zero_right] using hx
    simp only [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add, Real.exp_le_exp];
    filter_upwards [ ] with x using by cases abs_cases s <;> cases abs_cases ( F 0 ) <;> nlinarith
                                        [ abs_le.mp ( h_bound x ) ] ;

/-- The set of exponents `s` for which `exp (s • F)` is integrable is all of `ℝ`. -/
lemma integrableExpSet_lipschitz_eq_univ {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) :
    integrableExpSet F (standardGaussianMeasureOnEuclidean ι) = Set.univ := by
  ext s
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact integrable_exp_smul_lipschitz F L hL hLip s

/-
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
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
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
    ι);
  -- We need to show that $\Phi(t) \leq mt + L^2 t^2 / 2$.
  have hΦ : Φ t ≤ (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι) * t + L^2 * t^2 / 2 := by
    apply quadratic_bound_of_deriv_sub_le;
    · have h_analytic : ∀ s : ℝ, AnalyticAt ℝ Φ s := by
        intro s;
        apply_rules [ ProbabilityTheory.analyticAt_cgf ];
        rw [ integrableExpSet_lipschitz_eq_univ F L hL hLip ] ; norm_num;
      exact fun s => ( h_analytic s |> AnalyticAt.differentiableAt );
    · simp +zetaDelta at *;
    · intro s
      have h_deriv : deriv Φ s = (∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean
        ι) / (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
        apply_rules [ ProbabilityTheory.deriv_cgf ];
        rw [ integrableExpSet_lipschitz_eq_univ F L hL hLip ] ; norm_num;
      rw [ h_deriv, div_sub' ];
      · rw [ abs_div, abs_of_nonneg ( show 0 ≤ ∫ x, Real.exp ( s * F x )
          ∂standardGaussianMeasureOnEuclidean ι from MeasureTheory.integral_nonneg fun _ =>
          Real.exp_nonneg _ ) ];
        exact div_le_of_le_mul₀ ( MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ )
          ( by positivity ) ( by simpa only [ mul_comm ] using hcov s );
      · refine ne_of_gt ( ?_ );
        rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
        · simp [ Function.support, Real.exp_ne_zero ];
        · exact Filter.Eventually.of_forall fun x => Real.exp_nonneg _;
        · exact integrable_exp_smul_lipschitz F L hL hLip s;
  convert Real.exp_le_exp.mpr ( show Φ t - ( ∫ x, F x ∂standardGaussianMeasureOnEuclidean ι ) * t ≤
    L ^ 2 * t ^ 2 / 2 from by linarith ) using 1;
  rw [ Real.exp_sub, Real.exp_log ];
  · simp only [mgf, mul_sub, Real.exp_sub];
    rw [ MeasureTheory.integral_div, mul_comm ];
  · apply_rules [ ProbabilityTheory.mgf_pos ];
    exact integrable_exp_smul_lipschitz F L hL hLip t

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
    ((hasDerivAt_pow 2 x).neg.div_const 2).congr_deriv (by norm_num; ring)
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

/-
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
      _ = C * Real.exp ((c + 1) * |x|) := by rw [add_mul, one_mul, Real.exp_add]; ring
  -- Write both sides as Lebesgue integrals against the density `φ` and integrate by parts
  -- with `u = g` and `v = φ`, using `φ' = -x φ`.
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := gaussianPDFReal 0 1) (u' := g') (v' := fun x => -(x * gaussianPDFReal 0 1 x))
    (fun x _ => hg x) (fun x _ => hasDerivAt_gaussianPDFReal_zero_one x)
    ((integrable_gaussianPDFReal_mul hI_xg).neg.congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply, Pi.neg_apply]; ring))
    ((integrable_gaussianPDFReal_mul hI_g').congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply]; ring))
    ((integrable_gaussianPDFReal_mul hI_g).congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply]; ring))
  calc ∫ x, gaussianPDFReal 0 1 x * (x * g x)
      = -∫ x, g x * -(x * gaussianPDFReal 0 1 x) := by
        rw [← integral_neg]; congr 1; ext x; ring
    _ = ∫ x, gaussianPDFReal 0 1 x * g' x := by
        rw [key, neg_neg]; congr 1; ext x; ring

/-
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
    funext y; rw [← Real.exp_sum, Finset.mul_sum]
  rw [this]
  exact Integrable.fintype_prod (fun j => integrable_exp_abs_gaussianReal c)

/-
`|yᵢ| exp (c ∑ⱼ |yⱼ|)` is integrable against the product standard Gaussian.
-/
lemma integrable_abs_coord_mul_exp_c_sum_abs_pi {ι : Type*} [Fintype ι]
    (c : ℝ) (i : ι) :
    Integrable (fun y : ι → ℝ => |y i| * Real.exp (c * ∑ j, |y j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine MeasureTheory.Integrable.mono' (g := fun y => Real.exp ( ( |c| + 1 ) * ∑ j,
    |y j| )) ?_ ?_ ?_;
  · convert integrable_exp_c_sum_abs_pi ( |c| + 1 ) using 1;
  · fun_prop;
  · filter_upwards [ ] with y using
      by
        rw [ Real.norm_of_nonneg ( by positivity ) ]
        exact le_trans ( mul_le_mul_of_nonneg_right ( show |y i| ≤ Real.exp |y i| by
          linarith [ Real.add_one_le_exp |y i| ] ) ( Real.exp_nonneg _ ) ) ( by
            rw [ ← Real.exp_add ]
            exact Real.exp_le_exp.mpr ( by
              cases abs_cases c <;> cases abs_cases ( y i ) <;> nlinarith [ Real.exp_pos |y i|,
                Finset.single_le_sum ( fun a _ => abs_nonneg ( y a ) ) ( Finset.mem_univ i ) ] ) )

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
    exact h2.comp (by convert h1; rfl)
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

/-
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
    constructor;
    · refine MeasureTheory.Integrable.mono' (g := fun y => C * |y i| * Real.exp ( c * ∑ j,
        |y j| )) ?_ ?_ ?_;
      · convert integrable_abs_coord_mul_exp_c_sum_abs_pi c i |> fun h => h.const_mul C using 2 ;
          ring;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply i |>
          Measurable.aestronglyMeasurable ) ( hh.continuous.aestronglyMeasurable );
      · filter_upwards [ ] with y using by rw [ Real.norm_eq_abs, abs_mul ] ; nlinarith [ hhb y,
                                            abs_nonneg ( y i ) ] ;
    · refine MeasureTheory.Integrable.mono' (g := fun y => C * Real.exp ( c * ∑ j,
        |y j| )) ?_ ?_ ?_;
      · exact MeasureTheory.Integrable.const_mul ( integrable_exp_c_sum_abs_pi c ) _;
      · fun_prop;
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
      exact h_chain;
    have h_G_bound : ∀ x, |h (Function.update Yb i x)| ≤ C * Real.exp (c * (|x| + ∑ j,
      |y j|)) ∧ |(fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)| ≤ C * Real.exp (c * (|x| + ∑
      j, |y j|)) := by
      intro x
      have h_sum : ∑ j, |(Function.update Yb i x) j| = |x| + ∑ j, |y j| := by
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)];
        refine congr_arg₂ ( · + · ) ?_ ?_;
        · simp;
        · refine Finset.sum_bij ( fun j hj => ⟨ j, by simpa using hj ⟩ ) ?_ ?_ ?_ ?_ <;>
            simp [ Function.update_apply ]
          simp +contextual [Yb]
      exact ⟨by simpa only [h_sum] using hhb (Function.update Yb i x),
        by simpa only [h_sum] using hdb (Function.update Yb i x)⟩
    have := @gaussianReal_stein;
    convert this ( fun x => h ( Function.update Yb i x ) ) ( fun x => ( fderiv ℝ h ( Function.update
      Yb i x ) ) ( Pi.single i 1 ) ) h_G _ ( C * Real.exp ( c * ∑ j, |y j| ) ) c _ _ using 1;
    · fun_prop;
    · intro x; convert h_G_bound x |>.1 using 1; rw [ mul_assoc, ← Real.exp_add ] ; ring_nf;
    · intro x; specialize h_G_bound x; rw [ mul_assoc, ← Real.exp_add ] ; ring_nf at *;
        exact h_G_bound.2
  rw [integral_pi_eq_integral_slice i h_integrable.1,
    integral_pi_eq_integral_slice i h_integrable.2]
  congr 1
  funext y
  simpa using h_slice y

/-
Transferring the `i`-th gradient coordinate through the `toLp` identification: it becomes
the `i`-th partial derivative of the composed function on `ι → ℝ`.
-/
lemma gradient_toLp_coord_eq_fderiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : EuclideanSpace ℝ ι → ℝ) (hg : Differentiable ℝ g) (y : ι → ℝ) (i : ι) :
    (gradient g (WithLp.toLp 2 y)) i
      = fderiv ℝ (fun z => g (WithLp.toLp 2 z)) y (Pi.single i 1) := by
  rw [ gradient ];
  rw [ show ( fun z => g ( WithLp.toLp 2 z ) ) = g ∘ ( WithLp.toLp 2 ) from rfl,
    fderiv_comp ] <;> norm_num [ hg.differentiableAt, WithLp.ofLp ];
  · rw [ fderiv ];
    rw [ fderiv ];
    rw [ fderivWithin_univ, fderivWithin_univ, show ( WithLp.toLp 2 : ( ι → ℝ ) → EuclideanSpace ℝ
      ι ) = ( PiLp.continuousLinearEquiv 2 ℝ ( fun _ : ι => ℝ ) ).symm from rfl,
      ContinuousLinearEquiv.fderiv ] ; norm_num;
    rw [ ← InnerProductSpace.toDual_symm_apply ];
    rw [ EuclideanSpace.inner_single_right ] ; norm_num;
  · refine ⟨ ?_, hasFDerivAt_iff_tendsto.mpr ?_ ⟩
    · exact ( ContinuousLinearEquiv.toContinuousLinearMap ( ContinuousLinearEquiv.symm
        ( EuclideanSpace.equiv ι ℝ ) ) )
    · simp

/-
The value and gradient of `g` are integrable against the standard Gaussian when they have
exponential growth.
-/
lemma gaussian_ibp_integrable {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ ι → ℝ)
    (i : ι) (hg : ContDiff ℝ 1 g)
    (C c : ℝ) (hgb : ∀ w, |g w| ≤ C * Real.exp (c * ‖w‖))
    (hgradb : ∀ w, ‖gradient g w‖ ≤ C * Real.exp (c * ‖w‖)) :
    Integrable (fun w => w i * g w) (standardGaussianMeasureOnEuclidean ι)
      ∧ Integrable (fun w => (gradient g w) i) (standardGaussianMeasureOnEuclidean ι) := by
  constructor;
  · refine MeasureTheory.Integrable.mono' (g := fun w => |C| * Real.exp ( ( c + 1 ) * ‖w‖ )) ?_ ?_
      ?_;
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm ( c + 1 ) ) _;
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_ ( hg.continuous.aestronglyMeasurable );
      fun_prop;
    · refine Filter.Eventually.of_forall fun w => ?_;
      refine le_trans ( norm_mul_le _ _ ) ?_;
      refine le_trans ( mul_le_mul_of_nonneg_right ( show ‖w.ofLp i‖ ≤ ‖w‖ from ?_ )
        ( norm_nonneg _ ) ) ?_;
      · simp only [Real.norm_eq_abs, EuclideanSpace.norm_eq, sq_abs];
        exact Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( w.ofLp i ) )
          ( Finset.mem_univ i ) );
      · refine le_trans ( mul_le_mul_of_nonneg_left ( hgb w ) ( norm_nonneg _ ) ) ?_;
        rw [ add_mul, one_mul, Real.exp_add ];
        cases abs_cases C <;> nlinarith [ show 0 ≤ Real.exp ( c * ‖w‖ ) * Real.exp ‖w‖
          by
            positivity, show ‖w‖ ≤ Real.exp ‖w‖ by
              exact le_trans ( by
                norm_num ) ( Real.add_one_le_exp _ ), show 0 ≤ C * Real.exp ( c * ‖w‖ ) by
                  exact le_trans ( abs_nonneg _ ) ( hgb w ) ];
  · refine MeasureTheory.Integrable.mono' (g := fun w => C * Real.exp ( c * ‖w‖ )) ?_ ?_ ?_;
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm c ) _;
    · have h_grad_cont : Continuous (gradient g) := by
        have := hg.continuous_fderiv;
        exact Continuous.comp ( LinearIsometryEquiv.continuous _ ) ( this one_ne_zero );
      fun_prop;
    · refine Filter.Eventually.of_forall fun w => le_trans ?_ ( hgradb w );
      simp only [Real.norm_eq_abs, EuclideanSpace.norm_eq, sq_abs];
      exact Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( ( gradient g w ).ofLp
        i ) ) ( Finset.mem_univ i ) )

end SYK.GaussianConcentration
