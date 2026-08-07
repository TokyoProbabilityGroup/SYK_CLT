import Mathlib

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK

/-- The Euclidean space of real SYK couplings. -/
abbrev CouplingSpace (N q : ℕ) :=
  EuclideanSpace ℝ ({s : Finset (Fin N) // s.card = q})

@[simp]
theorem couplingSpace_card (N q : ℕ) :
    Fintype.card ({s : Finset (Fin N) // s.card = q}) = Nat.choose N q := by
  simp

/-- The product standard Gaussian measure transported to coupling space. -/
noncomputable def standardGaussianMeasure (N q : ℕ) :
    Measure (CouplingSpace N q) :=
  (Measure.pi fun _ : ({s : Finset (Fin N) // s.card = q}) => gaussianReal 0 1).map
    (WithLp.toLp 2)

/-- One standard Gaussian measure for every finite Euclidean coordinate type.
This is the product of standard one-dimensional Gaussians pushed forward to the
Euclidean (`L²`) structure on the coordinate space. -/
noncomputable def standardGaussianMeasureOnEuclidean
    (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2)

/-- The SYK coupling-space measure is the standard Euclidean Gaussian on the
interaction-index type. -/
@[simp]
theorem standardGaussianMeasure_eq_onEuclidean (N q : ℕ) :
    standardGaussianMeasure N q =
      standardGaussianMeasureOnEuclidean ({s : Finset (Fin N) // s.card = q}) := rfl

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
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => ∏ i, Real.exp ( |c| * |x i| );
    · have h_integrable : ∀ i : ι, MeasureTheory.Integrable (fun x : ℝ => Real.exp (|c| * |x|)) (gaussianReal 0 1) := by
        intro i
        have h_integrable : MeasureTheory.Integrable (fun x : ℝ => Real.exp (|c| * |x|)) (gaussianReal 0 1) := by
          have h_mgf : ∀ s : ℝ, MeasureTheory.Integrable (fun x : ℝ => Real.exp (s * x)) (gaussianReal 0 1) := by
            intro s
            have h_integrable : ∫ x, Real.exp (s * x) ∂(gaussianReal 0 1) = Real.exp (s^2 / 2) := by
              have := @ProbabilityTheory.mgf_gaussianReal;
              convert @this ℝ _ ( gaussianReal 0 1 ) 0 1 ( fun x => x ) _ s using 1 <;>
                norm_num [mgf, mul_comm]
            exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity )
          refine' MeasureTheory.Integrable.mono' ( h_mgf |c| |> fun h => h.add ( h_mgf ( -|c| ) ) ) _ _;
          · exact Continuous.aestronglyMeasurable ( by continuity );
          · filter_upwards [ ] with x using by norm_num; cases abs_cases x <;> simp +decide [ * ] <;> positivity;
        exact h_integrable;
      have h_prod_integrable : ∀ {f : ι → ℝ → ℝ}, (∀ i, MeasureTheory.Integrable (fun x => f i x) (gaussianReal 0 1)) → MeasureTheory.Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) (Measure.pi fun _ => gaussianReal 0 1) := by
        exact fun {f} a => Integrable.fintype_prod a;
      exact h_prod_integrable h_integrable;
    · fun_prop (disch := norm_num);
    · simp +decide [ ← Real.exp_sum, EuclideanSpace.norm_eq ];
      refine' Filter.Eventually.of_forall fun x => _;
      -- Apply the triangle inequality to the sum.
      have h_triangle : Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := by
        exact Real.sqrt_le_iff.mpr ⟨ by exact Finset.sum_nonneg fun _ _ => abs_nonneg _, by simpa [ sq, Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun i _ => abs_nonneg ( x i ) ) hi ) ( abs_nonneg ( x i ) ) ⟩;
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
    simp only [id_eq, Nat.cast_ofNat, pow_one, mul_one]
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
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖x‖ );
  · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm ( |s| * L ) ) _;
  · exact Continuous.aestronglyMeasurable ( by exact Real.continuous_exp.comp ( continuous_const.mul ( hLip.continuous ) ) );
  · -- Apply the Lipschitz condition to bound |F x|.
    have h_bound : ∀ x, |F x - F 0| ≤ L * ‖x‖ := by
      intro x
      have hx := hLip.dist_le_mul x 0
      rw [show (L.toNNReal : ℝ) = L by exact Real.coe_toNNReal L hL.le] at hx
      simpa only [Real.dist_eq, dist_zero_right] using hx
    simp +decide [ ← Real.exp_add ];
    filter_upwards [ ] with x using by cases abs_cases s <;> cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp ( h_bound x ) ] ;

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
  set Φ : ℝ → ℝ := fun s => Real.log (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι);
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
      have h_deriv : deriv Φ s = (∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) / (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
        apply_rules [ ProbabilityTheory.deriv_cgf ];
        rw [ integrableExpSet_lipschitz_eq_univ F L hL hLip ] ; norm_num;
      rw [ h_deriv, div_sub' ];
      · rw [ abs_div, abs_of_nonneg ( show 0 ≤ ∫ x, Real.exp ( s * F x ) ∂standardGaussianMeasureOnEuclidean ι from MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ) ];
        exact div_le_of_le_mul₀ ( MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ) ( by positivity ) ( by simpa only [ mul_comm ] using hcov s );
      · refine' ne_of_gt ( _ );
        rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
        · simp +decide [ Function.support, Real.exp_ne_zero ];
        · exact Filter.Eventually.of_forall fun x => Real.exp_nonneg _;
        · exact integrable_exp_smul_lipschitz F L hL hLip s;
  convert Real.exp_le_exp.mpr ( show Φ t - ( ∫ x, F x ∂standardGaussianMeasureOnEuclidean ι ) * t ≤ L ^ 2 * t ^ 2 / 2 from by linarith ) using 1;
  rw [ Real.exp_sub, Real.exp_log ];
  · simp +decide [ mgf, mul_sub, Real.exp_sub ];
    rw [ MeasureTheory.integral_div, mul_comm ];
  · apply_rules [ ProbabilityTheory.mgf_pos ];
    exact integrable_exp_smul_lipschitz F L hL hLip t

/-
**One-dimensional Gaussian integration by parts (Stein's identity).**  For a `C¹`
function `g` on `ℝ` whose value and derivative grow no faster than `C e^{c|x|}`, integration
against the standard Gaussian satisfies `∫ x * g x dγ = ∫ g' x dγ`.  This follows from the
boundary-free integration-by-parts on `ℝ` together with the identity `φ' = -x φ` for the
Gaussian density `φ`.
-/
set_option maxHeartbeats 4000000 in
lemma gaussianReal_stein (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'cont : Continuous g')
    (C c : ℝ) (hgbound : ∀ x, |g x| ≤ C * Real.exp (c * |x|))
    (hg'bound : ∀ x, |g' x| ≤ C * Real.exp (c * |x|)) :
    ∫ x, x * g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) := by
  -- Let's simplify the integral using the fact that multiplication by a constant out of the integral sign can be taken outside.
  suffices h_simp : ∫ x, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) = ∫ x, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) by
    convert h_simp using 1 <;> norm_num [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, gaussianReal ];
    · rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part, MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul, MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ gaussianPDF ];
        · congr! 2;
          · congr! 1;
            ext; rw [ ← ENNReal.ofReal_mul ( by exact ( by rw [ gaussianPDFReal ] ; positivity ) ) ] ; rw [ gaussianPDFReal ] ; ring; norm_num [ Real.sqrt_ne_zero'.mpr Real.pi_pos ] ;
            ring;
          · refine' MeasureTheory.lintegral_congr fun x => _;
            rw [ ← ENNReal.ofReal_mul ( by exact mul_nonneg ( by positivity ) ( by positivity ) ) ] ; norm_num [ gaussianPDFReal ] ; ring;
        · fun_prop;
        · exact Measurable.ennreal_ofReal ( Measurable.neg ( measurable_id.mul ( show Measurable g from by exact Continuous.measurable ( by exact continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ) );
        · fun_prop;
        · exact Measurable.ennreal_ofReal ( measurable_id.mul ( show Measurable g from by exact Continuous.measurable ( by exact continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) );
      · have h_integrable : MeasureTheory.Integrable (fun x => x * g x * (Real.exp (-x^2 / 2))) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => x * (C * Real.exp (c * |x|)) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (-x^2 / 4)) MeasureTheory.volume := by
                have := @integrable_rpow_mul_exp_neg_mul_sq;
                convert @this ( 1 / 4 ) ( by norm_num ) 1 ( by norm_num ) using 3 ; norm_num ; ring;
              have h_integrable : ∀ x : ℝ, |x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)| ≤ |x * Real.exp (-x^2 / 4)| * Real.exp (c^2) := by
                intro x; rw [ abs_mul, abs_mul, abs_mul ] ; norm_num [ ← Real.exp_add ] ; ring_nf; norm_num;
                norm_num [ mul_assoc, ← Real.exp_add ];
                exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases abs_cases x <;> nlinarith [ sq_nonneg ( |x| - 2 * c ) ] ) ( abs_nonneg x );
              refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun x => |x * Real.exp ( -x ^ 2 / 4 )| * Real.exp ( c ^ 2 );
              · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.abs ‹_› ) _;
              · exact Continuous.aestronglyMeasurable ( by continuity );
              · exact Filter.Eventually.of_forall h_integrable;
            convert h_integrable.const_mul C using 2 ; ring;
          refine' h_integrable.norm.mono' _ _;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ) ( Continuous.aestronglyMeasurable ( show Continuous fun x => Real.exp ( -x ^ 2 / 2 ) from Real.continuous_exp.comp <| by continuity ) );
          · simp_all +decide [ abs_mul, mul_assoc ];
            filter_upwards [ ] with x using mul_le_mul_of_nonneg_left ( by rw [ ← mul_assoc ] ; exact mul_le_mul_of_nonneg_right ( le_trans ( hgbound x ) ( mul_le_mul_of_nonneg_right ( le_abs_self _ ) ( Real.exp_nonneg _ ) ) ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ );
        convert h_integrable.div_const ( Real.sqrt 2 * Real.sqrt Real.pi ) using 2 ; ring;
      · have h_integrable : MeasureTheory.Integrable (fun x => x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => x * g x * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => x * (C * Real.exp (c * |x|)) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
                have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (-x^2 / 4)) MeasureTheory.volume := by
                  have := @integrable_rpow_mul_exp_neg_mul_sq;
                  convert @this ( 1 / 4 ) ( by norm_num ) 1 ( by norm_num ) using 3 ; norm_num ; ring;
                have h_integrable : ∀ x : ℝ, |x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)| ≤ |x * Real.exp (-x^2 / 4)| * Real.exp (c^2) := by
                  intro x; rw [ abs_mul, abs_mul, abs_mul ] ; norm_num [ ← Real.exp_add ] ; ring_nf; norm_num;
                  norm_num [ mul_assoc, ← Real.exp_add ];
                  exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases abs_cases x <;> nlinarith [ sq_nonneg ( |x| - 2 * c ) ] ) ( abs_nonneg x );
                refine' MeasureTheory.Integrable.mono' _ _ _;
                refine' fun x => |x * Real.exp ( -x ^ 2 / 4 )| * Real.exp ( c ^ 2 );
                · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.abs ‹_› ) _;
                · exact Continuous.aestronglyMeasurable ( by continuity );
                · exact Filter.Eventually.of_forall h_integrable;
              convert h_integrable.const_mul C using 2 ; ring;
            refine' h_integrable.norm.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ) ( Continuous.aestronglyMeasurable ( show Continuous fun x => Real.exp ( -x ^ 2 / 2 ) from Real.continuous_exp.comp <| by continuity ) );
            · simp_all +decide [ abs_mul, mul_assoc ];
              filter_upwards [ ] with x using mul_le_mul_of_nonneg_left ( by rw [ ← mul_assoc ] ; exact mul_le_mul_of_nonneg_right ( le_trans ( hgbound x ) ( mul_le_mul_of_nonneg_right ( le_abs_self _ ) ( Real.exp_nonneg _ ) ) ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ );
          convert h_integrable.div_const ( Real.sqrt ( 2 * Real.pi ) ) using 2 ; ring;
        rw [ MeasureTheory.integrable_withDensity_iff ];
        · convert h_integrable using 1 <;>
            first
            | rfl
            | (funext x
               rw [toReal_gaussianPDF]
               norm_num [gaussianPDFReal]
               ring
               exact Or.inl trivial)
        · fun_prop;
        · simp [gaussianPDF];
    · rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part, MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul, MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ gaussianPDF ];
        · congr! 2;
          · congr! 1;
            ext; rw [ gaussianPDFReal ] ; ring;
            rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; norm_num ; ring;
          · congr! 1;
            ext; rw [ ← ENNReal.ofReal_mul ( by exact mul_nonneg ( by positivity ) ( Real.exp_nonneg _ ) ) ] ; norm_num [ gaussianPDFReal ] ; ring;
        · fun_prop;
        · exact Measurable.ennreal_ofReal ( hg'cont.measurable.neg );
        · fun_prop;
        · exact Measurable.ennreal_ofReal hg'cont.measurable;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => C * Real.exp ( c * |x| ) * ( Real.exp ( -x ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) );
        · have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x|) * Real.exp (-x ^ 2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x| - x ^ 2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (-x ^ 2 / 4)) MeasureTheory.volume := by
                simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 4 ) );
              refine' h_integrable.const_mul ( Real.exp ( 2 * c ^ 2 ) ) |> fun h => h.mono' _ _;
              · exact Continuous.aestronglyMeasurable ( by continuity );
              · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ;
            convert h_integrable using 2 ; rw [ ← Real.exp_add ] ; ring;
          convert h_integrable.const_mul ( C / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) using 2 ; ring;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( hg'cont.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
        · filter_upwards [ ] with x using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( by positivity : 0 ≤ Real.exp ( -x ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ] ; exact mul_le_mul_of_nonneg_right ( hg'bound x ) ( by positivity ) ;
      · have h_integrable : MeasureTheory.Integrable (fun x => g' x * Real.exp (-x ^ 2 / 2)) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => C * Real.exp (c * |x|) * Real.exp (-x ^ 2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x| - x ^ 2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (-x ^ 2 / 4)) MeasureTheory.volume := by
                simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 4 ) );
              refine' h_integrable.const_mul ( Real.exp ( 2 * c ^ 2 ) ) |> fun h => h.mono' _ _;
              · exact Continuous.aestronglyMeasurable ( by continuity );
              · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ;
            convert h_integrable.const_mul C using 2 ; rw [ mul_assoc, ← Real.exp_add ] ; ring;
          refine' h_integrable.mono' _ _;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( hg'cont.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
          · filter_upwards [ ] using fun x => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( hg'bound x ) ( Real.exp_nonneg _ ) ;
        rw [ MeasureTheory.integrable_withDensity_iff ];
        · convert h_integrable.div_const ( Real.sqrt ( 2 * Real.pi ) ) using 1 <;>
            first
            | rfl
            | (funext x
               rw [toReal_gaussianPDF]
               norm_num [gaussianPDFReal]
               ring)
        · fun_prop;
        · simp [gaussianPDF];
  -- By integration by parts, we have $\int_{-\infty}^{\infty} x g(x) \phi(x) \, dx = \left[ -g(x) \phi(x) \right]_{-\infty}^{\infty} + \int_{-\infty}^{\infty} g'(x) \phi(x) \, dx$.
  have h_parts : ∀ a b : ℝ, ∫ x in a..b, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) = -g b * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi)) + g a * (Real.exp (-a^2 / 2) / Real.sqrt (2 * Real.pi)) + ∫ x in a..b, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) := by
    intro a b;
    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun x => -g x * ( Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) ) + ∫ x in a..x, g' x * ( Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) );
    · simpa using by ring;
    · intro x hx
      have hden : HasDerivAt
          (fun y : ℝ ↦ Real.exp (-y ^ 2 / 2) / Real.sqrt (2 * Real.pi))
          (-x * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))) x := by
        convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp.div_const
          (Real.sqrt (2 * Real.pi))) using 1 <;>
          first | rfl | (simp only [Pi.neg_apply]; ring)
      have hint : HasDerivAt
          (fun y : ℝ ↦ ∫ u in a..y,
            g' u * (Real.exp (-u ^ 2 / 2) / Real.sqrt (2 * Real.pi)))
          (g' x * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))) x := by
        exact intervalIntegral.integral_hasDerivAt_right
          (Continuous.intervalIntegrable (hg'cont.mul (by fun_prop)) _ _)
          ((hg'cont.mul (by fun_prop)).stronglyMeasurable.stronglyMeasurableAtFilter)
          (hg'cont.continuousAt.mul (by fun_prop))
      have htotal := ((hg x).neg.mul hden).add hint
      convert htotal using 1 <;>
        first | rfl | (simp only [Pi.neg_apply]; ring)
    · exact Continuous.intervalIntegrable ( by exact Continuous.mul ( Continuous.mul continuous_id ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ( by continuity ) ) _ _;
  -- Let's choose any two points $a$ and $b$ such that $a < b$.
  have h_lim : Filter.Tendsto (fun b => ∫ x in (-b)..b, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds (∫ x, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)))) := by
    apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral ];
    · -- We'll use the fact that $|x g(x)| \leq C |x| e^{c|x|}$ and $|x| e^{c|x|}$ is integrable.
      have h_integrable : MeasureTheory.Integrable (fun x => |x| * Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
        have h_integrable : MeasureTheory.Integrable (fun x => |x| * Real.exp (-x^2 / 4)) MeasureTheory.volume := by
          have := @integrable_rpow_mul_exp_neg_mul_sq;
          specialize @this ( 1 / 4 ) ( by norm_num ) ( 1 : ℝ ) ; norm_num at this;
          convert this.norm using 2 ; norm_num [ div_eq_inv_mul ];
        have h_integrable : ∀ x : ℝ, |x| * Real.exp (c * |x|) * Real.exp (-x^2 / 2) ≤ |x| * Real.exp (-x^2 / 4) * Real.exp (2 * c^2) := by
          intro x; rw [ mul_assoc, mul_assoc ] ; rw [ ← Real.exp_add, ← Real.exp_add ] ; ring_nf; norm_num;
          exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ( abs_nonneg x );
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => |x| * Real.exp ( -x ^ 2 / 4 ) * Real.exp ( 2 * c ^ 2 );
        · exact MeasureTheory.Integrable.mul_const ‹_› _;
        · exact Continuous.aestronglyMeasurable ( by continuity );
        · filter_upwards [ ] using fun x => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_integrable x;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => |x| * C * Real.exp ( c * |x| ) * Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi );
      · convert h_integrable.const_mul ( C / Real.sqrt ( 2 * Real.pi ) ) using 1 <;>
          first | rfl | (funext x; ring)
      · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Continuous.mul continuous_id ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ( by continuity ) );
      · simp_all +decide [ abs_mul, mul_assoc, mul_div_assoc ];
        filter_upwards [ ] with x using by rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; exact mul_le_mul_of_nonneg_left ( by simpa only [ mul_assoc, mul_div_assoc ] using mul_le_mul_of_nonneg_right ( hgbound x ) ( by positivity ) ) ( by positivity ) ;
    · exact Filter.tendsto_neg_atTop_atBot;
    · exact Filter.tendsto_id;
  -- By the properties of the Gaussian measure, we know that $\lim_{b \to \infty} g(b) \phi(b) = 0$ and $\lim_{b \to \infty} g(-b) \phi(-b) = 0$.
  have h_lim_zero : Filter.Tendsto (fun b => g b * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun b => g (-b) * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds 0) := by
    have h_lim_zero : Filter.Tendsto (fun b => C * Real.exp (c * |b|) * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds 0) := by
      -- We can factor out the constant $C / \sqrt{2\pi}$ and use the fact that $\exp(-b^2 / 2 + c|b|)$ tends to $0$ as $b$ tends to infinity.
      have h_exp : Filter.Tendsto (fun b => Real.exp (-b^2 / 2 + c * |b|)) Filter.atTop (nhds 0) := by
        norm_num [ Filter.tendsto_atTop_atBot ];
        exact fun b => ⟨ |b| * 2 + |c| * 2 + 1, fun x hx => by cases abs_cases b <;> cases abs_cases c <;> cases abs_cases x <;> nlinarith ⟩;
      convert h_exp.const_mul ( C / Real.sqrt ( 2 * Real.pi ) ) using 2 <;> ring;
      rw [ Real.exp_add ] ; ring;
    refine' ⟨ squeeze_zero_norm _ h_lim_zero, squeeze_zero_norm _ h_lim_zero ⟩;
    · exact fun x => by simpa [ abs_mul, abs_div, abs_of_nonneg ( Real.sqrt_nonneg _ ) ] using mul_le_mul_of_nonneg_right ( hgbound x ) ( by positivity ) ;
    · simp +zetaDelta at *;
      exact fun x => by rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; exact mul_le_mul_of_nonneg_right ( by simpa using hgbound ( -x ) ) ( by positivity ) ;
  have h_lim_zero : Filter.Tendsto (fun b => ∫ x in (-b)..b, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds (∫ x, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)))) := by
    apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral ];
    · -- The function $g'$ is bounded by $C e^{c|x|}$, and the Gaussian density is integrable.
      have h_integrable : MeasureTheory.Integrable (fun x => C * Real.exp (c * |x|) * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) MeasureTheory.volume := by
        have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x| - x ^ 2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (-x ^ 2 / 4)) MeasureTheory.volume := by
              simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 4 ) );
            refine' h_integrable.const_mul ( Real.exp ( c ^ 2 ) ) |> fun h => h.mono' _ _;
            · exact Continuous.aestronglyMeasurable ( by continuity );
            · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ;
          convert h_integrable using 1 ; ext x ; rw [ ← Real.exp_add ] ; ring;
        convert h_integrable.const_mul ( C / Real.sqrt ( 2 * Real.pi ) ) using 2 ; ring;
      refine' h_integrable.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( hg'cont.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
      · filter_upwards [ ] with x using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( by positivity : 0 ≤ Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) ) ] ; exact mul_le_mul_of_nonneg_right ( hg'bound x ) ( by positivity ) ;
    · exact Filter.tendsto_neg_atTop_atBot;
    · exact Filter.tendsto_id;
  simp_all +decide [ mul_div_assoc ];
  exact tendsto_nhds_unique h_lim ( by simpa using Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.neg ( ‹Filter.Tendsto ( fun b => g b * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ∧ Filter.Tendsto ( fun b => g ( -b ) * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ›.1 ) ) ( ‹Filter.Tendsto ( fun b => g b * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ∧ Filter.Tendsto ( fun b => g ( -b ) * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ›.2 ) ) h_lim_zero )

/-
The standard Euclidean Gaussian measure is centered: its mean is `0`.
-/
lemma standardGaussianMeasureOnEuclidean_integral_id {ι : Type*} [Fintype ι] :
    (standardGaussianMeasureOnEuclidean ι)[id] = (0 : EuclideanSpace ℝ ι) := by
  by_contra h_nonzero;
  -- The measure `standardGaussianMeasureOnEuclidean ι` is symmetric around `0`, meaning it is equal to its pushforward by the negation map.
  have h_symm : standardGaussianMeasureOnEuclidean ι = MeasureTheory.Measure.map (fun x => -x) (standardGaussianMeasureOnEuclidean ι) := by
    unfold standardGaussianMeasureOnEuclidean;
    rw [ MeasureTheory.Measure.map_map ];
    · have h_gauss_symm : ∀ (μ : MeasureTheory.Measure ℝ), μ = gaussianReal 0 1 → MeasureTheory.Measure.map (fun x => -x) μ = μ := by
        grind +suggestions;
      have h_gauss_symm : MeasureTheory.Measure.map (fun x : ι → ℝ => fun i => -x i) (Measure.pi fun _ : ι => gaussianReal 0 1) = Measure.pi fun _ : ι => gaussianReal 0 1 := by
        refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
        intro s hs; rw [ MeasureTheory.Measure.map_apply ];
        · simp +decide [ Set.preimage, hs ];
          convert MeasureTheory.Measure.pi_pi _ _ using 1;
          · rw [ show { x : ι → ℝ | ∀ i, -x i ∈ s i } = ( Set.pi Set.univ fun i => ( fun x => -x ) ⁻¹' s i ) by ext; simp +decide [ Set.mem_univ_pi ] ];
            rw [ MeasureTheory.Measure.pi_pi, MeasureTheory.Measure.pi_pi ];
            exact Finset.prod_congr rfl fun i _ => by rw [ ← MeasureTheory.Measure.map_apply ( measurable_neg ) ( hs i ), h_gauss_symm _ rfl ] ;
          · exact fun i => by infer_instance;
        · exact measurable_pi_lambda _ fun _ => measurable_neg.comp ( measurable_pi_apply _ );
        · exact MeasurableSet.univ_pi hs;
      convert congr_arg ( MeasureTheory.Measure.map ( WithLp.toLp 2 ) ) h_gauss_symm.symm using 1;
      rw [ MeasureTheory.Measure.map_map ];
      · congr! 1;
      · exact WithLp.measurable_toLp 2 _;
      · exact measurable_pi_lambda _ fun _ => measurable_neg.comp ( measurable_pi_apply _ );
    · exact measurable_id.neg;
    · fun_prop;
  apply_fun ( fun μ => ∫ x, x ∂μ ) at h_symm;
  rw [ MeasureTheory.integral_map ] at h_symm;
  · rw [ MeasureTheory.integral_neg ] at h_symm;
    exact h_nonzero ( by ext; have := congr_arg ( fun x => x ‹_› ) h_symm; norm_num at *; linarith );
  · exact measurable_id.neg.aemeasurable;
  · exact measurable_id.aestronglyMeasurable

/-
`exp (c |y|)` is integrable against the one-dimensional standard Gaussian.
-/
lemma integrable_exp_abs_gaussianReal (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (c * |y|)) (gaussianReal 0 1) := by
  have h_integrable : MeasureTheory.Integrable (fun y => Real.exp (c * y)) (gaussianReal 0 1) ∧ MeasureTheory.Integrable (fun y => Real.exp (-c * y)) (gaussianReal 0 1) := by
    constructor;
    · have h_integrable : ∫ y, Real.exp (c * y) ∂(gaussianReal 0 1) = Real.exp (c^2 / 2) := by
        have := @ProbabilityTheory.mgf_gaussianReal;
        convert @this ℝ _ ( gaussianReal 0 1 ) 0 1 ( fun x => x ) _ c using 1 <;> norm_num [ mgf ];
      exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity );
    · have := @ProbabilityTheory.mgf_gaussianReal;
      specialize @this ℝ _ ( gaussianReal 0 1 ) 0 1 ( fun x => x ) ; norm_num at this;
      contrapose! this;
      use -c; simp_all +decide [ mgf ];
      rw [ MeasureTheory.integral_undef this ] ; positivity;
  refine' MeasureTheory.Integrable.mono' ( h_integrable.1.add h_integrable.2 ) _ _;
  · exact Continuous.aestronglyMeasurable ( by continuity );
  · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; cases abs_cases x <;> simp +decide [ * ] <;> positivity;

/-
`|y| exp (c |y|)` is integrable against the one-dimensional standard Gaussian.
-/
lemma integrable_abs_mul_exp_abs_gaussianReal (c : ℝ) :
    Integrable (fun y : ℝ => |y| * Real.exp (c * |y|)) (gaussianReal 0 1) := by
  -- We'll use the fact that |y| * exp(c * |y|) ≤ exp((|c| + 1) * |y|).
  have h_bound : ∀ y : ℝ, |y| * Real.exp (c * |y|) ≤ Real.exp ((|c| + 1) * |y|) := by
    intro y;
    exact le_trans ( mul_le_mul_of_nonneg_right ( show |y| ≤ Real.exp |y| by linarith [ Real.add_one_le_exp |y| ] ) ( Real.exp_nonneg _ ) ) ( by rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases c <;> cases abs_cases y <;> nlinarith ) );
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => Real.exp ( ( |c| + 1 ) * |y| );
  · convert integrable_exp_abs_gaussianReal ( |c| + 1 ) using 1;
  · exact Continuous.aestronglyMeasurable ( by continuity );
  · filter_upwards [ ] using fun x => by simpa using h_bound x;

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
lemma integrable_abs_coord_mul_exp_c_sum_abs_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (i : ι) :
    Integrable (fun y : ι → ℝ => |y i| * Real.exp (c * ∑ j, |y j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => Real.exp ( ( |c| + 1 ) * ∑ j, |y j| );
  · convert integrable_exp_c_sum_abs_pi ( |c| + 1 ) using 1;
  · fun_prop;
  · filter_upwards [ ] with y using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact le_trans ( mul_le_mul_of_nonneg_right ( show |y i| ≤ Real.exp |y i| by linarith [ Real.add_one_le_exp |y i| ] ) ( Real.exp_nonneg _ ) ) ( by rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases c <;> cases abs_cases ( y i ) <;> nlinarith [ Real.exp_pos |y i|, Finset.single_le_sum ( fun a _ => abs_nonneg ( y a ) ) ( Finset.mem_univ i ) ] ) ) ;

/-
**Tensorized Stein identity on the product Gaussian measure.**  For a `C¹` function `h`
on `ι → ℝ` whose value and coordinate partial derivatives grow no faster than
`C e^{c ∑ⱼ |yⱼ|}`, integration against the product of standard Gaussians satisfies
`∫ yᵢ h y = ∫ ∂ᵢ h y`.  This is Fubini over the `i`-th coordinate combined with the
one-dimensional Stein identity `gaussianReal_stein`.
-/
lemma pi_gaussian_stein_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : (ι → ℝ) → ℝ) (i : ι)
    (hh : ContDiff ℝ 1 h) (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hhb : ∀ y, |h y| ≤ C * Real.exp (c * ∑ j, |y j|))
    (hdb : ∀ y j, |fderiv ℝ h y (Pi.single j 1)| ≤ C * Real.exp (c * ∑ k, |y k|)) :
    ∫ y, y i * h y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      = ∫ y, fderiv ℝ h y (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h_integrable : MeasureTheory.Integrable (fun y : ι → ℝ => y i * h y) (Measure.pi fun _ : ι => gaussianReal 0 1) ∧ MeasureTheory.Integrable (fun y : ι → ℝ => (fderiv ℝ h y) (Pi.single i 1)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    constructor;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun y => C * |y i| * Real.exp ( c * ∑ j, |y j| );
      · convert integrable_abs_coord_mul_exp_c_sum_abs_pi c i |> fun h => h.const_mul C using 2 ; ring;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply i |> Measurable.aestronglyMeasurable ) ( hh.continuous.aestronglyMeasurable );
      · filter_upwards [ ] with y using by rw [ Real.norm_eq_abs, abs_mul ] ; nlinarith [ hhb y, abs_nonneg ( y i ) ] ;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun y => C * Real.exp ( c * ∑ j, |y j| );
      · exact MeasureTheory.Integrable.const_mul ( integrable_exp_c_sum_abs_pi c ) _;
      · fun_prop;
      · exact Filter.Eventually.of_forall fun y => hdb y i;
  have h_split : ∀ y : {j // j ≠ i} → ℝ, ∫ x : ℝ, x * h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x) ∂(gaussianReal 0 1) = ∫ x : ℝ, (fderiv ℝ h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x)) (Pi.single i 1) ∂(gaussianReal 0 1) := by
    intro y
    set Yb : ι → ℝ := fun j => if h : j = i then 0 else y ⟨j,h⟩
    have h_Yb : ∀ x, Function.update Yb i x = fun j => if h : j = i then x else y ⟨j,h⟩ := by
      grind;
    have h_G : ∀ x, HasDerivAt (fun t => h (Function.update Yb i t)) ((fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)) x := by
      intro x
      have h_chain : HasDerivAt (fun t => h (Function.update Yb i t)) ((fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)) x := by
        have h_update : HasDerivAt (fun t => Function.update Yb i t) (Pi.single i 1) x :=
          hasDerivAt_update Yb i x
        convert HasFDerivAt.comp_hasDerivAt x
          (hh.contDiffAt.differentiableAt (by norm_num) |> DifferentiableAt.hasFDerivAt)
          h_update using 1 <;> rfl
      exact h_chain;
    have h_G_bound : ∀ x, |h (Function.update Yb i x)| ≤ C * Real.exp (c * (|x| + ∑ j, |y j|)) ∧ |(fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)| ≤ C * Real.exp (c * (|x| + ∑ j, |y j|)) := by
      intro x
      have h_sum : ∑ j, |(Function.update Yb i x) j| = |x| + ∑ j, |y j| := by
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)];
        refine' congr_arg₂ ( · + · ) _ _;
        · simp +decide [ Function.update_apply ];
        · refine' Finset.sum_bij ( fun j _ => ⟨ j, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ Function.update_apply ];
          aesop;
      exact ⟨ by simpa only [ h_sum ] using hhb ( Function.update Yb i x ), by simpa only [ h_sum ] using hdb ( Function.update Yb i x ) i ⟩;
    have := @gaussianReal_stein;
    convert this ( fun x => h ( Function.update Yb i x ) ) ( fun x => ( fderiv ℝ h ( Function.update Yb i x ) ) ( Pi.single i 1 ) ) h_G _ ( C * Real.exp ( c * ∑ j, |y j| ) ) c _ _ using 1;
    · fun_prop;
    · intro x; convert h_G_bound x |>.1 using 1; rw [ mul_assoc, ← Real.exp_add ] ; ring;
    · intro x; specialize h_G_bound x; rw [ mul_assoc, ← Real.exp_add ] ; ring_nf at *; aesop;
  have h_split : ∫ y : ι → ℝ, y i * h y ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = ∫ y : {j // j ≠ i} → ℝ, ∫ x : ℝ, x * h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x) ∂(gaussianReal 0 1) ∂(Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
    have h_split : Measure.pi (fun _ : ι => gaussianReal 0 1) = Measure.map (fun p : ℝ × ({j // j ≠ i} → ℝ) => Function.update (fun j => if h : j = i then 0 else p.2 ⟨j,h⟩) i p.1) (gaussianReal 0 1 |> Measure.prod <| Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
      refine' MeasureTheory.Measure.pi_eq _;
      intro s hs; rw [ MeasureTheory.Measure.map_apply ];
      · rw [ show ( fun p : ℝ × ( { j // j ≠ i } → ℝ ) => Function.update ( fun j => if h : j = i then 0 else p.2 ⟨ j, h ⟩ ) i p.1 ) ⁻¹' Set.univ.pi s = ( s i ) ×ˢ ( Set.pi Set.univ fun j : { j // j ≠ i } => s j ) from ?_ ];
        · rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
          simp +decide [MeasureTheory.Measure.prod_prod]
          refine' congr rfl ( Finset.prod_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide;
        · grind;
      · refine' measurable_pi_lambda _ _;
        intro j; by_cases hj : j = i <;> simp +decide [ hj, Function.update_apply ] ;
        · exact measurable_fst;
        · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
      · exact MeasurableSet.univ_pi hs;
    rw [ h_split, MeasureTheory.integral_map ];
    · erw [ MeasureTheory.integral_prod_symm ];
      · simp +decide [ Function.update_apply ];
      · convert h_integrable.1 using 1;
        rw [ h_split ];
        rw [ MeasureTheory.integrable_map_measure ];
        · rfl;
        · exact h_split ▸ h_integrable.1.aestronglyMeasurable;
        · refine' Measurable.aemeasurable _;
          refine' measurable_pi_lambda _ _;
          intro j; by_cases hj : j = i <;> simp +decide [ hj, Function.update_apply ] ;
          · exact measurable_fst;
          · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
    · refine' Measurable.aemeasurable _;
      refine' measurable_pi_lambda _ _;
      intro j; by_cases hj : j = i <;> simp +decide [ hj, Function.update_apply ] ;
      · exact measurable_fst;
      · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
    · exact h_split ▸ h_integrable.1.aestronglyMeasurable;
  have h_split : ∫ y : ι → ℝ, (fderiv ℝ h y) (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = ∫ y : {j // j ≠ i} → ℝ, ∫ x : ℝ, (fderiv ℝ h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x)) (Pi.single i 1) ∂(gaussianReal 0 1) ∂(Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
    have h_split : Measure.pi (fun _ : ι => gaussianReal 0 1) = Measure.map (fun p : ℝ × ({j // j ≠ i} → ℝ) => Function.update (fun j => if h : j = i then 0 else p.2 ⟨j,h⟩) i p.1) (gaussianReal 0 1 |> Measure.prod <| Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
      rw [ MeasureTheory.Measure.pi_eq ];
      intro s hs;
      rw [ MeasureTheory.Measure.map_apply ];
      · rw [ show ( fun p : ℝ × ( { j // j ≠ i } → ℝ ) => Function.update ( fun j => if h : j = i then 0 else p.2 ⟨ j, h ⟩ ) i p.1 ) ⁻¹' Set.univ.pi s = ( s i ) ×ˢ ( Set.pi Set.univ fun j : { j // j ≠ i } => s j ) from ?_ ];
        · rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
          simp +decide [MeasureTheory.Measure.prod_prod]
          refine' congr rfl ( Finset.prod_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide;
        · grind;
      · refine' measurable_pi_lambda _ _;
        intro j; by_cases hj : j = i <;> simp +decide [ hj, Function.update_apply ] ;
        · exact measurable_fst;
        · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
      · exact MeasurableSet.univ_pi hs;
    rw [ h_split, MeasureTheory.integral_map ];
    · rw [ MeasureTheory.integral_prod_symm ];
      rw [ h_split ] at h_integrable;
      have hmap : Measurable
          (fun p : ℝ × ({j // j ≠ i} → ℝ) ↦
            Function.update (fun j ↦ if h : j = i then 0 else p.2 ⟨j, h⟩) i p.1) := by
        refine measurable_pi_lambda _ fun j ↦ ?_
        by_cases hj : j = i
        · simpa [hj] using measurable_fst
        · have hm : Measurable
              (fun p : ℝ × ({j // j ≠ i} → ℝ) ↦ p.2 ⟨j, hj⟩) :=
            (@measurable_pi_apply {j // j ≠ i} (fun _ ↦ ℝ) _ ⟨j, hj⟩).comp
              measurable_snd
          simpa [hj] using hm
      convert h_integrable.2.comp_measurable hmap using 1
      rfl
    · refine' Measurable.aemeasurable _;
      refine' measurable_pi_lambda _ _;
      intro j; by_cases hj : j = i <;> simp +decide [ hj, Function.update_apply ] ;
      · exact measurable_fst;
      · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
    · convert h_integrable.2.aestronglyMeasurable using 1;
      exact h_split.symm;
  aesop

/-
The `i`-th coordinate of the gradient equals the partial derivative in direction `i`.
-/
lemma gradient_coord_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : EuclideanSpace ℝ ι → ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    (gradient g w) i = fderiv ℝ g w (EuclideanSpace.single i 1) := by
  simp +decide [ gradient ];
  rw [ ← InnerProductSpace.toDual_symm_apply ];
  rw [ EuclideanSpace.inner_single_right ] ; norm_num

/-
Transferring the `i`-th gradient coordinate through the `toLp` identification: it becomes
the `i`-th partial derivative of the composed function on `ι → ℝ`.
-/
lemma gradient_toLp_coord_eq_fderiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : EuclideanSpace ℝ ι → ℝ) (hg : Differentiable ℝ g) (y : ι → ℝ) (i : ι) :
    (gradient g (WithLp.toLp 2 y)) i
      = fderiv ℝ (fun z => g (WithLp.toLp 2 z)) y (Pi.single i 1) := by
  rw [ gradient ];
  rw [ show ( fun z => g ( WithLp.toLp 2 z ) ) = g ∘ ( WithLp.toLp 2 ) from rfl, fderiv_comp ] <;> norm_num [ hg.differentiableAt, WithLp.ofLp ];
  · rw [ fderiv ];
    rw [ fderiv ];
    rw [ fderivWithin_univ, fderivWithin_univ, show ( WithLp.toLp 2 : ( ι → ℝ ) → EuclideanSpace ℝ ι ) = ( PiLp.continuousLinearEquiv 2 ℝ ( fun _ : ι => ℝ ) ).symm from rfl, ContinuousLinearEquiv.fderiv ] ; norm_num;
    rw [ ← InnerProductSpace.toDual_symm_apply ];
    rw [ EuclideanSpace.inner_single_right ] ; norm_num;
  · refine' ⟨ _, hasFDerivAt_iff_tendsto.mpr _ ⟩;
    exact ( ContinuousLinearEquiv.toContinuousLinearMap ( ContinuousLinearEquiv.symm ( EuclideanSpace.equiv ι ℝ ) ) );
    simp +decide [ WithLp.toLp ]

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
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun w => |C| * Real.exp ( ( c + 1 ) * ‖w‖ );
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm ( c + 1 ) ) _;
    · refine' MeasureTheory.AEStronglyMeasurable.mul _ ( hg.continuous.aestronglyMeasurable );
      fun_prop;
    · refine' Filter.Eventually.of_forall fun w => _;
      refine' le_trans ( norm_mul_le _ _ ) _;
      refine' le_trans ( mul_le_mul_of_nonneg_right ( show ‖w.ofLp i‖ ≤ ‖w‖ from _ ) ( norm_nonneg _ ) ) _;
      · simp +decide [ EuclideanSpace.norm_eq ];
        exact Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( w.ofLp i ) ) ( Finset.mem_univ i ) );
      · refine' le_trans ( mul_le_mul_of_nonneg_left ( hgb w ) ( norm_nonneg _ ) ) _;
        rw [ add_mul, one_mul, Real.exp_add ];
        cases abs_cases C <;> nlinarith [ show 0 ≤ Real.exp ( c * ‖w‖ ) * Real.exp ‖w‖ by positivity, show ‖w‖ ≤ Real.exp ‖w‖ by exact le_trans ( by norm_num ) ( Real.add_one_le_exp _ ), show 0 ≤ C * Real.exp ( c * ‖w‖ ) by exact le_trans ( abs_nonneg _ ) ( hgb w ) ];
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun w => C * Real.exp ( c * ‖w‖ );
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm c ) _;
    · have h_grad_cont : Continuous (gradient g) := by
        have := hg.continuous_fderiv;
        exact Continuous.comp ( LinearIsometryEquiv.continuous _ ) ( this one_ne_zero );
      fun_prop;
    · refine' Filter.Eventually.of_forall fun w => le_trans _ ( hgradb w );
      simp +decide [ EuclideanSpace.norm_eq ];
      exact Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( ( gradient g w ).ofLp i ) ) ( Finset.mem_univ i ) )

end SYK
