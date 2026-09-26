import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import SYK.Probability.GaussianConcentration.StandardGaussian

open MeasureTheory Filter Set Real
open scoped ProbabilityTheory NNReal ENNReal Filter Topology

/-!
# Gaussian integration by parts via exponential tilt (Stein’s identity)

We prove Stein’s lemma and the integration by parts formula for real Gaussian
measures by an explicit control of the exponential tilt and a dominated
differentiation argument. The presentation is self–contained and works in full
generality for one–dimensional (possibly degenerate) Gaussians, under minimal,
standard hypotheses on the test function.

Let `γ_{μ,v}` denote the law of the real normal `N(μ,v)` (variance `v : ℝ≥0`).
For `v ≠ 0` (non-degenerate, centered case) and a test function `F : ℝ → ℝ`
which is `C¹` with polynomial growth (for `F` and `F'`), we show
  E[X F(X)] = v · E[F'(X)]   for X ∼ N(0,v).

The proof follows the canonical route:

1. Exponential tilt and shift:
   For the centered Gaussian density `φ_v(x)`, and `t ∈ ℝ`,
     exp(t x − v t²/2) φ_v(x) = φ_v(x − v t).
   Hence, for every test function `F`,
     E[F(X) exp(tX − v t²/2)] = E[F(X + v t)]  (X ∼ N(0,v)).

2. Difference–quotient bounds:
   We establish sharp, uniform (in `t` near `0`) bounds for
     (exp(t x − v t²/2) − 1)/t,
   derived from the generic inequality `|exp a − 1| ≤ |a| exp |a|`
   and exact algebra on the tilt exponent. This yields an
   exponential–linear integrable majorant after composing with `F`.

3. Dominated differentiation:
   Using the previous step, we differentiate under the integral sign at `t = 0`
   and identify both one–sided derivatives:
     (d/dt)|_{t=0} E[F(X) exp(tX − v t²/2)] = E[X F(X)],
     (d/dt)|_{t=0} E[F(X + v t)]           = v · E[F'(X)].
   Equality of left and right derivatives yields Stein’s identity.

4. Degenerate case:
   If `v = 0`, `γ_{μ,0}` is the Dirac mass at `μ`. All statements reduce to
   trivial identities and are handled uniformly in the API.

Main statements:

- `gaussianTilt_eq_shift`:
    Exponential tilt equals a spatial shift of the test function:
    ∫ F(x) exp(t x − v t²/2) dγ_{0,v}(x) = ∫ F(x + v t) dγ_{0,v}(x).

- `tiltKernel_diffquot_uniform_bound`:
    Uniform (in `t` near `0`) exponential–linear bound for the centered difference quotient
    of the kernel `exp(t x − v t²/2)`.

- `HasModerateGrowth`:
    A simple “polynomial growth” predicate on `F` and `F'` ensuring all integrability
    requirements against a Gaussian. This replaces ad‑hoc, local integrability checks.

- `gaussianTilt_hasDerivAt_left`, `gaussianTilt_hasDerivAt_right`:
    Differentiation under the integral sign at `t = 0` for the tilted functional.

- `stein_lemma_gaussianReal` and `gaussianReal_integration_by_parts`:
    Measure–level statements for `N(0,v)` with `v ≠ 0`.

- `gaussianRV_integration_by_parts` and
  `gaussian_integration_by_parts_general`:
    Random-variable versions for centered and non–centered Gaussians, respectively.

Auxiliary integrability layer:

- Polynomial × sub-Gaussian integrability:
    We prove
      (1+|x|)^k exp(s x²) ∈ L¹(γ_{0,v})
    for every `k : ℕ` whenever either `v = 0` or `s < 1/(2v)`.
    In particular, for `s = 1/(4v)` (non-degenerate) we get the explicit bound
      exp(|x|²/(4v)).
    This is the only analytic input needed for dominated differentiation.

Design notes and future extensions:

- The arguments are written for ℝ and make sharp, explicit use of the 1D tilt
  algebra. The architecture is ready for a finite–dimensional extension
  (`ℝ^n` with the Euclidean norm), where the Cameron–Martin formula replaces
  the 1D tilt identity and the same dominated-differentiation pattern applies.

- The degenerate case is treated uniformly by the Dirac–mass API.

- When interacting with Lebesgue measure, we use the standard `withDensity` and
  `MeasurePreserving` API; addition by a constant is measure–preserving and is
  the canonical tool to implement the change of variables needed in Step 1.

References:
- C. Stein (1972). A bound for the error in the normal approximation to the
  distribution of a sum of dependent random variables.
- M. Talagrand (2011). Upper and Lower Bounds for Stochastic Processes.

-/
namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If `f` is ae strongly measurable, then so is `‖f x‖^p`.
(The converse is false in general and was incorrectly stated before.) -/
lemma AEStronglyMeasurable.norm_rpow
    {E : Type*} [NormedAddCommGroup E] {f : α → E} {p : ℝ}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => ‖f x‖ ^ p) μ := by
  have : AEMeasurable (fun x => ‖f x‖ ^ p) μ :=
    hf.norm.aemeasurable.pow_const p
  exact this.aestronglyMeasurable

end MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω]

namespace ProbabilityTheory

/-- A random variable `g` is Gaussian with mean `μ` and variance `v` if its law is
`gaussianReal μ v`. -/
def IsGaussianRV (g : Ω → ℝ) (μ : ℝ) (v : ℝ≥0) : Prop :=
  Measure.map g ℙ = gaussianReal μ v

/-- A random variable `g` is centered Gaussian with variance `v` if its law is
`gaussianReal 0 v`. -/
def IsCenteredGaussianRV (g : Ω → ℝ) (v : ℝ≥0) : Prop :=
  IsGaussianRV g 0 v

/-- Second central moment of a (possibly non–centered) real Gaussian. -/
lemma integral_sq_sub_mean_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ)^2 ∂ gaussianReal μ v = v := by
  have h := variance_id_gaussianReal (μ := μ) (v := v)
  have := congrArg id h
  simpa using
    (by
      erw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
      exact h)

/-- Second moment of a centered Gaussian (mean = 0). -/
lemma integral_sq_gaussianReal_centered (v : ℝ≥0) :
    ∫ x, x^2 ∂ gaussianReal 0 v = v := by
  simpa using (integral_sq_sub_mean_gaussianReal (μ := 0) (v := v))

/-- Exponential tilt identity for the centered Gaussian density. -/
lemma gaussian_tilt_identity_zero
    {v : ℝ≥0} (hv : v ≠ 0) :
    ∀ t x : ℝ,
      Real.exp (t * x - (v:ℝ) * t^2 / 2) * gaussianPDFReal 0 v x
        = gaussianPDFReal 0 v (x - (v:ℝ) * t) := by
  intro t x
  have hvpos : 0 < (v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hsq : (x - (v:ℝ) * t)^2 = x^2 - 2 * (v:ℝ) * t * x + (v:ℝ)^2 * t^2 := by
    ring
  have hExp :
      (t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))
        = - ((x - (v:ℝ) * t)^2) / (2 * (v:ℝ)) := by
    have h2vne : (2 * (v:ℝ)) ≠ 0 := by nlinarith
    apply (mul_right_cancel₀ h2vne)
    have hL :
        ((t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))) * (2 * (v:ℝ))
          = 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2 - x^2 := by ring_nf; aesop
    have hR :
        (- ((x - (v:ℝ) * t)^2) / (2 * (v:ℝ))) * (2 * (v:ℝ))
          = - (x - (v:ℝ) * t)^2 := by
      field_simp [h2vne]
    have hR' :
        - (x - (v:ℝ) * t)^2 = 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2 - x^2 := by
      calc
        - (x - (v:ℝ) * t)^2
            = - (x^2 - 2 * (v:ℝ) * t * x + (v:ℝ)^2 * t^2) := by simp [hsq]
        _ = (-x^2 + 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2) := by ring
        _ = 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2 - x^2 := by ring
    aesop
  have : gaussianPDFReal 0 v x
      = (√(2 * π * (v:ℝ)))⁻¹ * Real.exp (- x^2 / (2 * (v:ℝ))) := by
    simp [gaussianPDFReal, sub_eq_add_neg, mul_comm, mul_left_comm]
  have : Real.exp (t * x - (v:ℝ) * t^2 / 2) * gaussianPDFReal 0 v x
      = (√(2 * π * (v:ℝ)))⁻¹
          * Real.exp ((t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))) := by
    simp [this, sub_eq_add_neg, Real.exp_add, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    ring_nf
  calc
    Real.exp (t * x - (v:ℝ) * t^2 / 2) * gaussianPDFReal 0 v x
        = (√(2 * π * (v:ℝ)))⁻¹
            * Real.exp ((t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))) := this
    _ = (√(2 * π * (v:ℝ)))⁻¹
            * Real.exp ( - ((x - (v:ℝ) * t)^2) / (2 * (v:ℝ)) ) := by
          simp [hExp]
    _ = gaussianPDFReal 0 v (x - (v:ℝ) * t) := by
          simp [gaussianPDFReal, sub_eq_add_neg, mul_comm, mul_left_comm, pow_two]

/-- Tilted Gaussian expectation functional. -/
noncomputable def gaussianTilt (F : ℝ → ℝ) (v : ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, F x * Real.exp (t * x - (v:ℝ) * t^2 / 2) ∂ (gaussianReal 0 v)

lemma gaussianTilt_eq_shift
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ} :
    ∀ t, gaussianTilt F v t
        = ∫ x, F (x + (v:ℝ) * t) ∂ (gaussianReal 0 v) := by
  intro t
  set φ := fun (μ₀ : ℝ) x => gaussianPDFReal μ₀ v x
  set c := (v : ℝ) * t
  have hConv :
    ∀ (μ₀ : ℝ) (f : ℝ → ℝ),
      (∫ x, f x ∂ gaussianReal μ₀ v)
        = ∫ x, φ μ₀ x • f x :=
      fun μ₀ f => integral_gaussianReal_eq_integral_smul
        (μ := μ₀) (v := v) hv (f := f)
  have h1 :
      gaussianTilt F v t
        = ∫ x, F x * Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x := by
    simp [gaussianTilt, hConv 0, φ, mul_comm, mul_left_comm]
  have hTilt :
      ∀ x,
        Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x
          = φ 0 (x - c) := by
    intro x
    simpa [φ, c] using gaussian_tilt_identity_zero (v := v) hv t x
  have h2 :
      gaussianTilt F v t
        = ∫ x, F x * φ 0 (x - c) := by
    calc
      gaussianTilt F v t
          = ∫ x, F x * Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x := h1
      _ = ∫ x, F x * (Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x) := by
            simp [mul_comm, mul_left_comm]
      _ = ∫ x, F x * φ 0 (x - c) := by
            simp [hTilt]
  have hTrans :
      (∫ x, F x * φ 0 (x - c))
        = ∫ x, F (x + c) * φ 0 x := by
    let g := fun x : ℝ => F x * φ 0 (x - c)
    have hInv : (∫ x, g (x + c)) = ∫ x, g x := by
      simpa using
        (integral_add_right_eq_self (μ := (volume : Measure ℝ)) (f := g) c)
    have : (fun x => g (x + c)) = fun x => F (x + c) * φ 0 x := by
      funext x; simp [g, φ, sub_eq_add_neg, add_assoc]
    simpa [g, this, φ, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hInv.symm
  have hR :
      (∫ x, F (x + c) * φ 0 x)
        = ∫ x, F (x + c) ∂ gaussianReal 0 v := by
    have hConv' := hConv 0 (fun x => F (x + c))
    simpa [φ, mul_comm, mul_left_comm, mul_assoc] using hConv'.symm
  calc
    gaussianTilt F v t
        = ∫ x, F x * φ 0 (x - c) := h2
    _ = ∫ x, F (x + c) * φ 0 x := hTrans
    _ = ∫ x, F (x + c) ∂ gaussianReal 0 v := hR

/-! ### Prerequisites for the proof of `gaussianTilt_hasDerivAt_left`

We isolate:
1. A core kernel `tiltKernel`.
2. Pointwise derivative lemmas for the kernel and the integrand.
3. A (local-in-`t`) domination lemma suitable for applying differentiation
   under the integral sign at `t = 0`. -/

/-- The (centered) Gaussian exponential tilt kernel (no prefactor `F x`). -/
@[simp] noncomputable def tiltKernel (v : ℝ≥0) (t x : ℝ) : ℝ :=
  Real.exp (t * x - (v : ℝ) * t^2 / 2)

/-- Pointwise derivative of the quadratic–linear exponent inside the kernel. -/
lemma hasDerivAt_tiltExponent
    (v : ℝ≥0) (x t : ℝ) :
  HasDerivAt (fun s => s * x - (v:ℝ) * s^2 / 2) (x - (v:ℝ) * t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * x) x t := by
    simpa [mul_comm] using (hasDerivAt_id t).mul_const x
  have h2 : HasDerivAt (fun s : ℝ => (v:ℝ) * s^2 / 2) ((v:ℝ) * t) t := by
    have hpow : HasDerivAt (fun s : ℝ => s^2) (2 * t) t := by
      simpa using (hasDerivAt_pow (n := 2) t)
    have := hpow.const_mul ((v:ℝ)/2)
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  have hsub := h1.sub h2
  change HasDerivAt
    ((fun s : ℝ => s * x) - (fun s : ℝ => (v : ℝ) * s ^ 2 / 2))
    (x - (v : ℝ) * t) t
  exact hsub

/-- Derivative of the tilt kernel in `t`. -/
lemma hasDerivAt_tiltKernel (v : ℝ≥0) (x t : ℝ) :
  HasDerivAt (fun s => tiltKernel v s x)
    ((x - (v:ℝ) * t) * tiltKernel v t x) t := by
  have hExp := hasDerivAt_tiltExponent v x t
  have := (Real.hasDerivAt_exp _).comp t hExp
  change HasDerivAt
    (Real.exp ∘ fun s : ℝ => s * x - (v : ℝ) * s ^ 2 / 2)
    ((x - (v : ℝ) * t) * Real.exp (t * x - (v : ℝ) * t ^ 2 / 2)) t
  simpa only [mul_comm] using this

/-- Specialization of `hasDerivAt_tiltKernel` at `t = 0`. -/
lemma hasDerivAt_tiltKernel_at0 (v : ℝ≥0) (x : ℝ) :
  HasDerivAt (fun s => tiltKernel v s x) (x) 0 := by
  simpa [tiltKernel] using
    (hasDerivAt_tiltKernel v x 0)

/-- Derivative of the full integrand (with fixed space parameter `x`)
    before multiplying by the test function `F x`. -/
lemma hasDerivAt_F_mul_tiltKernel
    (v : ℝ≥0) (F : ℝ → ℝ) (x t : ℝ) :
  HasDerivAt (fun s => F x * tiltKernel v s x)
    (F x * (x - (v:ℝ) * t) * tiltKernel v t x) t := by
  have hk := hasDerivAt_tiltKernel v x t
  simpa [tiltKernel, mul_comm, mul_left_comm, mul_assoc] using hk.const_mul (F x)

/-- Specialization at `t = 0`: derivative is `F x * x`. -/
lemma hasDerivAt_F_mul_tiltKernel_at0
    (v : ℝ≥0) (F : ℝ → ℝ) (x : ℝ) :
  HasDerivAt (fun s => F x * tiltKernel v s x) (F x * x) 0 := by
  simpa using
    (hasDerivAt_F_mul_tiltKernel v F x 0)

/-- The integrand (as a 2-variable function) used in `gaussianTilt`. -/
@[simp] noncomputable def gaussianTiltIntegrand (F : ℝ → ℝ) (v : ℝ≥0) (t x : ℝ) : ℝ :=
  F x * tiltKernel v t x

/-- Pointwise derivative (in `t`) of the integrand (parametrized by `x`). -/
lemma hasDerivAt_gaussianTiltIntegrand
    (v : ℝ≥0) (F : ℝ → ℝ) (x t : ℝ) :
  HasDerivAt (fun s => gaussianTiltIntegrand F v s x)
    (F x * (x - (v:ℝ) * t) * tiltKernel v t x) t := by
  simpa [gaussianTiltIntegrand] using
    hasDerivAt_F_mul_tiltKernel v F x t

/-- Pointwise derivative (in `t`) at `0` of the integrand: `F x * x`. -/
lemma hasDerivAt_gaussianTiltIntegrand_at0
    (v : ℝ≥0) (F : ℝ → ℝ) (x : ℝ) :
  HasDerivAt (fun s => gaussianTiltIntegrand F v s x)
    (F x * x) 0 := by
  simpa [gaussianTiltIntegrand] using
    hasDerivAt_F_mul_tiltKernel_at0 v F x

/-! ### Refined uniform bounds for the tilt kernel (replacing the coarse placeholder)

We give standard (sharp enough) analytic inequalities used to justify dominated
convergence.  No ad–hoc `nlinarith` placeholders remain.
-/

/-- Basic upper bound: the exponential tilt never exceeds `exp (|t| |x|)`. -/
lemma tiltKernel_le_exp_abs (v : ℝ≥0) (t x : ℝ) :
  tiltKernel v t x ≤ Real.exp (|t| * |x|) := by
  have hineq :
      t * x - (v:ℝ) * t^2 / 2 ≤ |t| * |x| := by
    have hx : t * x ≤ |t| * |x| := by
      have := abs_mul t x
      exact (le_abs_self _).trans (by simp [abs_mul])
    have : t * x - (v:ℝ) * t^2 / 2 ≤ t * x := by
      have : 0 ≤ (v:ℝ) * t^2 / 2 := by
        have : 0 ≤ (v:ℝ) := v.property
        have : 0 ≤ t^2 := by nlinarith
        nlinarith
      linarith
    exact this.trans hx
  simpa [tiltKernel] using (Real.exp_le_exp.mpr hineq)

/-- Triangle inequality in the form used later. -/
lemma abs_add_le_abs_add_abs (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add_le _ _

/-- Positive–increment representation: for `a > 0`,
`exp a - 1 = a * exp c` for some `c ∈ (0,a)`. -/
lemma exp_sub_one_pos_rep {a : ℝ} (h : 0 < a) :
    ∃ c ∈ Set.Ioo 0 a, Real.exp a - 1 = a * Real.exp c := by
  have hcont : ContinuousOn Real.exp (Icc 0 a) := Real.continuous_exp.continuousOn
  have hder : ∀ x ∈ Ioo 0 a, HasDerivAt Real.exp (Real.exp x) x :=
    by intro x _; exact Real.hasDerivAt_exp x
  obtain ⟨c, hcIoo, hcEq⟩ :=
    exists_hasDerivAt_eq_slope (f := Real.exp) (f' := fun x => Real.exp x)
      (a := 0) (b := a) h hcont hder
  have hEq' : Real.exp a - 1 = a * Real.exp c := by
    have : Real.exp c = (Real.exp a - 1) / a := by
      simp [hcEq, sub_eq_add_neg]
    have ha : a ≠ 0 := ne_of_gt h
    field_simp [this, ha] at *; exact id (Eq.symm this)
  exact ⟨c, hcIoo, hEq'⟩

/-- Negative–increment representation: for `a < 0`,
`exp a - 1 = a * exp c` for some `c ∈ (a,0)`. -/
lemma exp_sub_one_neg_rep {a : ℝ} (h : a < 0) :
    ∃ c ∈ Set.Ioo a 0, Real.exp a - 1 = a * Real.exp c := by
  have hcont : ContinuousOn Real.exp (Icc a 0) := Real.continuous_exp.continuousOn
  have hder : ∀ x ∈ Ioo a 0, HasDerivAt Real.exp (Real.exp x) x :=
    by intro x _; exact Real.hasDerivAt_exp x
  obtain ⟨c, hcIoo, hcEq⟩ :=
    exists_hasDerivAt_eq_slope (f := Real.exp) (f' := fun x => Real.exp x)
      (a := a) (b := 0) h hcont hder
  have ha0 : a ≠ 0 := ne_of_lt h
  have hEq' : Real.exp a - 1 = a * Real.exp c := by
    have h1 : Real.exp c = (1 - Real.exp a)/(-a) := by
      simpa [sub_eq_add_neg] using hcEq
    have hflip : (1 - Real.exp a)/(-a) = (Real.exp a - 1)/a := by
      have htmp : (1 - Real.exp a)/(-a) = -(1 - Real.exp a)/a := by
        field_simp [ha0, sub_eq_add_neg]
      have hnum : -(1 - Real.exp a) = Real.exp a - 1 := by
        simp
      simp [htmp, hnum]
    have hExpc : Real.exp c = (Real.exp a - 1)/a := by
      simpa [hflip] using h1
    have : a * Real.exp c = Real.exp a - 1 := by
      field_simp [ha0, hExpc]; grind
    exact this.symm
  exact ⟨c, hcIoo, hEq'⟩

/-- Sharp inequality `|exp a - 1| ≤ |a| * exp |a|`. -/
lemma abs_exp_sub_one_le_abs_mul_exp (a : ℝ) :
    |Real.exp a - 1| ≤ |a| * Real.exp |a| := by
  classical
  by_cases h0 : a = 0
  · subst h0; simp
  have hsign : 0 < a ∨ a < 0 := lt_or_gt_of_ne (ne_comm.mp h0)
  rcases hsign with hpos | hneg
  · -- a > 0
    rcases exp_sub_one_pos_rep hpos with ⟨c, hcIoo, hRep⟩
    have hAbs : |Real.exp a - 1| = |a| * Real.exp c := by
      simp [hRep, abs_mul, abs_of_pos hpos]
    have hc_le : c ≤ a := (Set.mem_Ioo.1 hcIoo).2.le
    have hMon : Real.exp c ≤ Real.exp a := Real.exp_le_exp.mpr hc_le
    have : Real.exp c ≤ Real.exp |a| := by simpa [abs_of_pos hpos]
    calc
      |Real.exp a - 1| = |a| * Real.exp c := hAbs
      _ ≤ |a| * Real.exp |a| := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · -- a < 0
    rcases exp_sub_one_neg_rep hneg with ⟨c, hcIoo, hRep⟩
    have hAbs : |Real.exp a - 1| = |a| * Real.exp c := by
      simp [hRep, abs_mul, abs_of_neg hneg]
    have hc_le0 : c ≤ 0 := (Set.mem_Ioo.1 hcIoo).2.le
    have hLe0 : Real.exp c ≤ Real.exp 0 := Real.exp_le_exp.mpr hc_le0
    have h0Le : Real.exp 0 ≤ Real.exp |a| := by
      have : |a| = -a := abs_of_neg hneg
      have : 0 ≤ -a := neg_nonneg.mpr (le_of_lt hneg)
      simp
    have hMon : Real.exp c ≤ Real.exp |a| := hLe0.trans h0Le
    calc
      |Real.exp a - 1| = |a| * Real.exp c := hAbs
      _ ≤ |a| * Real.exp |a| := mul_le_mul_of_nonneg_left hMon (abs_nonneg _)

/-- Monotonicity of division by a nonnegative (possibly zero) real.  (If the
denominator is zero both sides are zero in a field, so the inequality holds.) -/
lemma div_le_div_of_le_of_nonneg {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) :
  a / c ≤ b / c := by
  have : 0 ≤ c⁻¹ := inv_nonneg.mpr hc
  simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_right h this)

/-- Commuting variant of `mul_div_cancel'`. -/
lemma mul_div_cancel_left' {G : Type*} [CommGroupWithZero G] (a : G) {b : G} (hb : b ≠ 0) :
  b * a / b = a := by
  rw [mul_comm];rw [propext (div_eq_iff_mul_eq hb)]

/-! ### Difference–quotient bounds for the tilt kernel  -/
/-- Absolute-value bound on the exponent of the Gaussian tilt kernel.  -/
lemma abs_tiltExponent_bound (v : ℝ≥0) (t x : ℝ) :
    |t * x - (v:ℝ) * t^2 / 2| ≤ |t| * |x| + (v:ℝ) * t^2 / 2 := by
  have hx : |t * x| = |t| * |x| := by simp [abs_mul]
  have hv : 0 ≤ (v:ℝ) * t^2 / 2 := by
    have hv' : 0 ≤ (v:ℝ) := v.property
    have ht2 : 0 ≤ t^2 := sq_nonneg _
    have : 0 ≤ (v:ℝ) * t^2 := mul_nonneg hv' ht2
    exact (div_nonneg this (by norm_num))
  have hAbsV : |(v:ℝ) * t^2 / 2| = (v:ℝ) * t^2 / 2 := by
    simp [abs_of_nonneg hv]
  have hAbsVneg : |-(v:ℝ) * t^2 / 2| = (v:ℝ) * t^2 / 2 := by
    have h' : (-(v:ℝ) * t^2 / 2) = -((v:ℝ) * t^2 / 2) := by ring
    simp
    aesop
  calc
    |t * x - (v:ℝ) * t^2 / 2|
        = |t * x + (-(v:ℝ) * t^2 / 2)| := by ring_nf
    _ ≤ |t * x| + |-(v:ℝ) * t^2 / 2| := abs_add_le _ _
    _ = |t| * |x| + (v:ℝ) * t^2 / 2 := by
          simp [hx]
          aesop

/-- Algebraic factorization of the tilt exponent. -/
lemma tiltExponent_factor (v : ℝ≥0) (t x : ℝ) :
    t * x - (v:ℝ) * t^2 / 2 = t * (x - (v:ℝ) * t / 2) := by
  ring

/-- Cancellation lemma giving the normalized absolute value after factoring. -/
lemma abs_tiltExponent_div_eq (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    |t * x - (v:ℝ) * t^2 / 2| / |t| = |x - (v:ℝ) * t / 2| := by
  have hfac := tiltExponent_factor (v := v) (t := t) (x := x)
  have hne : |t| ≠ 0 := abs_ne_zero.mpr ht
  simp [hfac, abs_mul, hne]

/-- Absolute value of the scaled term `|(v) * t / 2|`. -/
lemma abs_nnreal_mul_div_two (v : ℝ≥0) (t : ℝ) :
    |(v:ℝ) * t / 2| = (v:ℝ) * |t| / 2 := by
  have hv : 0 ≤ (v:ℝ) := v.property
  have h1 : |((v:ℝ) * t) / 2| = |(v:ℝ) * t| / |2| := abs_div _ _
  have h2 : |(v:ℝ) * t| = (v:ℝ) * |t| := by
    simp [abs_mul, abs_of_nonneg hv, mul_comm]
  have h3 : |2| = (2:ℝ) := by norm_num
  simpa [h2, h3] using h1

/-- Triangle-type bound specialized to the inner expression. (Fixed version) -/
lemma abs_x_sub_vt_half_le (v : ℝ≥0) (t x : ℝ) :
    |x - (v:ℝ) * t / 2| ≤ |x| + (v:ℝ) * |t| / 2 := by
  have h₁ : |x - (v:ℝ) * t / 2| ≤ |x| + |(v:ℝ) * t / 2| := by
    have hrewrite : x - (v:ℝ) * t / 2 = x + (-((v:ℝ) * t / 2)) := by ring
    simpa [hrewrite, abs_neg] using
      (abs_add_le x (-((v:ℝ) * t / 2)))
  have h₂ : |(v:ℝ) * t / 2| = (v:ℝ) * |t| / 2 :=
    abs_nnreal_mul_div_two v t
  simpa [h₂, add_comm, add_left_comm, add_assoc] using h₁

/-- Main divided bound reduced to the inner absolute value (nonzero `t`). -/
lemma abs_tiltExponent_div_le_inner (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    |t * x - (v:ℝ) * t^2 / 2| / |t| ≤ |x - (v:ℝ) * t / 2| := by
  simp [abs_tiltExponent_div_eq (v := v) ht]

/-- Final divided bound (original statement), now factored through helper lemmas. -/
lemma abs_tiltExponent_div_bound (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    |t * x - (v:ℝ) * t^2 / 2| / |t| ≤ |x| + (v:ℝ) * |t| / 2 := by
  calc
    |t * x - (v:ℝ) * t^2 / 2| / |t|
        ≤ |x - (v:ℝ) * t / 2| := abs_tiltExponent_div_le_inner (v := v) ht
    _ ≤ |x| + (v:ℝ) * |t| / 2 := abs_x_sub_vt_half_le (v := v) (t := t) (x := x)

/-- Exponential bound on the absolute-value exponent. -/
lemma exp_abs_tiltExponent_bound (v : ℝ≥0) (t x : ℝ) :
  Real.exp |t * x - (v:ℝ) * t^2 / 2|
    ≤ Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
  exact Real.exp_le_exp.mpr (abs_tiltExponent_bound v t x)

/-! ### Difference–quotient bounds for the exponential -/

/-- Generic bound on the difference–quotient of the exponential function.
No Gaussian parameters appear here. -/
lemma abs_exp_sub_one_div_le (a t : ℝ) (ht : t ≠ 0) :
    |(Real.exp a - 1) / t| ≤ |a| / |t| * Real.exp |a| := by
  have h₁ : |Real.exp a - 1| ≤ |a| * Real.exp |a| :=
    abs_exp_sub_one_le_abs_mul_exp a
  have hpos : 0 < |t| := abs_pos.mpr ht
  have h₂ : |Real.exp a - 1| / |t| ≤ |a| * Real.exp |a| / |t| :=
    (div_le_div_of_le_of_nonneg h₁ (le_of_lt hpos))
  have h₃ : |(Real.exp a - 1) / t| ≤ |a| * Real.exp |a| / |t| := by
    simpa [abs_div] using h₂
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h₃

/-- Tilt-specific algebraic step: bounding the factor `|a| / |t|`
by a *linear–quadratic* expression in `x` and `|t|`.  This is exactly the
content of `abs_tiltExponent_div_bound`, but we expose it under the shorter
name `abs_tiltExponent_div_le_linQuad`. -/
lemma abs_tiltExponent_div_le_linQuad
    (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    let a : ℝ := t * x - (v:ℝ) * t^2 / 2;
    |a| / |t| ≤ |x| + (v:ℝ) * |t| / 2 := by
  intro a
  have := abs_tiltExponent_div_bound (v := v) (t := t) (x := x) ht
  simpa [a] using this

/-! ### Core difference–quotient bound  -/

/-- Core bound for the centred difference quotient of the **Gaussian tilt
kernel** -/
lemma tiltKernel_diffquot_bound_core
    (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v:ℝ) * |t| / 2)
        * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
  set a : ℝ := t * x - (v:ℝ) * t^2 / 2
  have h₁ := abs_exp_sub_one_div_le a t ht
  have h₂ := abs_tiltExponent_div_le_linQuad (v := v) (t := t) (x := x) ht
  have h₃ : Real.exp |a| ≤ Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) :=
    exp_abs_tiltExponent_bound v t x
  calc
    |(tiltKernel v t x - 1) / t|
        = |(Real.exp a - 1) / t| := by
            simp [tiltKernel, a]
    _ ≤ (|a| / |t|) * Real.exp |a| := by
            simpa [mul_comm] using h₁
    _ ≤ (|x| + (v:ℝ) * |t| / 2) * Real.exp |a| := by
            gcongr;
    _ ≤ (|x| + (v:ℝ) * |t| / 2)
          * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
            gcongr;

/-- Uniform-in-x difference–quotient bound (all t, including 0). -/
lemma tiltKernel_diffquot_bound (v : ℝ≥0) (t x : ℝ) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v:ℝ) * |t| / 2)
        * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
  by_cases ht : t = 0
  · subst ht
    have : 0 ≤ (|x| + (v:ℝ) * 0 / 2)
        * Real.exp (0 * |x| + (v:ℝ) * 0^2 / 2) := by positivity
    simp [tiltKernel]
  · exact tiltKernel_diffquot_bound_core v ht

lemma tiltKernel_diffquot_bound_of_le (v : ℝ≥0) {t x δ : ℝ}
    (hδ : 0 ≤ δ) (ht : |t| ≤ δ) :
  |(tiltKernel v t x - 1) / t|
      ≤ (|x| + (v:ℝ) * δ / 2)
          * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) := by
  have hcore := tiltKernel_diffquot_bound v t x
  have hFactor :
      |x| + (v:ℝ) * |t| / 2 ≤ |x| + (v:ℝ) * δ / 2 := by
    have hvnon : 0 ≤ (v:ℝ) := v.property
    have h_mul : (v:ℝ) * |t| ≤ (v:ℝ) * δ :=
      mul_le_mul_of_nonneg_left ht hvnon
    have h_half :
        (v:ℝ) * |t| / 2 ≤ (v:ℝ) * δ / 2 := by
      have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using mul_le_mul_of_nonneg_right h_mul this
    exact (add_le_add_iff_left |x|).mpr h_half
  have hExpArg :
      |t| * |x| + (v:ℝ) * t^2 / 2
        ≤ δ * |x| + (v:ℝ) * δ^2 / 2 := by
    have h1 : |t| * |x| ≤ δ * |x| :=
      mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    have h_sq : t^2 ≤ δ^2 := by
      have h_abs : |t| ≤ δ := ht
      have habs : |t| ≤ |δ| := by
        simpa [abs_of_nonneg hδ] using h_abs
      simpa using (sq_le_sq).mpr habs
    have h2_base : (v:ℝ) * t^2 ≤ (v:ℝ) * δ^2 :=
      mul_le_mul_of_nonneg_left h_sq (by exact v.property)
    have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
    have h2 :
        (v:ℝ) * t^2 / 2 ≤ (v:ℝ) * δ^2 / 2 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using mul_le_mul_of_nonneg_right h2_base this
    linarith
  have hExpMono :
      Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2)
        ≤ Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) :=
    Real.exp_le_exp.mpr hExpArg
  have hpos₁ : 0 ≤ Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by positivity
  have hpos₂ : 0 ≤ Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) := by positivity
  calc
    |(tiltKernel v t x - 1) / t|
        ≤ (|x| + (v:ℝ) * |t| / 2)
            * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := hcore
    _ ≤ (|x| + (v:ℝ) * δ / 2)
            * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) := by
      have h_comb :
          (|x| + (v:ℝ) * |t| / 2)
              * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2)
            ≤ (|x| + (v:ℝ) * δ / 2)
              * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) :=
        mul_le_mul hFactor hExpMono
          hpos₁
          (by
            have habs : 0 ≤ |x| := abs_nonneg _
            have hvδ : 0 ≤ (v:ℝ) * δ / 2 := by
              have hv : 0 ≤ (v:ℝ) := v.property
              have hδ' : 0 ≤ δ := hδ
              nlinarith
            nlinarith)
      simpa using h_comb

/-- Final pointwise δ–bound (public version). -/
lemma tiltKernel_diffquot_pointwise_bound
    (v : ℝ≥0) {δ t x : ℝ} (hδ : 0 ≤ δ) (ht : |t| ≤ δ) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v:ℝ) * δ / 2)
        * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) :=
  tiltKernel_diffquot_bound_of_le v hδ ht

/-! ### Uniform‐in‐`t` bounds -/

/-- `|t| ≤ δ` happens eventually in the neighbourhood of `0` (any `δ > 0`). -/
lemma eventually_abs_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| ≤ δ := by
  have hOpen : IsOpen {t : ℝ | |t| < δ} :=
    isOpen_lt continuous_abs continuous_const
  have hMem : (0 : ℝ) ∈ {t : ℝ | |t| < δ} := by simp [hδ]
  have hNhds : {t : ℝ | |t| < δ} ∈ 𝓝 (0 : ℝ) :=
    hOpen.mem_nhds hMem
  filter_upwards [hNhds] with t ht
  exact (le_of_lt ht)

/-- Upgrade the exponent
    `exp (δ |x| + v δ² / 2) ≤ exp (v δ / 2) · exp (δ |x|)`
whenever `0 ≤ v` and `δ ∈ (0,1]`. This is the only non-trivial analytic step
needed in the uniform bound. -/
lemma exp_factor_le_product
    (v : ℝ≥0) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) (x : ℝ) :
    Real.exp (δ * |x| + (v : ℝ) * δ^2 / 2)
      ≤ Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  have hδsq : δ^2 ≤ δ := by
    have : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ₁ (le_of_lt hδ₀)
    simpa [pow_two] using this
  have hv : 0 ≤ (v : ℝ) := v.property
  have hMul : (v : ℝ) * δ^2 ≤ (v : ℝ) * δ := mul_le_mul_of_nonneg_left hδsq hv
  have hExpArg :
      δ * |x| + (v : ℝ) * δ^2 / 2
        ≤ δ * |x| + (v : ℝ) * δ / 2 := by
    have : (v : ℝ) * δ^2 / 2 ≤ (v : ℝ) * δ / 2 := by
      nlinarith [hMul]
    linarith
  have := Real.exp_le_exp.mpr hExpArg
  simpa [Real.exp_add, mul_comm, mul_left_comm, mul_assoc] using this

/-- Enhanced *pointwise* δ–bound (linear-quadratic ↝ linear × exp) that will
be used in the uniform lemma. -/
lemma tiltKernel_diffquot_pointwise_bound'
    (v : ℝ≥0) {δ t x : ℝ} (hδ : 0 ≤ δ) (ht : |t| ≤ δ)
    (hδ₁ : δ ≤ 1) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v : ℝ) * δ / 2)
        * Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  have h₀ :=
    tiltKernel_diffquot_pointwise_bound (v := v) (δ := δ) (t := t) (x := x) hδ ht
  by_cases hδ0 : δ = 0
  · subst hδ0
    simpa using h₀
  · have hδpos : 0 < δ := lt_of_le_of_ne' hδ hδ0
    have hExpUpgrade :
        Real.exp (δ * |x| + (v : ℝ) * δ^2 / 2)
          ≤ Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) :=
      exp_factor_le_product v hδpos hδ₁ x
    have hlin : 0 ≤ |x| + (v : ℝ) * δ / 2 := by
      have hx : 0 ≤ |x| := abs_nonneg _
      have hvδ : 0 ≤ (v : ℝ) * δ / 2 := by
        have hv : 0 ≤ (v : ℝ) := v.property
        have hδ' : 0 ≤ δ := hδ
        have hmul : 0 ≤ (v : ℝ) * δ := mul_nonneg hv hδ'
        exact div_nonneg hmul (by norm_num)
      exact add_nonneg hx hvδ
    have hMul :
        (|x| + (v : ℝ) * δ / 2) * Real.exp (δ * |x| + (v : ℝ) * δ^2 / 2)
          ≤ (|x| + (v : ℝ) * δ / 2)
              * (Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|)) :=
      mul_le_mul_of_nonneg_left hExpUpgrade hlin
    exact (le_trans h₀ (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hMul))

/-- *Elementary* eventual property:
`(∀ᶠ t, |t| ≤ δ)` together with the enhanced pointwise bound. -/
lemma eventually_diffquot_enhanced
    (v : ℝ≥0) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
  ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    ∀ x,
      |(tiltKernel v t x - 1) / t|
        ≤ (|x| + (v : ℝ) * δ / 2)
            * Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  have hSmall := eventually_abs_le δ hδ₀
  filter_upwards [hSmall] with t ht_small
  refine And.intro ht_small ?_
  intro x
  have :=
    tiltKernel_diffquot_pointwise_bound' (v := v) (δ := δ) (t := t) (x := x)
      (hδ := (le_of_lt hδ₀)) (ht := ht_small) hδ₁
  simpa using this

/-! ### Uniform bound -/

/-- Uniform (in `t` close to `0`) *exponential–linear* bound on the centred
difference quotient of the Gaussian tilt kernel.  This is now just a thin
wrapper around the auxiliary lemmas above. -/
lemma tiltKernel_diffquot_uniform_bound
    (v : ℝ≥0) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
  ∀ᶠ t in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    ∀ x,
      |(tiltKernel v t x - 1) / t|
        ≤ (|x| + (v : ℝ) * δ / 2)
            * Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) :=
  eventually_diffquot_enhanced v δ hδ₀ hδ₁

/-- Final domination lemma (state-of-art version):
For any fixed `δ ∈ (0,1]`, and any function `F`, for `|t| ≤ δ` we have
  | (F x * tiltKernel v t x - F x) / t |
    ≤ |F x| * (|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|).

Uses the uniform kernel difference–quotient bound and a simple factorization. -/
lemma gaussianTilt_diffquot_dom
    (v : ℝ≥0) (F : ℝ → ℝ)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
  ∀ᶠ t in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    ∀ x,
      |(F x * tiltKernel v t x - F x) / t|
        ≤ |F x| * (|x| + (v:ℝ) * δ / 2)
            * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  refine (tiltKernel_diffquot_uniform_bound v δ hδ₀ hδ₁).mono ?_
  intro t ht
  refine And.intro ht.left ?_
  intro x
  have hcore := ht.right x
  have hfact : F x * tiltKernel v t x - F x = F x * (tiltKernel v t x - 1) := by ring
  calc
    |(F x * tiltKernel v t x - F x) / t|
        = |(F x * (tiltKernel v t x - 1)) / t| := by aesop
    _ = |F x| * |(tiltKernel v t x - 1) / t| := by
          simp [div_eq_mul_inv, abs_mul, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ |F x| * ((|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|)) :=
          mul_le_mul_of_nonneg_left hcore (abs_nonneg _)
    _ = |F x| * (|x| + (v:ℝ) * δ / 2)
          * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|) := by
          ring_nf

/-!
## Moderate growth shortcut

To ease usage of the Gaussian integration by parts lemma, we introduce a (very
simple) predicate `HasModerateGrowth F` asserting polynomial growth bounds on
`F` and its derivative.  From this, integrability of the required functions
under a (centered) Gaussian measure follows, so the user does not have to
establish the integrability hypotheses manually each time.

-/

/-- `HasModerateGrowth F` means that `F` and its (real) derivative grow at most
polynomially: there are constants `C` and an exponent `m` such that both
`|F x|` and `|deriv F x|` are bounded by `C (1 + |x|)^m`.  This (very) classical
condition implies integrability of the functions we need against a Gaussian
measure. -/
def HasModerateGrowth (F : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), 0 < C ∧
    (∀ x, |F x| ≤ C * (1 + |x|)^m) ∧
    (∀ x, |deriv F x| ≤ C * (1 + |x|)^m)

/-- All absolute moments `|x|^k` are integrable under any centered real Gaussian. -/
lemma integrable_abs_pow_gaussianReal_centered
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  cases k with
  | zero =>
      have h : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 v) :=
        integrable_const (μ := gaussianReal 0 v) (c := (1 : ℝ))
      simp [pow_zero]
  | succ k =>
      have hmem :
          MemLp id ((Nat.succ k : ℝ≥0∞)) (gaussianReal 0 v) :=
        memLp_id_gaussianReal' (μ := 0) (v := v)
          (p := (Nat.succ k : ℝ≥0∞)) (by simp)
      have hInt_norm_rpow :
          Integrable
            (fun x : ℝ => ‖(fun y : ℝ => y) x‖ ^ (((Nat.succ k : ℝ≥0∞)).toReal))
            (gaussianReal 0 v) := by
        simpa using
          hmem.integrable_norm_rpow (by simp : ((Nat.succ k : ℝ≥0∞)) ≠ 0)
      have hInt_abs_rpow :
          Integrable (fun x : ℝ => |x| ^ (((Nat.succ k : ℝ≥0∞)).toReal))
            (gaussianReal 0 v) := by
        simpa [Real.norm_eq_abs] using hInt_norm_rpow
      have h_toNat :
              (fun x : ℝ => |x| ^ (((Nat.succ k : ℝ≥0∞)).toReal))
                =ᵐ[gaussianReal 0 v] (fun x : ℝ => |x| ^ (Nat.succ k)) := by
            have ht : (((Nat.succ k : ℝ≥0∞)).toReal) = (Nat.succ k : ℝ) := by
              aesop
            exact ae_of_all (gaussianReal 0 v) (fun x => by
              have hx : 0 ≤ |x| := abs_nonneg x
              rw [ht]
              exact rpow_natCast |x| k.succ)
      exact (hInt_abs_rpow.congr h_toNat)

/-- Polynomial moment `(1 + |x|)^k` integrable under any centered real Gaussian. -/
lemma integrable_one_add_abs_pow_gaussianReal_centered
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) := by
  classical
  have hpow :
      (fun x : ℝ => (1 + |x|)^k)
        =
      (fun x : ℝ =>
        ∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ) * |x| ^ j) := by
    funext x
    have : (1 + |x|)^k = (|x| + 1)^k := by
      ring
    simpa [this, one_pow, mul_comm, mul_left_comm, mul_assoc]
      using (add_pow |x| (1 : ℝ) k)
  rw [hpow]
  refine
    integrable_finset_sum
        (s := Finset.range (k + 1)) (μ := gaussianReal 0 v) ?_
  intro j hj
  have hjInt : Integrable (fun x : ℝ => |x| ^ j) (gaussianReal 0 v) :=
    integrable_abs_pow_gaussianReal_centered v j
  let Δ : ℝ := (Nat.choose k j : ℝ)
  have : Integrable (fun x : ℝ => Δ * |x| ^ j) (gaussianReal 0 v) :=
    hjInt.const_mul Δ
  simpa [Δ, mul_comm, mul_left_comm, mul_assoc] using this

/-- A measurable‐version of the moderate‐growth ⇒ integrability lemma. -/
theorem HasModerateGrowth.integrable_pair'
    {F : ℝ → ℝ} {v : ℝ≥0} (hF : HasModerateGrowth F)
    (hF_meas : AEStronglyMeasurable F (gaussianReal 0 v))
    (hF'_meas : AEStronglyMeasurable (fun x => deriv F x) (gaussianReal 0 v)) :
    Integrable (fun x => x * F x) (gaussianReal 0 v)
      ∧ Integrable (fun x => deriv F x) (gaussianReal 0 v) := by
  rcases hF with ⟨C, m, hCpos, hFbound, hF'bound⟩
  have hMom_m  : Integrable (fun x : ℝ => (1 + |x|)^m)     (gaussianReal 0 v) :=
    integrable_one_add_abs_pow_gaussianReal_centered v m
  have hMom_mp1 : Integrable (fun x : ℝ => (1 + |x|)^(m+1)) (gaussianReal 0 v) :=
    integrable_one_add_abs_pow_gaussianReal_centered v (m + 1)
  have hInt_dF : Integrable (fun x => deriv F x) (gaussianReal 0 v) := by
    refine Integrable.mono' ((hMom_m).const_mul C) hF'_meas ?_
    refine ae_of_all _ (fun x => ?_)
    have hCle : 0 ≤ C := le_of_lt hCpos
    simpa [Real.norm_eq_abs, abs_of_nonneg hCle,
      mul_comm, mul_left_comm, mul_assoc] using (hF'bound x)
  have h_xF_meas :
      AEStronglyMeasurable (fun x : ℝ => x * F x) (gaussianReal 0 v) :=
    (aestronglyMeasurable_id.mul hF_meas)
  have hInt_xF : Integrable (fun x => x * F x) (gaussianReal 0 v) := by
    refine Integrable.mono' ((hMom_mp1).const_mul C) h_xF_meas ?_
    refine ae_of_all _ (fun x => ?_)
    have hCle : 0 ≤ C := le_of_lt hCpos
    -- `|x| ≤ 1 + |x|`
    have hx_le : |x| ≤ 1 + |x| := by
      have := abs_nonneg x; linarith
    -- `|x| * (1 + |x|)^m ≤ (1 + |x|)^(m+1)`
    have hx_pow :
        |x| * (1 + |x|)^m ≤ (1 + |x|)^(m + 1) := by
      have hbase : 0 ≤ (1 + |x|)^m :=
        pow_nonneg (by have := abs_nonneg x; linarith) _
      have := mul_le_mul_of_nonneg_right hx_le hbase
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    have hFx : |F x| ≤ C * (1 + |x|)^m := hFbound x
    have h1 : |x| * |F x| ≤ |x| * (C * (1 + |x|)^m) :=
      mul_le_mul_of_nonneg_left hFx (abs_nonneg _)
    have h2 : |x| * (C * (1 + |x|)^m) = C * (|x| * (1 + |x|)^m) := by ring
    have h3 : C * (|x| * (1 + |x|)^m) ≤ C * (1 + |x|)^(m + 1) :=
      mul_le_mul_of_nonneg_left hx_pow hCle
    have : |x * F x| ≤ C * (1 + |x|)^(m + 1) := by
      calc
        |x * F x| = |x| * |F x| := by simp [abs_mul]
        _ ≤ |x| * (C * (1 + |x|)^m) := h1
        _ = C * (|x| * (1 + |x|)^m) := h2
        _ ≤ C * (1 + |x|)^(m + 1)   := h3
    exact this

  exact ⟨hInt_xF, hInt_dF⟩

theorem HasModerateGrowth.integrable_pair
    {F : ℝ → ℝ} {v : ℝ≥0} (hF : HasModerateGrowth F)
    (hF_meas : AEStronglyMeasurable F (gaussianReal 0 v))
    (hF'_meas : AEStronglyMeasurable (fun x => deriv F x) (gaussianReal 0 v)) :
    Integrable (fun x => x * F x) (gaussianReal 0 v)
      ∧ Integrable (fun x => deriv F x) (gaussianReal 0 v) :=
  HasModerateGrowth.integrable_pair' (v := v) hF hF_meas hF'_meas

section DominationExponentialUpgrade

variable {v : ℝ≥0} {δ : ℝ}

/-! ### Elementary linear–quadratic “Young” bounds  -/

section YoungBounds

open Real

/-- Core algebraic inequality
`4 v δ |x| ≤ |x|² + 4 v² δ²`, obtained from the non-negativity of
`(|x| − 2 v δ)²`.  Only the assumption `0 < v : ℝ` is needed. -/
lemma four_mul_mul_le_sq_add_sq
    {v δ x : ℝ} (_ : 0 < v) :
    4 * v * δ * |x| ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 := by
  have hsq : 0 ≤ (|x| - 2 * v * δ) ^ 2 := by
    exact sq_nonneg _
  have hsq_exp : (|x| - 2 * v * δ) ^ 2 =
      |x| ^ 2 - 4 * v * δ * |x| + 4 * v ^ 2 * δ ^ 2 := by ring
  have : 4 * v * δ * |x| ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 := by
    -- `0 ≤ A - B`  ⇒  `B ≤ A`.
    have : 0 ≤ |x| ^ 2 - 4 * v * δ * |x| + 4 * v ^ 2 * δ ^ 2 := by
      simpa [hsq_exp] using hsq
    linarith
  simpa using this

/-- “Young” inequality in *undivided* form
`4 v δ |x| ≤ |x|² + 4 v² δ²`. -/
lemma young_linear_quadratic_mul
    {v δ x : ℝ} (hv : 0 < v) :
    4 * v * δ * |x| ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 :=
  four_mul_mul_le_sq_add_sq hv

namespace Real

open Real

lemma div_le_iff_of_pos {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b c : α} (hc : 0 < c) :
    a ≤ b / c ↔ a * c ≤ b := by
  simp [div_eq_mul_inv]
  rw [@le_iff_le_iff_lt_iff_lt]
  exact mul_inv_lt_iff₀ hc

end Real
open Real


section YoungBounds

open Real

/-- Divided Young inequality
`δ |x| ≤ |x|² /(4 v) + v δ²` (with `v > 0`). -/
lemma young_linear_quadratic_div
    {v δ x : ℝ} (hv : 0 < v) :
    δ * |x| ≤ |x| ^ 2 / (4 * v) + v * δ ^ 2 := by
  have h₀ := young_linear_quadratic_mul (v := v) (δ := δ) (x := x) hv
  have hpos : 0 < 4 * v := by
    have : (0 : ℝ) < 4 := by norm_num
    exact mul_pos this hv
  have h₁ : δ * |x| ≤ (|x| ^ 2 + 4 * v ^ 2 * δ ^ 2) / (4 * v) := by
    have hmul : (δ * |x|) * (4 * v) ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h₀
    exact (div_le_iff_of_pos hpos).mpr hmul
  have h_split :
      (|x| ^ 2 + 4 * v ^ 2 * δ ^ 2) / (4 * v)
        = |x| ^ 2 / (4 * v) + v * δ ^ 2 := by
    field_simp [mul_comm, mul_left_comm, mul_assoc]
  aesop

/-- **Young inequality (Gaussian form) for `ℝ≥0` variance**. -/
lemma young_linear_quadratic_bound
    (x δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    δ * |x| ≤ |x|^2 / (4 * (v : ℝ)) + (v : ℝ) * δ^2 := by
  have hv_pos : 0 < (v : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hv)
  simpa using (young_linear_quadratic_div (x := x) (δ := δ) hv_pos)

/-- Exponential linear-vs-quadratic domination (explicit constant):
for `v > 0` we have
  exp (δ |x|) ≤ exp ( (v:ℝ) * δ^2 ) * exp ( |x|^2 / (4 v) ). -/
lemma exp_abs_linear_le_gaussian_aux
    (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∀ x, Real.exp (δ * |x|)
        ≤ Real.exp ((v:ℝ) * δ^2) * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
  intro x
  have h := young_linear_quadratic_bound x δ v hv
  have : δ * |x| ≤ (|x|^2) / (4 * (v:ℝ)) + (v:ℝ) * δ^2 := by aesop
  have hExp := Real.exp_le_exp.mpr this
  simpa [Real.exp_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using hExp

/-- Polynomial growth control transferred to the profile used in
`gaussianTilt_diffquot_dom_integrable`: from moderate growth of `F` we get
a bound of the form
  |F x| * (|x| + 1) ≤ C' * (1 + |x|)^{m+1}. -/
lemma HasModerateGrowth.bound_F_mul_linear
    {F : ℝ → ℝ} (hF : HasModerateGrowth F) :
  ∃ (C : ℝ) (m : ℕ) (_ : 0 < C),
    ∀ x, |F x| * (|x| + 1) ≤ C * (1 + |x|)^(m+1) := by
  rcases hF with ⟨C, m, hCpos, hFbound, _⟩
  have h₂ : ∀ x, |F x| * (|x| + 1) ≤ (C * 2) * (1 + |x|)^(m+1) := by
    intro x
    have hF' := hFbound x
    have hlin : (|x| + 1) ≤ 2 * (1 + |x|) := by nlinarith [abs_nonneg x]
    have : |F x| * (|x| + 1) ≤ |F x| * (2 * (1 + |x|)) :=
      mul_le_mul_of_nonneg_left hlin (abs_nonneg _)
    have : |F x| * (|x| + 1) ≤ 2 * |F x| * (1 + |x|) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hFpow :
        |F x| ≤ C * (1 + |x|)^m := hF'
    have : 2 * |F x| * (1 + |x|) ≤ 2 * (C * (1 + |x|)^m) * (1 + |x|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFpow (by norm_num))
        (by nlinarith [abs_nonneg x])
    have hpow :
        2 * (C * (1 + |x|)^m) * (1 + |x|)
          = (C * 2) * (1 + |x|)^(m+1) := by
          simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
    have := le_trans this (by
    aesop)
    have hstep :
        |F x| * (|x| + 1) ≤ 2 * C * (1 + |x|)^(m+1) := by
      have h1 :
          |F x| * (|x| + 1) ≤ 2 * |F x| * (1 + |x|) := by
        aesop
      have h2 :
          2 * |F x| * (1 + |x|) ≤ 2 * (C * (1 + |x|)^m) * (1 + |x|) := by aesop
      have h3 :
          2 * (C * (1 + |x|)^m) * (1 + |x|) = 2 * C * (1 + |x|)^(m+1) := by
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
      linarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
  refine ⟨C * 2, m, by nlinarith, h₂⟩

namespace Measure

open MeasureTheory

/-- Any Borel function is integrable with respect to a Dirac measure: the
`L¹`‐norm collapses to the single (finite) value at the support point. -/
lemma integrable_dirac
    {f : ℝ → ℝ} {a : ℝ} (hf : Measurable f) :
    Integrable f (Measure.dirac a) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hEval :
      (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂ Measure.dirac a) =
        (‖f a‖₊ : ℝ≥0∞) := by
    simp
  have : (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂ Measure.dirac a) < ∞ := by
    simp [hEval, show ((‖f a‖₊ : ℝ≥0∞) < ∞) by simp]
  exact this
end Measure
open Measure

/-!
### Structured domination lemmas for `( |x| + B )^k` and Gaussian integrability

We factor the proof of
`Integrable fun x => (|x| + 2)^k * exp (-a * x^2)`
into small reusable lemmas.  The bound is intentionally *coarse* but
polynomial × Gaussian is always integrable, so sharp constants are irrelevant.
-/

section PolyGaussianDomination

namespace Real

/-- Convenience wrapper (ℝ‐specialization) of `pow_le_pow_of_le_left`. -/
lemma pow_le_pow_of_le_left {x y : ℝ} {k : ℕ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    x^k ≤ y^k :=
  pow_le_pow_left₀ hx hxy k

/-- Elementary inequality: `|x| + B ≤ 2 * max B |x|`. -/
lemma abs_add_const_le_two_mul_max (B x : ℝ) :
    |x| + B ≤ 2 * max B |x| := by
  have h₁ : |x| ≤ max B |x| := le_max_right _ _
  have h₂ : B   ≤ max B |x| := le_max_left  _ _
  have h : |x| + B ≤ max B |x| + max B |x| := add_le_add h₁ h₂
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h

/-- Power version (requires nonnegativity of the base):
If `0 ≤ |x| + B` then `( |x| + B)^k ≤ (2)^k * (max B |x|)^k`.  (This
hypothesis is satisfied, for instance, when `0 ≤ B`.) -/
lemma pow_abs_add_const_le_two_pow_mul_max
    (B x : ℝ) (k : ℕ) (hbase : 0 ≤ |x| + B) :
    (|x| + B)^k ≤ (2 : ℝ)^k * (max B |x|)^k := by
  have hineq := abs_add_const_le_two_mul_max B x
  have hpow : (|x| + B)^k ≤ (2 * max B |x|)^k :=
    pow_le_pow_of_le_left hbase hineq
  have hfac : (2 * max B |x|)^k = (2 : ℝ)^k * (max B |x|)^k := by
    simp [mul_comm]
    exact mul_pow (max B |x|) 2 k
  aesop

/-- Convenience specialization of the previous lemma when `B ≥ 0`. -/
lemma pow_abs_add_const_le_two_pow_mul_max_of_nonneg
    {B x : ℝ} (k : ℕ) (hB : 0 ≤ B) :
    (|x| + B)^k ≤ (2 : ℝ)^k * (max B |x|)^k :=
  pow_abs_add_const_le_two_pow_mul_max B x k
    (add_nonneg (abs_nonneg _) hB)

/-- Auxiliary bound turning the `max` into a product of two simpler factors:
`(max B |x|)^k ≤ (max B 1)^k * (1 + |x|^k)`. -/
lemma max_pow_le_max1_pow_mul_one_add_abs_pow (B x : ℝ) (k : ℕ) :
    (max B |x|)^k ≤ (max B 1)^k * (1 + |x|^k) := by
  have hx0 : 0 ≤ |x| := abs_nonneg _
  by_cases h1 : |x| ≤ 1
  · -- Case |x| ≤ 1
    have hmax : max B |x| ≤ max B 1 := by
      exact max_le_max le_rfl h1
    have hpos : 0 ≤ max B |x| := le_trans hx0 (le_max_right _ _)
    have hpow : (max B |x|)^k ≤ (max B 1)^k :=
      pow_le_pow_of_le_left hpos hmax
    have h1pow : (1 : ℝ) ≤ 1 + |x|^k := by
      have : 0 ≤ |x|^k := pow_nonneg hx0 _
      linarith
    have hnon : 0 ≤ (max B 1)^k := by
      have : 0 ≤ max B 1 := Preorder.le_trans 0 (max B |x|) (max B 1) hpos hmax
      exact pow_nonneg this _
    have : (max B |x|)^k ≤ (max B 1)^k * (1 + |x|^k) := by
      have hmul := mul_le_mul_of_nonneg_left h1pow hnon
      have hmul' : max B 1 ^ k ≤ max B 1 ^ k * (1 + |x| ^ k) := by
        simp
      simpa [one_mul] using (le_trans hpow hmul')
    simpa using this
  · -- Case |x| ≥ 1
    have hx1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge h1)
    have hmax :
        max B |x| ≤ (max B 1) * |x| := by
      cases le_total B |x| with
      | inl hB =>
          have hM1 : 1 ≤ max B 1 := le_max_right _ _
          have : max B |x| = |x| := by simpa [max_comm] using max_eq_right hB
          have hMul : |x| ≤ (max B 1) * |x| :=
            by
              have : 1 ≤ max B 1 := hM1
              have hxpos : 0 ≤ |x| := hx0
              have := mul_le_mul_of_nonneg_right this hxpos
              simpa [one_mul] using this
          simpa [this]
      | inr hB =>
          have hM1 : max B 1 = B := by
            have : 1 ≤ B := le_trans (by norm_num) (le_trans hx1 hB)
            exact max_eq_left this
          have hxpos : 0 ≤ |x| := hx0
          have hx1' : (1 : ℝ) ≤ |x| := hx1
          have : B ≤ B * |x| := by
            have hBpos : 0 ≤ B := le_trans hx0 hB
            have := mul_le_mul_of_nonneg_left hx1' hBpos
            simpa [one_mul] using this
          aesop
    have hposM : 0 ≤ max B |x| := le_trans hx0 (le_max_right _ _)
    have hpow : (max B |x|)^k ≤ ((max B 1) * |x|)^k :=
      pow_le_pow_of_le_left hposM hmax
    have : ((max B 1) * |x|)^k = (max B 1)^k * |x|^k := by
      simp [mul_comm]
      exact mul_pow |x| (max B 1) k
    have hle : (max B |x|)^k ≤ (max B 1)^k * |x|^k :=
      by simpa [this] using hpow
    have hAbsorb : (max B 1)^k * |x|^k ≤ (max B 1)^k * (1 + |x|^k) := by
      have h1 : |x|^k ≤ 1 + |x|^k := by
        have : 0 ≤ |x|^k := pow_nonneg hx0 _
        linarith
      have hnon : 0 ≤ (max B 1)^k := by
        have : 0 ≤ max B 1 := by aesop
        exact pow_nonneg this _
      simp [mul_comm]
    exact le_trans hle hAbsorb

/-- Refined global domination (improved constant) for nonnegative `B`:
`(|x| + B)^k ≤ (2^k * (max B 1)^k) * (1 + |x|^k)`. -/
lemma pow_abs_add_const_global_refined
    (k : ℕ) {B x : ℝ} (hB : 0 ≤ B) :
    (|x| + B)^k ≤ (2 : ℝ)^k * (max B 1)^k * (1 + |x|^k) := by
  have h₁ := pow_abs_add_const_le_two_pow_mul_max_of_nonneg (B := B) (x := x) k hB
  have h₂ := max_pow_le_max1_pow_mul_one_add_abs_pow B x k
  have h₂' :
      (2 : ℝ)^k * (max B |x|)^k
        ≤ (2 : ℝ)^k * ((max B 1)^k * (1 + |x|^k)) :=
    mul_le_mul_of_nonneg_left h₂ (by positivity)
  have hChain :=
    le_trans h₁ h₂'
  simpa [mul_comm, mul_left_comm, mul_assoc] using hChain

/-- Existence version (with `B ≥ 0`) giving a constant `C` so that
`(|x| + B)^k ≤ C * (1 + |x|^k)`. -/
lemma pow_abs_add_const_global
    (k : ℕ) {B : ℝ} (hB : 0 ≤ B) :
  ∃ C > 0, ∀ x : ℝ, (|x| + B)^k ≤ C * (1 + |x|^k) := by
  let C := (2 : ℝ)^k * (max B 1)^k
  have hCpos : 0 < C := by
    have h1 : 0 < (2 : ℝ)^k := by positivity
    have h2 : 0 < (max B 1)^k := by
      have : 0 < max B 1 := by aesop
      exact pow_pos this _
    exact mul_pos h1 h2
  refine ⟨C, hCpos, ?_⟩
  intro x
  have h := pow_abs_add_const_global_refined k (B := B) (x := x) hB
  simpa [C, mul_comm, mul_left_comm, mul_assoc] using h
end Real

open Real

/-- Integrability of `|x|^k * exp (-a x^2)` for `a > 0`.  We obtain it from the
library lemma with *unsigned* monomial by taking absolute values. -/
lemma integrable_abs_pow_mul_exp_neg_mul_sq
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k * Real.exp (-a * x^2)) := by
  classical
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq ha (s := (k : ℝ)) hk
  have h_norm : Integrable (fun x : ℝ => |x^(k : ℝ) * Real.exp (-a * x^2)|) := h.norm
  have hEq : (fun x : ℝ => |x|^k * Real.exp (-a * x^2))
           = (fun x : ℝ => |x^(k : ℝ) * Real.exp (-a * x^2)|) := by
    funext x
    have hx : 0 ≤ |x| := abs_nonneg _
    have hexp_pos : 0 < Real.exp (-a * x^2) := Real.exp_pos _
    rw [abs_mul, abs_of_pos hexp_pos]
    have h_rpow : |x^(k : ℝ)| = |x|^(k : ℝ) := by
      aesop
    rw [h_rpow]
    aesop
  rwa [hEq]

/-- Core Gaussian integrability block. -/
lemma integrable_exp_neg_mul_sq' {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * x^2)) := by
  simpa using integrable_exp_neg_mul_sq ha

/-- Helper (all `B : ℝ`): there is a constant `C > 0` with
`| (|x| + B)^k | ≤ C * (1 + |x|^k)`.  (Coarse global polynomial domination.) -/
lemma pow_abs_add_const_global_allB (k : ℕ) (B : ℝ) :
  ∃ C > 0, ∀ x : ℝ, |(|x| + B)^k| ≤ C * (1 + |x|^k) := by
  classical
  obtain ⟨C, hCpos, hDom⟩ :=
    Real.pow_abs_add_const_global (k := k) (B := |B|) (hB := abs_nonneg _)
  refine ⟨C, hCpos, ?_⟩
  intro x
  have h1 : |(|x| + B)^k| = |(|x| + B)| ^ k := by
    simp [abs_pow]
  have h2 : |(|x| + B)| ≤ |x| + |B| := by
    have := abs_add_le (|x|) B
    simpa using this
  have h2pow : |(|x| + B)| ^ k ≤ (|x| + |B|)^k :=
    pow_le_pow_left₀ (abs_nonneg _) h2 k
  have : |(|x| + B)^k| ≤ (|x| + |B|)^k := by simpa [h1]
  have hDom' := hDom x
  exact this.trans hDom'

/-- Main domination/integrability lemma:
`( |x| + B)^k * exp(-a x^2)` integrable for `a > 0`, any real `B`. -/
lemma integrable_polyShift_mul_exp_neg_mul_sq
    {a B : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (|x| + B)^k * Real.exp (- a * x^2)) := by
  classical
  have hBase := integrable_exp_neg_mul_sq' (a := a) ha
  have hMoment := integrable_abs_pow_mul_exp_neg_mul_sq (a := a) ha k
  obtain ⟨C, hCpos, hDom⟩ := pow_abs_add_const_global_allB k B
  have hPoint :
      ∀ x, ‖(|x| + B)^k * Real.exp (-a * x^2)‖
          ≤ C * ( (1 + |x|^k) * Real.exp (-a * x^2)) := by
    intro x
    have hExpPos : 0 ≤ Real.exp (-a * x^2) := by positivity
    have hDom' : |(|x| + B)^k| ≤ C * (1 + |x|^k) := hDom x
    have : ‖(|x| + B)^k * Real.exp (-a * x^2)‖
            = |(|x| + B)^k| * Real.exp (-a * x^2) := by
      simp [Real.norm_eq_abs]
    have : |(|x| + B)^k| * Real.exp (-a * x^2)
          ≤ (C * (1 + |x|^k)) * Real.exp (-a * x^2) :=
      mul_le_mul_of_nonneg_right hDom' hExpPos
    simpa [this, mul_comm, mul_left_comm, mul_assoc]
  have hIntDom :
      Integrable (fun x : ℝ => (1 + |x|^k) * Real.exp (-a * x^2)) := by
    have hEq :
        (fun x : ℝ => (1 + |x|^k) * Real.exp (-a * x^2))
          = (fun x => Real.exp (-a * x^2))
            + (fun x => |x|^k * Real.exp (-a * x^2)) := by
      funext x; simp [add_mul]
    rw [hEq]
    exact hBase.add hMoment
  have hIntDomC :
      Integrable (fun x : ℝ => C * ((1 + |x|^k) * Real.exp (-a * x^2))) :=
    hIntDom.const_mul _
  refine hIntDomC.mono' ?_ (ae_of_all _ hPoint)
  have hMeasPoly : Measurable fun x : ℝ => (|x| + B)^k :=
    (measurable_abs.add measurable_const).pow_const _
  have hMeasExp : Measurable fun x : ℝ => Real.exp (-a * x^2) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id'.pow 2))).measurable
  exact (hMeasPoly.mul hMeasExp).aestronglyMeasurable

end PolyGaussianDomination

/-- Integrability of `( |x| + 2)^k * exp(-a x^2)` for `a > 0`. -/
lemma integrable_polynomial_exp_neg_mul_sq
    {k : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (|x| + 2)^k * Real.exp (- a * x^2)) volume := by
  simpa using
    (integrable_polyShift_mul_exp_neg_mul_sq (a := a) (B := 2) ha k)

/-- Degenerate (variance = 0) real Gaussian is the Dirac mass at the mean.
(Provide this alias if missing in the snapshot.) -/
@[simp] lemma gaussianReal_dirac (μ : ℝ) :
    gaussianReal μ (0 : ℝ≥0) = Measure.dirac μ := by
  classical
  simp [gaussianReal]

open ProbabilityTheory

/-! ### Polynomial moment integrability -/

/-- Degenerate case: integrability of `(1 + |x|)^k` under the Dirac measure. -/
lemma gaussianReal_integrable_one_add_abs_pow_deg
    (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 (0 : ℝ≥0)) := by
  classical
  have : gaussianReal 0 (0 : ℝ≥0) = Measure.dirac 0 := by simp
  have hMeas : Measurable (fun x : ℝ => (1 + |x|)^k) :=
    (measurable_const.add measurable_abs).pow_const _
  simpa [this, abs_of_nonneg (show 0 ≤ (0:ℝ) by simp)] using
    Measure.integrable_dirac hMeas

/-- Explicit constants (decay rate `a` and normalizing factor `c`) giving the
centered Gaussian pdf as `c * exp(-a x^2)` in the non–degenerate case. -/
lemma gaussianPDF_centered_const_mul_exp
    {v : ℝ≥0} (hv : v ≠ 0) :
  let a : ℝ := 1 / (2 * (v : ℝ))
  let c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  (0 < a) ∧ (0 < c) ∧
    (∀ x : ℝ, gaussianPDF 0 v x = ENNReal.ofReal (c * Real.exp (- a * x^2))) := by
  classical
  intro a c
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have ha : 0 < a := by
    have : 0 < 2 * (v : ℝ) := by nlinarith
    simp [a, one_div]
    aesop
  have hc : 0 < c := by
    have : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
      have : 0 < 2 * Real.pi * (v : ℝ) := by
        have hπ : 0 < Real.pi := Real.pi_pos
        nlinarith
      exact Real.sqrt_pos.mpr this
    simp [c]
    aesop
  refine ⟨ha, hc, ?_⟩
  intro x
  simp [gaussianPDF, gaussianPDFReal, a, c, div_eq_mul_inv,
    mul_comm, mul_left_comm]

/-- Lebesgue–integrability of the polynomial times Gaussian kernel
`(1 + |x|)^k * exp (-a x^2)` for every `a > 0`. -/
lemma integrable_one_add_abs_pow_mul_exp
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (- a * x^2)) := by
  have hEq : (fun x : ℝ => (1 + |x|)^k * Real.exp (- a * x^2))
            = (fun x : ℝ => (|x| + 1)^k * Real.exp (- a * x^2)) := by
    funext x; simp [add_comm]
  have h := integrable_polyShift_mul_exp_neg_mul_sq
              (a := a) (B := 1) ha k
  aesop

section GaussianPolynomialMomentRewrite

variable {v : ℝ≥0} (hv : v ≠ 0) (k : ℕ)

private lemma gaussian_poly_pow_nonneg :
  ∀ x : ℝ, 0 ≤ (1 + |x|)^k := by
  intro x; exact pow_nonneg (by nlinarith [abs_nonneg x]) _

private lemma gaussian_poly_exp_nonneg
  {a : ℝ} : ∀ x : ℝ, 0 ≤ Real.exp (- a * x^2) := by
  intro x; positivity

/-- Unfold the (non–degenerate) centered Gaussian as a withDensity integral. -/
lemma lintegral_gaussian_poly_step1 (hv : v ≠ 0) (k : ℕ) :
  (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    = ∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := by
  classical
  have hμ : gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v) := by
    simp [gaussianReal, hv]
  have h_meas_poly :
      Measurable (fun x : ℝ => (‖(1 + |x|)^k‖₊ : ℝ≥0∞)) := by
    have hRew :
        (fun x : ℝ => (‖(1 + |x|)^k‖₊ : ℝ≥0∞))
          = fun x => ENNReal.ofReal ((1 + |x|)^k) := by
      funext x
      have hx : 0 ≤ (1 + |x|)^k :=
        (gaussian_poly_pow_nonneg (k := k) x)
      simp [Real.nnnorm_of_nonneg hx]; rw [← ENNReal.ofReal_eq_coe_nnreal]
    rw [hRew]
    exact ENNReal.measurable_ofReal.comp ((measurable_const.add measurable_abs).pow_const k)
  have h_meas_pdf : Measurable (gaussianPDF 0 v) :=
    measurable_gaussianPDF _ _
  rw [hμ]
  have h_eq :=
    lintegral_withDensity_eq_lintegral_mul volume
      h_meas_pdf
      h_meas_poly
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq

/-- Rewrite the integral of the polynomial under the Gaussian
density by substituting the explicit `(a,c)` exponential form of the pdf. -/
lemma lintegral_gaussian_poly_step2
    (hv : v ≠ 0) (k : ℕ) :
  let a : ℝ := 1 / (2 * (v : ℝ))
  let c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    =
  ∫⁻ x,
    (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (c * Real.exp (- a * x^2)) := by
  classical
  intro a c
  have h₁ :=
    lintegral_gaussian_poly_step1
      (v := v) (hv := hv) (k := k)
  obtain ⟨_ha, _hc, hpdf⟩ :=
    gaussianPDF_centered_const_mul_exp (v := v) hv
  have h₂ :
      (∫⁻ x,
          (‖(1 + |x|)^k‖₊ : ℝ≥0∞) * gaussianPDF 0 v x)
        =
      ∫⁻ x,
          (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
            ENNReal.ofReal (c * Real.exp (- a * x^2)) := by
    aesop
  aesop

/-- For every non-negative real `r`, `ENNReal.ofReal r` coincides with the
corresponding coercion of the `nnnorm`.  (Tiny wrapper around
`Real.nnnorm_of_nonneg` / `ofReal_eq_coe_nnreal`.) -/
@[simp] lemma ofReal_eq_nnnorm {r : ℝ} (hr : 0 ≤ r) :
    (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [nnnorm_of_nonneg hr]; rw [← ENNReal.ofReal_eq_coe_nnreal]

/-- Splitting rule for `ofReal` on a non-negative product, with the *forward*
orientation that is more convenient for rewriting. -/
@[simp] lemma ofReal_mul'
    {a b : ℝ} (_ : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (a * b) =
      ENNReal.ofReal a * ENNReal.ofReal b := by
  rw [ENNReal.ofReal_mul' hb]

/-- `nnnorm` of the polynomial–exponential product that appears in the
Gaussian moment lemmas.  Stated once and for all so that later proofs can
`rw [nnnorm_poly_exp]` instead of reproducing the same reasoning. -/
@[simp] lemma nnnorm_poly_exp
    {k : ℕ} {a x : ℝ} (hk : 0 ≤ (1 + |x|)^k)
    (h_exp : 0 ≤ Real.exp (-a * x^2)) :
    (‖((1 + |x|)^k * Real.exp (-a * x^2))‖₊ : ℝ≥0∞)
      = ENNReal.ofReal ((1 + |x|)^k * Real.exp (-a * x^2)) := by
  have h_nonneg : 0 ≤ (1 + |x|)^k * Real.exp (-a * x^2) :=
    mul_nonneg hk h_exp
  simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    using ofReal_eq_nnnorm h_nonneg

/-- *pointwise* factorisation lemma.
It rewrites the product of the polynomial factor and the Gaussian kernel

    `‖(1+|x|)^k‖₊ ⋅ ofReal (c · exp (-a x²))`

as the product of the normalising constant `ofReal c` and the
`nnnorm` of the full polynomial–exponential factor. -/
lemma gaussian_poly_pointwise_factor
    {k : ℕ} {a c : ℝ} (hc_pos : 0 < c) :
    ∀ x : ℝ,
      (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-a * x^2))
        =
      ENNReal.ofReal c *
        (‖((1 + |x|)^k * Real.exp (-a * x^2))‖₊ : ℝ≥0∞) := by
  intro x
  have h_pow_nonneg : 0 ≤ (1 + |x|) ^ k := by
    have : 0 ≤ (1 : ℝ) + |x| := by linarith [abs_nonneg x]
    exact pow_nonneg this _
  have h_exp_nonneg : 0 ≤ Real.exp (-a * x^2) := (Real.exp_pos _).le

  calc
    (‖(1 + |x|)^k‖₊ : ℝ≥0∞) * ENNReal.ofReal (c * Real.exp (-a * x^2))
      = ENNReal.ofReal ((1 + |x|)^k) * ENNReal.ofReal (c * Real.exp (-a * x^2)) := by
        rw [ofReal_eq_nnnorm h_pow_nonneg]
    _ = ENNReal.ofReal ((1 + |x|)^k) * (ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-a * x^2))) := by
        rw [ofReal_mul' hc_pos.le h_exp_nonneg]
    _ = ENNReal.ofReal c * (ENNReal.ofReal ((1 + |x|)^k) * ENNReal.ofReal (Real.exp (-a * x^2))) := by
        rw [← mul_assoc, mul_comm (ENNReal.ofReal c)]; rw [mul_right_comm]
    _ = ENNReal.ofReal c * ENNReal.ofReal ((1 + |x|)^k * Real.exp (-a * x^2)) := by
        rw [← ofReal_mul' h_pow_nonneg h_exp_nonneg]
    _ = ENNReal.ofReal c * (‖((1 + |x|)^k * Real.exp (-a * x^2))‖₊ : ℝ≥0∞) := by
        rw [← nnnorm_poly_exp h_pow_nonneg h_exp_nonneg]

/-- Pull out the constant `c` from the Lebesgue integral. -/
lemma lintegral_gaussian_poly_step4
  {a c : ℝ} (_ : 0 < c) :
  (∫⁻ x,
     ENNReal.ofReal c *
       (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞))
    =
  ENNReal.ofReal c *
    (∫⁻ x,
       (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := by
  classical
  have hpow : Measurable fun x : ℝ => (1 + |x|)^k :=
    (measurable_const.add measurable_abs).pow_const k
  have hExp : Measurable fun x : ℝ => Real.exp (- a * x^2) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id'.pow 2))).measurable
  have h_meas :
      Measurable (fun x : ℝ =>
        (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := by
    have hnon :
        (fun x : ℝ =>
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞))
        =
        (fun x : ℝ =>
          ENNReal.ofReal ((1 + |x|)^k * Real.exp (- a * x^2))) := by
      funext x
      have : 0 ≤ (1 + |x|)^k * Real.exp (- a * x^2) := by
        have h1 : 0 ≤ (1 + |x|)^k :=
          pow_nonneg (by nlinarith [abs_nonneg x]) _
        have h2 : 0 ≤ Real.exp (- a * x^2) := by positivity
        exact mul_nonneg h1 h2
      rw [ofReal_eq_nnnorm this]
    rw [hnon]
    exact ENNReal.measurable_ofReal.comp (hpow.mul hExp)
  exact lintegral_const_mul _ h_meas

lemma lintegral_one_add_abs_pow_gaussian_rewrite
    (hv : v ≠ 0) (k : ℕ) :
  let a : ℝ := 1 / (2 * (v : ℝ))
  let c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  (∫⁻ x,
      (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    =
  ENNReal.ofReal c *
    (∫⁻ x,
      (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := by
  classical
  intro a c
  obtain ⟨ha, hc, hpdf⟩ := gaussianPDF_centered_const_mul_exp (v := v) hv
  have h2 := lintegral_gaussian_poly_step2 (v := v) hv k
  have hPoint :
      ∀ x : ℝ,
        (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (- a * x^2))
        =
        ENNReal.ofReal c *
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞) :=
    gaussian_poly_pointwise_factor (k := k) (a := a) hc
  have h3 :
      ∫⁻ x,
        (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (- a * x^2))
        =
      ∫⁻ x,
        ENNReal.ofReal c *
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞) :=
    lintegral_congr_ae (ae_of_all _ hPoint)
  have h4 := lintegral_gaussian_poly_step4 (k := k) (a := a) (c := c) hc
  calc
    (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ∫⁻ x,
        (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (- a * x^2)) := h2
    _ =
      ∫⁻ x,
        ENNReal.ofReal c *
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞) := h3
    _ =
      ENNReal.ofReal c *
        (∫⁻ x,
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := h4
end GaussianPolynomialMomentRewrite

/-- Final integrability lemma (non–degenerate centered Gaussian): the polynomial
moment `(1 + |x|)^k` has finite expectation under `gaussianReal 0 v`.  This is a
thin wrapper combining the preceding structural lemmas. -/
lemma gaussianReal_integrable_one_add_abs_pow_pos
    {v : ℝ≥0} (hv : v ≠ 0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) := by
  classical
  set a : ℝ := 1 / (2 * (v : ℝ))
  set c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have hConsts := gaussianPDF_centered_const_mul_exp (v := v) hv
  rcases hConsts with ⟨ha, hc, hpdf⟩
  have hCore :
      Integrable (fun x : ℝ =>
          (1 + |x|)^k * Real.exp (- a * x^2)) :=
    integrable_one_add_abs_pow_mul_exp (a := a) ha k
  have hAEs :
      AEStronglyMeasurable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) :=
    ((measurable_const.add measurable_abs).pow_const _).aestronglyMeasurable
  refine ⟨hAEs, ?_⟩
  have hRewrite :=
    lintegral_one_add_abs_pow_gaussian_rewrite (v := v) hv k
  have hCoreFin :
      (∫⁻ x,
        (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) < ∞ := hCore.2
  have hcFin : (ENNReal.ofReal c) < ∞ := by
    simp
  have hProdFin :
      (ENNReal.ofReal c) *
        (∫⁻ x,
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) < ∞ :=
    ENNReal.mul_lt_top hcFin hCoreFin
  have hLHSfin :
      (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := by
    aesop
  exact hLHSfin

/-- Centered case: integrability of `(1 + |x|)^k` under the Gaussian measure. -/
lemma gaussianReal_integrable_one_add_abs_pow_centered
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) := by
  classical
  by_cases hv : v = 0
  · simpa [hv] using gaussianReal_integrable_one_add_abs_pow_deg k
  · exact gaussianReal_integrable_one_add_abs_pow_pos (v := v) hv k

/-- Shifted case: integrability of `(1 + |x - μ|)^k` under the Gaussian measure. -/
lemma gaussianReal_integrable_one_add_abs_pow_shift
    (μ : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x - μ|)^k) (gaussianReal μ v) := by
  classical
  have hmap :
      (gaussianReal 0 v).map (fun x => x + μ) = gaussianReal μ v :=
    by simpa using gaussianReal_map_add_const (μ := 0) (v := v) μ
  have hCent := gaussianReal_integrable_one_add_abs_pow_centered (v := v) k
  have hMeas :
      Measurable (fun y : ℝ => (1 + |y - μ|)^k) :=
    (measurable_const.add ((measurable_id.sub measurable_const).abs)).pow_const _
  refine ⟨hMeas.aestronglyMeasurable, ?_⟩
  have hg : Measurable (fun x : ℝ => x + μ) :=
    measurable_id.add measurable_const
  have hf :
      Measurable (fun y : ℝ =>
        (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞)) := by
    have hrew :
        (fun y : ℝ =>
          (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞))
        =
        (fun y : ℝ =>
          ENNReal.ofReal ((1 + |y - μ|)^k)) := by
      funext y
      have hy : 0 ≤ (1 + |y - μ|)^k := by
        have : 0 ≤ (1 : ℝ) + |y - μ| := by nlinarith [abs_nonneg (y - μ)]
        exact pow_nonneg this _
      simpa [Real.norm_eq_abs, abs_of_nonneg hy] using ofReal_eq_nnnorm hy
    rw [hrew]
    change Measurable (ENNReal.ofReal ∘ fun y : ℝ => (1 + |y - μ|) ^ k)
    exact ENNReal.measurable_ofReal.comp hMeas
  have hlin :
      (∫⁻ y, (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal μ v)
        =
      (∫⁻ x, (‖(1 + |(x + μ) - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) := by
    simpa [hmap, Function.comp] using
      (lintegral_map (μ := gaussianReal 0 v)
        (g := fun x : ℝ => x + μ)
        (f := fun y : ℝ => (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞))
        (hf := hf) (hg := hg))
  have hCentFin :
      (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := hCent.2
  have hRHSfin :
      (∫⁻ x, (‖(1 + |(x + μ) - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_neg_cancel] using hCentFin
  have hLHSfin :
      (∫⁻ y, (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal μ v) < ∞ := by
    aesop
  exact hLHSfin

lemma gaussianReal_integrable_one_add_abs_pow
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ k) (gaussianReal 0 v) := by
  simpa [Real.norm_eq_abs] using
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) k

/-! ### General polynomial × sub-Gaussian exponential integrability under a Gaussian law

We split `integrable_polynomial_exp_quadratic_gaussian` into higher–generality lemmas:
1) A parameterized lemma for non-degenerate Gaussians with any exponent `s < 1/(2v)`.
2) A wrapper that includes the degenerate Dirac case.
3) The original lemma as a short corollary with `s = 1/(4v)`.
-/

/-- Combine the exponents on `x^2`: `exp (s x^2) * exp (-(a) x^2) = exp (-(a - s) x^2)`. -/
private lemma exp_sq_combine (s a x : ℝ) :
  Real.exp (s * x^2) * Real.exp (-(a) * x^2) = Real.exp (-(a - s) * x^2) := by
  have hsum : s * x^2 + (-(a) * x^2) = (-(a - s)) * x^2 := by
    ring
  calc
    Real.exp (s * x^2) * Real.exp (-(a) * x^2)
        = Real.exp (s * x^2 + (-(a) * x^2)) := by
          simp [Real.exp_add]
    _ = Real.exp (-(a - s) * x^2) := by aesop


/-- Core integrability transfer (non-degenerate Gaussian):
Let `v ≠ 0`. Put `a := 1/(2v)`. If `s < a` and the Lebesgue integral of
`x ↦ g x * exp (-(a - s) x^2)` is finite, then
`x ↦ g x * exp (s x^2)` is integrable w.r.t. `gaussianReal 0 v`.

Only measurability of `g` and pointwise nonnegativity are required. -/
private lemma measurable_nnnorm_of_nonneg_of_measurable
    {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) :
    Measurable (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞)) := by
  have hRew :
      (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞)) = fun x => ENNReal.ofReal (f x) := by
    funext x
    simpa [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
      using ofReal_eq_nnnorm (h0 x)
  rw [hRew]
  change Measurable (ENNReal.ofReal ∘ f)
  exact ENNReal.measurable_ofReal.comp hf

/-- With-density rewrite of the L¹-seminorm under `gaussianReal 0 v` (non-degenerate). -/
private lemma lintegral_nnnorm_wrt_gaussian_eq_mul_pdf
    {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ}
    (h : Measurable (fun x => (‖f x‖₊ : ℝ≥0∞))) :
  (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    =
  ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := by
  have hμ : gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v) := by
    simp [gaussianReal, hv]
  have hEq :=
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_gaussianPDF 0 v) h
  simpa [hμ, mul_comm, mul_left_comm, mul_assoc] using hEq

/-- Pointwise factorization against the explicit Gaussian pdf kernel.
It pulls out the pdf normalizing constant and leaves a pure Lebesgue kernel. -/
private lemma gaussian_pdf_pointwise_factor
    {v : ℝ≥0} (_ : v ≠ 0)
    {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    {s a c : ℝ}
    (hpdf :
      ∀ x : ℝ, gaussianPDF 0 v x = ENNReal.ofReal (c * Real.exp (-(a) * x^2))) :
  ∀ x : ℝ,
    (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x
      =
    ENNReal.ofReal c *
      (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞) := by
  intro x
  have h_exp2 : 0 ≤ Real.exp (-(a) * x^2) := (Real.exp_pos _).le
  have h_exp1 : 0 ≤ Real.exp (s * x^2) := (Real.exp_pos _).le
  have hf_nonneg : 0 ≤ g x * Real.exp (s * x^2) :=
    mul_nonneg (hg0 x) h_exp1
  have hpdfx := hpdf x
  calc
    (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x
        = (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
            * ENNReal.ofReal (c * Real.exp (-(a) * x^2)) := by
          rw [hpdfx]
    _ = (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
            * (ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-(a) * x^2))) := by
          rw [ENNReal.ofReal_mul' h_exp2]
    _ = ENNReal.ofReal c *
            ((‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
              * ENNReal.ofReal (Real.exp (-(a) * x^2))) := by
          rw [mul_left_comm]
    _ = ENNReal.ofReal c *
            (ENNReal.ofReal (g x * Real.exp (s * x^2))
              * ENNReal.ofReal (Real.exp (-(a) * x^2))) := by
          have hnn :
              (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
                = ENNReal.ofReal (g x * Real.exp (s * x^2)) := by
            rw [nnnorm_of_nonneg hf_nonneg, ← ENNReal.ofReal_eq_coe_nnreal]
          rw [hnn]
    _ = ENNReal.ofReal c *
            ENNReal.ofReal ((g x * Real.exp (s * x^2))
              * Real.exp (-(a) * x^2)) := by
          rw [← ENNReal.ofReal_mul' h_exp2]
    _ = ENNReal.ofReal c *
          ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))) := by
      have hassoc :
        (g x * Real.exp (s * x^2)) * Real.exp (-(a) * x^2)
          = g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)) := by
        simp [mul_assoc]
      aesop
    _ = ENNReal.ofReal c *
          (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞) := by
      have hnon :
        0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)) :=
        mul_nonneg (hg0 x) (mul_nonneg h_exp1 h_exp2)
      have htoNN :
          ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))
            = (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞) := by
        rw [nnnorm_of_nonneg hnon, ← ENNReal.ofReal_eq_coe_nnreal]
      aesop

/-- Combine the two exponential factors on `x^2` inside the lintegrand. -/
private lemma lintegral_congr_exp_sq_combine
    {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) {s a : ℝ} :
  (∫⁻ x,
      (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞))
    =
  (∫⁻ x, (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞)) := by
  apply lintegral_congr_ae
  refine ae_of_all _ ?_
  intro x
  have hposL : 0 ≤ Real.exp (s * x^2) * Real.exp (-(a) * x^2) := by positivity
  have hposR : 0 ≤ Real.exp (-(a - s) * x^2) := by positivity
  have hL :
      (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞)
        =
      ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))) := by
    have : 0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)) :=
      mul_nonneg (hg0 x) hposL
    simpa [Real.norm_eq_abs, abs_of_nonneg this] using ofReal_eq_nnnorm this
  have hR :
      (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞)
        =
      ENNReal.ofReal (g x * Real.exp (-(a - s) * x^2)) := by
    have : 0 ≤ g x * Real.exp (-(a - s) * x^2) :=
      mul_nonneg (hg0 x) hposR
    simpa [Real.norm_eq_abs, abs_of_nonneg this] using ofReal_eq_nnnorm this
  have hreal :
      g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))
        = g x * Real.exp (-(a - s) * x^2) := by
    exact congrArg (fun t => g x * t) (exp_sq_combine s a x)
  calc
    (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞)
        = ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))) := by
          rw [hL]
    _ = ENNReal.ofReal (g x * Real.exp (-(a - s) * x^2)) := by
          rw [hreal]
    _ = (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞) := by
          exact hR.symm

private lemma gaussian_tilt_lintegral_identity
    {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (s : ℝ) :
  ∃ (a c : ℝ) (_ : 0 < a) (_ : 0 < c),
    (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
      =
    ENNReal.ofReal c *
      (∫⁻ x, (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞)) := by
  classical
  obtain ⟨ha_pos, hc_pos, hpdf⟩ := gaussianPDF_centered_const_mul_exp (v := v) hv
  refine ⟨(1 / (2 * (v : ℝ))), (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹, ?_, ?_, ?_⟩
  · simpa using ha_pos
  · simpa using hc_pos
  · have hExp : Measurable fun x : ℝ => Real.exp (s * x^2) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
    have hMeas_f : Measurable (fun x : ℝ => (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)) :=
      measurable_nnnorm_of_nonneg_of_measurable (hg.mul hExp) (by
        intro x; exact mul_nonneg (hg0 x) ((Real.exp_pos _).le))
    have hWD :
        (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
          =
        ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x :=
      lintegral_nnnorm_wrt_gaussian_eq_mul_pdf (v := v) hv hMeas_f
    have hPoint := gaussian_pdf_pointwise_factor (v := v) hv (g := g) hg0
        (s := s) (a := (1 / (2 * (v : ℝ)))) (c := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) hpdf
    have hmeas_inner :
      Measurable (fun x : ℝ =>
        (‖(g x * (Real.exp (s * x^2) * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞)) := by
      have hexp1 : Measurable fun x : ℝ => Real.exp (s * x^2) :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
      have hexp2 : Measurable fun x : ℝ => Real.exp (-(1 / (2 * (v : ℝ))) * x^2) :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
      have hreal : Measurable (fun x : ℝ =>
        g x * (Real.exp (s * x^2) * Real.exp (-(1 / (2 * (v : ℝ))) * x^2))) :=
        hg.mul (hexp1.mul hexp2)
      have hnon :
        ∀ x, 0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)) := by
        intro x
        exact mul_nonneg (hg0 x) (mul_nonneg ((Real.exp_pos _).le) ((Real.exp_pos _).le))
      exact measurable_nnnorm_of_nonneg_of_measurable hreal hnon
    have hA :
        (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
          =
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
          *
        (∫⁻ x,
          (‖(g x * (Real.exp (s * x^2)
                         * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞)) := by
      calc
        (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
            = ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := hWD
        _ = ∫⁻ x,
              ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
                *
              (‖(g x * (Real.exp (s * x^2)
                        * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞) := by
              refine lintegral_congr_ae (ae_of_all _ ?_); intro x; exact hPoint x
        _ =
            ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
              *
            (∫⁻ x,
              (‖(g x * (Real.exp (s * x^2)
                        * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞)) := by
              exact lintegral_const_mul _ hmeas_inner
    have hLebInt :
        (∫⁻ x,
          (‖(g x * (Real.exp (s * x^2)
                        * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞))
          =
        (∫⁻ x,
          (‖(g x * Real.exp (-((1 / (2 * (v : ℝ))) - s) * x^2))‖₊ : ℝ≥0∞)) := by
      simpa using
        (lintegral_congr_exp_sq_combine (g := g) hg0 (s := s) (a := (1 / (2 * (v : ℝ)))))
    aesop

/-- Core integrability transfer (non-degenerate Gaussian), refactored:
reduce Gaussian integrability to a Lebesgue integrability at decay `(a - s)`. -/
lemma integrable_subGaussian_tilt_gaussian_nondeg
    {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ}
    (_ : s < 1 / (2 * (v : ℝ)))
    {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hLeb :
      Integrable (fun x : ℝ =>
        g x * Real.exp (-(1 / (2 * (v : ℝ)) - s) * x^2))) :
    Integrable (fun x : ℝ => g x * Real.exp (s * x^2))
      (gaussianReal 0 v) := by
  classical
  have hMeas_f : Measurable (fun x : ℝ => g x * Real.exp (s * x^2)) :=
    hg.mul ((Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable)
  obtain ⟨ha_pos, hc_pos, hpdf⟩ := gaussianPDF_centered_const_mul_exp (v := v) hv
  set a0 : ℝ := 1 / (2 * (v : ℝ)) with ha0_def
  set c0 : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hc0_def
  have hExp : Measurable (fun x : ℝ => Real.exp (s * x^2)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
  have hMeas_nnn :
      Measurable (fun x : ℝ => (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)) :=
    measurable_nnnorm_of_nonneg_of_measurable (hg.mul hExp) (by
      intro x; exact mul_nonneg (hg0 x) ((Real.exp_pos _).le))
  have hWD :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x :=
    lintegral_nnnorm_wrt_gaussian_eq_mul_pdf (v := v) hv hMeas_nnn
  have hPoint :
      ∀ x : ℝ,
        (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x
          =
        ENNReal.ofReal c0 *
          (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞) :=
    gaussian_pdf_pointwise_factor (v := v) hv (g := g) hg0
      (s := s) (a := a0) (c := c0) hpdf
  have hmeas_inner :
      Measurable (fun x : ℝ =>
        (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞)) := by
    have hexp1 : Measurable fun x : ℝ => Real.exp (s * x^2) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
    have hexp2 : Measurable fun x : ℝ => Real.exp (-(a0) * x^2) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
    have hreal : Measurable (fun x : ℝ =>
      g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2))) :=
      hg.mul (hexp1.mul hexp2)
    have hnon :
        ∀ x, 0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2)) := by
      intro x
      exact mul_nonneg (hg0 x) (mul_nonneg ((Real.exp_pos _).le) ((Real.exp_pos _).le))
    exact measurable_nnnorm_of_nonneg_of_measurable hreal hnon
  have hA :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ENNReal.ofReal c0 *
        (∫⁻ x,
          (‖(g x * (Real.exp (s * x^2)
                       * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞)) := by
    calc
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
          = ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := hWD
      _ = ∫⁻ x,
            ENNReal.ofReal c0 *
            (‖(g x * (Real.exp (s * x^2)
                      * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞) := by
            refine lintegral_congr_ae (ae_of_all _ ?_); intro x; exact hPoint x
      _ =
          ENNReal.ofReal c0 *
          (∫⁻ x,
            (‖(g x * (Real.exp (s * x^2)
                      * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞)) := by
            exact lintegral_const_mul _ hmeas_inner
  have hLebInt :
      (∫⁻ x,
        (‖(g x * (Real.exp (s * x^2)
                      * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞))
        =
      (∫⁻ x,
        (‖(g x * Real.exp (-((a0) - s) * x^2))‖₊ : ℝ≥0∞)) := by
    simpa using
      (lintegral_congr_exp_sq_combine (g := g) hg0 (s := s) (a := a0))
  have hId :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ENNReal.ofReal c0 *
        (∫⁻ x, (‖(g x * Real.exp (-(a0 - s) * x^2))‖₊ : ℝ≥0∞)) := by
    aesop
  have hLebFin :
      (∫⁻ x,
         (‖(g x * Real.exp (-(a0 - s) * x^2))‖₊ : ℝ≥0∞)) < ∞ := hLeb.2
  have hcFin : (ENNReal.ofReal c0) < ∞ := by simp
  have hGFin :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := by
    rw [hId]
    exact ENNReal.mul_lt_top hcFin hLebFin
  exact ⟨hMeas_f.aestronglyMeasurable, hGFin⟩

/-- Corollary (non-degenerate): polynomial envelope `g x = (1 + |x|)^k`. -/
lemma integrable_polynomial_exp_sq_gaussian_param_nondeg
    {v : ℝ≥0} (hv : v ≠ 0) (k : ℕ) {s : ℝ}
    (hs : s < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2))
      (gaussianReal 0 v) := by
  classical
  let g : ℝ → ℝ := fun x => (1 + |x|)^k
  have hg : Measurable g :=
    (measurable_const.add measurable_abs).pow_const k
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x; exact pow_nonneg (by nlinarith [abs_nonneg x]) _
  set a : ℝ := 1 / (2 * (v : ℝ))
  have hLeb :
      Integrable (fun x : ℝ => g x * Real.exp (-(a - s) * x^2)) := by
    have hapos : 0 < a - s := sub_pos.mpr hs
    simpa [g] using
      integrable_one_add_abs_pow_mul_exp (a := a - s) hapos k
  simpa [g] using
    integrable_subGaussian_tilt_gaussian_nondeg (v := v) hv hs hg hg0 hLeb

/-- Parameterized polynomial × sub-Gaussian exponential integrability under a centered Gaussian.
Works also in the degenerate (Dirac) case for any real `s`. -/
lemma integrable_polynomial_exp_sq_gaussian_param
    (v : ℝ≥0) (k : ℕ) (s : ℝ) :
    (v = 0 ∨ s < 1 / (2 * (v : ℝ))) →
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2)) (gaussianReal 0 v) := by
  classical
  intro hcond
  by_cases hv : v = 0
  · subst hv
    have hdirac : gaussianReal 0 (0 : ℝ≥0) = Measure.dirac 0 := by simp
    have hMeas : Measurable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2)) := by
      have hPoly : Measurable fun x : ℝ => (1 + |x|)^k :=
        (measurable_const.add measurable_abs).pow_const _
      have hExp : Measurable fun x : ℝ => Real.exp (s * x^2) :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
      exact hPoly.mul hExp
    have : Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2)) (Measure.dirac 0) :=
      Measure.integrable_dirac hMeas
    simpa [hdirac] using this
  · rcases hcond with hv0 | hs
    · exact False.elim (hv hv0)
    · exact integrable_polynomial_exp_sq_gaussian_param_nondeg hv k hs

lemma integrable_polynomial_exp_quadratic_gaussian
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (|x|^2 / (4 * (v:ℝ))))
      (gaussianReal 0 v) := by
  classical
  by_cases hv : v = 0
  · have : Integrable (fun x : ℝ =>
                (1 + |x|)^k * Real.exp ((1 / (4 * (v:ℝ))) * x^2)) (gaussianReal 0 v) := by
      refine integrable_polynomial_exp_sq_gaussian_param v k (1 / (4 * (v:ℝ))) (Or.inl hv)
    have hAbsSq : ∀ x : ℝ, |x|^2 = x^2 := by
      intro x; simp [pow_two]
    simpa [div_eq_mul_inv, hAbsSq, mul_comm, mul_left_comm, mul_assoc] using this
  · have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
    have h4v_pos : 0 < 4 * (v : ℝ) := by nlinarith
    have h2v_pos : 0 < 2 * (v : ℝ) := by nlinarith
    have hs : (1 / (4 * (v : ℝ))) < (1 / (2 * (v : ℝ))) := by
      have hlt : 2 * (v : ℝ) < 4 * (v : ℝ) := by nlinarith
      simpa [one_div] using (one_div_lt_one_div_of_lt h2v_pos hlt)
    have : Integrable (fun x : ℝ =>
                (1 + |x|)^k * Real.exp ((1 / (4 * (v:ℝ))) * x^2)) (gaussianReal 0 v) := by
      refine integrable_polynomial_exp_sq_gaussian_param v k (1 / (4 * (v:ℝ))) (Or.inr ?_)
      simpa [one_div] using hs
    have hAbsSq : ∀ x : ℝ, |x|^2 = x^2 := by
      intro x; simp [pow_two]
    simpa [div_eq_mul_inv, hAbsSq, mul_comm, mul_left_comm, mul_assoc] using this

/-- Main integrability upgrade lemma (state-of-art, no placeholders):
we assume moderate growth of `F`. Then for every `δ > 0`,
  x ↦ |F x| (|x|+1) exp(δ|x|)
is integrable under the centered Gaussian `gaussianReal 0 v` (for any variance `v`).
If `v = 0` (degenerate Gaussian) this is immediate; otherwise we use the
quadratic domination `exp(δ|x|) ≤ exp(v δ^2) * exp(|x|^2/(4v))`
combined with the polynomial bound on `F`. -/
lemma integrable_dom_profile_of_moderateGrowth
    {F : ℝ → ℝ} (hF : HasModerateGrowth F)
    (v : ℝ≥0) (δ : ℝ) (_ : 0 < δ)
    (hFmeas : Measurable F) :
    Integrable (fun x => |F x| * (|x| + 1) * Real.exp (δ * |x|))
      (gaussianReal 0 v) := by
  classical
  by_cases hv : v = 0
  · have hdirac : gaussianReal 0 v = Measure.dirac 0 := by
      simp [hv]
    have hMeas :
        Measurable (fun x : ℝ =>
          |F x| * (|x| + 1) * Real.exp (δ * |x|)) := by
      have hFabs : Measurable fun x : ℝ => |F x| := hFmeas.abs
      have hAbs  : Measurable fun x : ℝ => |x|     := measurable_abs
      have hLin  : Measurable fun x : ℝ => |x| + 1 := hAbs.add measurable_const
      have hExp  : Measurable fun x : ℝ => Real.exp (δ * |x|) :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable
      exact (hFabs.mul hLin).mul hExp
    simpa [hdirac] using Measure.integrable_dirac hMeas
  · rcases HasModerateGrowth.bound_F_mul_linear (F := F) hF with
      ⟨C, m, hCpos, hBound⟩
    have hExpDom := exp_abs_linear_le_gaussian_aux δ v hv
    have hAE :
        ∀ᵐ x ∂ gaussianReal 0 v,
          |F x| * (|x| + 1) * Real.exp (δ * |x|)
            ≤ (C * Real.exp ((v:ℝ) * δ^2))
              * (1 + |x|)^(m+1) * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
      refine ae_of_all _ ?_
      intro x
      have h1 := hBound x
      have h2 := hExpDom x
      have hposExp : 0 ≤ Real.exp (δ * |x|) := by positivity
      calc
        |F x| * (|x| + 1) * Real.exp (δ * |x|)
            ≤ (C * (1 + |x|)^(m+1)) * Real.exp (δ * |x|) :=
              (mul_le_mul_of_nonneg_right h1 hposExp)
        _ ≤ (C * (1 + |x|)^(m+1)) *
              (Real.exp ((v:ℝ) * δ^2) * Real.exp (|x|^2 / (4 * (v:ℝ)))) :=
            (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = (C * Real.exp ((v:ℝ) * δ^2)) * (1 + |x|)^(m+1)
              * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
              ring_nf
    have hDomInt :
        Integrable (fun x =>
          (C * Real.exp ((v:ℝ) * δ^2)) * (1 + |x|)^(m+1)
              * Real.exp (|x|^2 / (4 * (v:ℝ))))
          (gaussianReal 0 v) := by
      have hpoly := integrable_polynomial_exp_quadratic_gaussian v (m+1)
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hpoly.const_mul (C * Real.exp ((v:ℝ) * δ^2))
    have hAE_norm :
        ∀ᵐ x ∂ gaussianReal 0 v,
          ‖|F x| * (|x| + 1) * Real.exp (δ * |x|)‖
            ≤ (C * Real.exp ((v:ℝ) * δ^2))
              * (1 + |x|)^(m+1) * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
      refine hAE.mono ?_
      intro x hx
      have hnon : 0 ≤ |F x| * (|x| + 1) * Real.exp (δ * |x|) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      exact hx
    have hFabs : Measurable fun x : ℝ => |F x| := hFmeas.abs
    have hAbs : Measurable fun x : ℝ => |x| := measurable_abs
    have hLin : Measurable fun x : ℝ => |x| + 1 := hAbs.add measurable_const
    have hExp : Measurable fun x : ℝ => Real.exp (δ * |x|) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable
    have hMeas :
        Measurable (fun x : ℝ => |F x| * (|x| + 1) * Real.exp (δ * |x|)) :=
      (hFabs.mul hLin).mul hExp
    refine hDomInt.mono' hMeas.aestronglyMeasurable hAE_norm

lemma integrable_dom_profile
    {F : ℝ → ℝ} (hF : HasModerateGrowth F)
    (v : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (hFmeas : Measurable F) :
    Integrable (fun x => |F x| * (|x| + 1) * Real.exp (δ * |x|))
      (gaussianReal 0 v) :=
  integrable_dom_profile_of_moderateGrowth hF v δ hδ hFmeas

end YoungBounds
end YoungBounds
end DominationExponentialUpgrade

/-- Domination near zero for the *difference quotient* of the Gaussian tilt integrand.
Requires an explicit integrability assumption on the Gaussian law of the exponential–moment
profile.  This is the version appropriate for a mathlib-quality proof of differentiation
under the integral sign. -/
lemma gaussianTilt_diffquot_dom_integrable
    {v : ℝ≥0} {F : ℝ → ℝ}
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hInt : Integrable (fun x => |F x| * (|x| + 1) * Real.exp (δ * |x|)) (gaussianReal 0 v))
    (hFmeas : Measurable F) :
  ∀ᶠ t in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    Integrable (fun x =>
      |(F x * tiltKernel v t x - F x) / t|) (gaussianReal 0 v) := by
  have hdom := gaussianTilt_diffquot_dom (v := v) (F := F) δ hδ₀ hδ₁
  refine hdom.mono ?_
  intro t ht
  refine And.intro ht.left ?_
  have hPoint :
      ∀ x, |(F x * tiltKernel v t x - F x) / t|
          ≤ |F x| * (|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|) := ht.right
  have hC :
      ∀ x, (|x| + (v:ℝ) * δ / 2) ≤ ((v:ℝ) * δ / 2 + 1) * (|x| + 1) := by
    intro x
    have hx : 0 ≤ |x| := abs_nonneg _
    have hvδ : 0 ≤ (v:ℝ) * δ / 2 := by
      have hv0 : 0 ≤ (v:ℝ) := v.property
      have hδ0 : 0 ≤ δ := le_of_lt hδ₀
      nlinarith
    have : |x| + (v:ℝ) * δ / 2 ≤ (|x| + 1) + ((v:ℝ) * δ / 2) * (|x| + 1) := by
      have h1 : |x| ≤ |x| + 1 := by nlinarith
      have h2 : (v:ℝ) * δ / 2 ≤ ((v:ℝ) * δ / 2) * (|x| + 1) := by
        have hpos : 0 ≤ |x| + 1 := by nlinarith
        nlinarith
      nlinarith
    have hfac :
        (|x| + 1) + ((v:ℝ) * δ / 2) * (|x| + 1)
          = ((v:ℝ) * δ / 2 + 1) * (|x| + 1) := by ring
    simpa [hfac]
  have hDomInt :
      Integrable (fun x =>
        |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|))
        (gaussianReal 0 v) := by
    have := hInt.const_mul (((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hMeas_tilt : Measurable fun x : ℝ => tiltKernel v t x := by
    have hInner : Continuous fun x : ℝ => t * x - (v:ℝ) * t^2 / 2 :=
      (continuous_const.mul continuous_id).sub continuous_const
    exact (Real.continuous_exp.comp hInner).measurable
  have hAEs_meas :
      AEStronglyMeasurable
        (fun x => |(F x * tiltKernel v t x - F x) / t|) (gaussianReal 0 v) := by
    have hProd : Measurable (fun x : ℝ => F x * tiltKernel v t x) := hFmeas.mul hMeas_tilt
    have hDiff : Measurable (fun x : ℝ => F x * tiltKernel v t x - F x) := hProd.sub hFmeas
    have hQuot : Measurable (fun x : ℝ => (F x * tiltKernel v t x - F x) / t) := Measurable.div_const hDiff t
    exact hQuot.abs.aestronglyMeasurable
  have hAE :
      ∀ᵐ x ∂ gaussianReal 0 v,
        |(F x * tiltKernel v t x - F x) / t|
          ≤ |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|) := by
    refine ae_of_all _ ?_
    intro x
    have hpt := hPoint x
    have hxC := hC x
    have hposExp1 : 0 ≤ Real.exp (δ * |x|) := by positivity
    have hposExp2 : 0 ≤ Real.exp ((v:ℝ) * δ / 2) := by positivity
    have hposF   : 0 ≤ |F x| := abs_nonneg _
    have hxC' :
        |F x| * (|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|)
          ≤ |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|) := by
      have h1 := mul_le_mul_of_nonneg_left hxC hposF
      have h2 := mul_le_mul_of_nonneg_right h1 hposExp2
      have h3 := mul_le_mul_of_nonneg_right h2 hposExp1
      simpa [mul_comm, mul_left_comm, mul_assoc] using h3
    exact hpt.trans hxC'
  have hAE_norm :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ‖|(F x * tiltKernel v t x - F x) / t|‖
          ≤ |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|) := by
    simpa [Real.norm_eq_abs, abs_abs] using hAE
  exact hDomInt.mono' hAEs_meas hAE_norm

/-- Map of a measure by subtraction of a constant. -/
lemma Measure.map_sub_right {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : Measurable f) (c : ℝ) :
    μ.map (fun x => f x - c) = (μ.map f).map (· - c) := by
  have hg : Measurable (fun x : ℝ => x - c) :=
    (continuous_id.sub continuous_const).measurable
  change μ.map ((fun x : ℝ => x - c) ∘ f) = (μ.map f).map (· - c)
  exact
    (Measure.map_map (μ := μ) (f := f) (g := fun x : ℝ => x - c) (hf := hf) (hg := hg)).symm


/-- Auxiliary integrability lemma: if both `x ↦ x * F x` and `x ↦ F x`
are integrable under `gaussianReal 0 v`, then any function dominated by
`x ↦ |x * F x| + |F x|` is integrable. -/
lemma Integrable.of_bound_gaussianTilt
    {F : ℝ → ℝ} {v : ℝ≥0}
    (h1 : Integrable (fun x => x * F x) (gaussianReal 0 v))
    (h2 : Integrable (fun x => F x) (gaussianReal 0 v))
    {g : ℝ → ℝ}
    (hg_meas : AEStronglyMeasurable g (gaussianReal 0 v))
    (hg : ∀ᵐ x ∂ gaussianReal 0 v,
      |g x| ≤ |x * F x| + |F x|) :
    Integrable g (gaussianReal 0 v) := by
  have h12 : Integrable (fun x => |x * F x| + |F x|) (gaussianReal 0 v) :=
    (h1.abs.add h2.abs)
  exact h12.mono' hg_meas (hg.mono (by intro x hx; exact hx))

/-- Pointwise derivative bundled as a measurability statement (for use with
parametric integral differentiation lemmas). -/
lemma aestronglyMeasurable_deriv_integrand
    {F : ℝ → ℝ} {v : ℝ≥0}
    (hF : ContDiff ℝ 1 F) :
  AEStronglyMeasurable
    (fun x => F x * x) (gaussianReal 0 v) := by
  have hcont : Continuous F := (hF.continuous)
  have hmeas : Measurable F := hcont.measurable
  have : Measurable (fun x : ℝ => F x * x) :=
    (hmeas.mul measurable_id)
  exact this.aestronglyMeasurable

/-- The Gaussian tilt kernel is nonnegative everywhere. -/
lemma tiltKernel_nonneg (v : ℝ≥0) (t x : ℝ) : 0 ≤ tiltKernel v t x := by
  have : 0 < Real.exp (t * x - (v:ℝ) * t^2 / 2) := Real.exp_pos _
  simpa [tiltKernel] using this.le

lemma gaussianTilt_deriv_dom_bound
    {v : ℝ≥0} (δ : ℝ) (hδ_pos : 0 < δ)
    {F : ℝ → ℝ}
    (t : ℝ) (ht : |t| ≤ δ) (x : ℝ) :
  |F x * (x - (v:ℝ) * t) * tiltKernel v t x|
    ≤ |F x| * ((|(v:ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|) := by
  -- 1) triangle: |x - v t| ≤ |x| + |v| |t|
  have h1 : |x - (v:ℝ) * t| ≤ |x| + |(v:ℝ)| * |t| := by
    have := abs_add_le_abs_add_abs x (-(v:ℝ) * t)
    simpa [sub_eq_add_neg, abs_mul, abs_neg, mul_comm, mul_left_comm, mul_assoc] using this
  -- 2) bound |t| by δ
  have h1' : |x - (v:ℝ) * t| ≤ |x| + |(v:ℝ)| * δ := by
    have hvabs : 0 ≤ |(v:ℝ)| := abs_nonneg _
    have hvd : |(v:ℝ)| * |t| ≤ |(v:ℝ)| * δ :=
      mul_le_mul_of_nonneg_left ht hvabs
    exact le_trans h1 (by linarith)
  -- 3) kernel bound: tiltKernel ≤ exp(|t| |x|) ≤ exp(δ |x|)
  have h2 : tiltKernel v t x ≤ Real.exp (|t| * |x|) :=
    tiltKernel_le_exp_abs v t x
  have h2' : tiltKernel v t x ≤ Real.exp (δ * |x|) := by
    have hmul : |t| * |x| ≤ δ * |x| :=
      mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    exact le_trans h2 (by
      simpa using (Real.exp_le_exp.mpr (by simpa [mul_comm] using hmul)))
  -- 4) absorb linear term: |x| + |v| δ ≤ ((|v| δ)+1)(|x|+1)
  have h3 : (|x| + |(v:ℝ)| * δ) ≤ ((|(v:ℝ)| * δ) + 1) * (|x| + 1) := by
    have hx : 0 ≤ |x| := abs_nonneg _
    have hvδ : 0 ≤ |(v:ℝ)| * δ :=
      mul_nonneg (abs_nonneg _) (le_of_lt hδ_pos)
    nlinarith
  -- 5) we chain multiplicative inequalities with explicit nonnegativity
  have hF_nonneg : 0 ≤ |F x| := abs_nonneg _
  have hK_nonneg : 0 ≤ tiltKernel v t x := tiltKernel_nonneg v t x
  have hExpNonneg : 0 ≤ Real.exp (δ * |x|) := by positivity
  have hxvδ_nonneg : 0 ≤ |x| + |(v:ℝ)| * δ := by nlinarith [abs_nonneg x, abs_nonneg (v:ℝ), hδ_pos.le]
  calc
    |F x * (x - (v:ℝ) * t) * tiltKernel v t x|
        = |F x| * |x - (v:ℝ) * t| * tiltKernel v t x := by
            simp [abs_mul, mul_comm, mul_assoc]
    _ ≤ |F x| * (|x| + |(v:ℝ)| * δ) * tiltKernel v t x := by
          have : |F x| * |x - (v:ℝ) * t| ≤ |F x| * (|x| + |(v:ℝ)| * δ) :=
            mul_le_mul_of_nonneg_left h1' hF_nonneg
          exact mul_le_mul_of_nonneg_right this hK_nonneg
    _ ≤ |F x| * (|x| + |(v:ℝ)| * δ) * Real.exp (δ * |x|) := by
          have hKexp : tiltKernel v t x ≤ Real.exp (δ * |x|) := h2'
          have hconst_nonneg :
              0 ≤ |F x| * (|x| + |(v:ℝ)| * δ) := by
            nlinarith [hF_nonneg, hxvδ_nonneg]
          have := mul_le_mul_of_nonneg_left hKexp hconst_nonneg
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
    _ ≤ |F x| * (((|(v:ℝ)| * δ) + 1) * (|x| + 1)) * Real.exp (δ * |x|) := by
          have : (|x| + |(v:ℝ)| * δ) ≤ ((|(v:ℝ)| * δ) + 1) * (|x| + 1) := h3
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left this hF_nonneg)
            hExpNonneg
    _ = |F x| * ((|(v:ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|) := by
          ring_nf

lemma gaussianTilt_domination_bound
    {v : ℝ≥0} (δ : ℝ) (hδ_pos : 0 < δ)
    {F : ℝ → ℝ} (hF : HasModerateGrowth F) (hF_cont : Continuous F) :
    Integrable (fun x => |F x| * ((|(v:ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|))
      (gaussianReal 0 v) := by
  have hInt := integrable_dom_profile_of_moderateGrowth hF v δ hδ_pos hF_cont.measurable
  convert hInt.const_mul (((|(v:ℝ)|) * δ) + 1) using 1
  funext x; ring

/-- AEStronglyMeasurable of the `t`-tilted integrand in `x` from measurability of `F`. -/
lemma aestronglyMeasurable_gaussianTilt_integrand_of_measurable
    {v : ℝ≥0} {F : ℝ → ℝ} (hFmeas : Measurable F) :
  ∀ t, AEStronglyMeasurable (fun x => F x * tiltKernel v t x) (gaussianReal 0 v) := by
  intro t
  have hTilt : Measurable (fun x => tiltKernel v t x) :=
    (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub continuous_const)).measurable
  exact (hFmeas.mul hTilt).aestronglyMeasurable

/-- AEStronglyMeasurable of the “derivative-at-0” integrand `x ↦ F x * x`
under the Gaussian (only measurability of `F`). -/
lemma aestronglyMeasurable_F_mul_id_of_measurable
    {v : ℝ≥0} {F : ℝ → ℝ} (hFmeas : Measurable F) :
  AEStronglyMeasurable (fun x => F x * x) (gaussianReal 0 v) := by
  exact (hFmeas.mul measurable_id).aestronglyMeasurable

/-- Local dominated-differentiation lemma for the left tilt (general).-/
lemma gaussianTilt_hasDerivAt_left_of_dominated
    {v : ℝ≥0} {F : ℝ → ℝ}
    (hFmeas : Measurable F)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (B : ℝ → ℝ)
    (hB_int : Integrable B (gaussianReal 0 v))
    (hBound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ,
          ‖F x * (x - (v : ℝ) * t) * tiltKernel v t x‖ ≤ B x)
    (hF_int : Integrable (fun x => F x) (gaussianReal 0 v)) :
  HasDerivAt (gaussianTilt F v) (∫ x, x * F x ∂ gaussianReal 0 v) 0 := by
  set G  : ℝ → ℝ → ℝ := fun t x => F x * tiltKernel v t x
  set G' : ℝ → ℝ → ℝ := fun t x => F x * (x - (v : ℝ) * t) * tiltKernel v t x
  have hG_meas : ∀ t, AEStronglyMeasurable (G t) (gaussianReal 0 v) :=
    aestronglyMeasurable_gaussianTilt_integrand_of_measurable (v := v) (F := F) hFmeas
  have hG0_int : Integrable (G 0) (gaussianReal 0 v) := by
    simpa [G, tiltKernel] using hF_int
  have hGp0_meas : AEStronglyMeasurable (G' 0) (gaussianReal 0 v) := by
    have : (fun x => G' 0 x) = (fun x => F x * x) := by
      funext x; simp [G', tiltKernel]
    simpa [this] using aestronglyMeasurable_F_mul_id_of_measurable (v := v) (F := F) hFmeas
  have h_bound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖G' t x‖ ≤ B x := by
    simpa [G'] using hBound
  have h_diff :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, HasDerivAt (fun s => G s x) (G' t x) t := by
    refine ae_of_all _ ?_
    intro x t _
    simpa [G, G'] using hasDerivAt_gaussianTiltIntegrand (v := v) (F := F) (x := x) (t := t)
  have hDer :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ              := gaussianReal 0 v)
      (F              := G)
      (F'             := G')
      (s              := Metric.ball (0 : ℝ) δ)
      (hs             := Metric.ball_mem_nhds (0 : ℝ) hδ_pos)
      (bound          := B)
      (hF_meas        := Eventually.of_forall hG_meas)
      (hF_int         := hG0_int)
      (hF'_meas       := hGp0_meas)
      (h_bound        := h_bound)
      (bound_integrable := hB_int)
      (h_diff         := h_diff)
  change HasDerivAt (fun t => ∫ x, G t x ∂ gaussianReal 0 v)
    (∫ x, x * F x ∂ gaussianReal 0 v) 0
  exact hDer.2.congr_deriv (by simp [G', tiltKernel, mul_comm])

lemma gaussianTilt_hasDerivAt_left
    {v : ℝ≥0} (_ : v ≠ 0) {F : ℝ → ℝ}
    (hF  : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    HasDerivAt (gaussianTilt F v)
      (∫ x, x * F x ∂ gaussianReal 0 v) 0 := by
  -- We work with the ball of radius 1 around 0 in `t`.
  let δ : ℝ := 1
  have hδ_pos : 0 < δ := by norm_num
  let B : ℝ → ℝ :=
    fun x => |F x| * ((|(v : ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|)
  have hBound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ,
          ‖F x * (x - (v : ℝ) * t) * tiltKernel v t x‖ ≤ B x := by
    refine ae_of_all _ ?_
    intro x t ht
    have ht' : |t| ≤ δ := (mem_ball_zero_iff.mp ht).le
    have h := gaussianTilt_deriv_dom_bound (v := v) (F := F) δ hδ_pos t ht' x
    exact h
  have hB_int :
      Integrable B (gaussianReal 0 v) := by
    simpa [B] using
      gaussianTilt_domination_bound (v := v) (F := F) δ hδ_pos hMod hF.continuous
  have hFmeas : Measurable F := hF.continuous.measurable
  have hG0_int : Integrable (fun x => F x) (gaussianReal 0 v) := by
    have h1 : ∀ x, ‖F x‖ ≤ B x := by
      intro x
      have hGe1_A : 1 ≤ (|(v : ℝ)| * δ + 1) := by
        have hvn : 0 ≤ |(v : ℝ)| * δ := by
          have hvn' : 0 ≤ |(v : ℝ)| := abs_nonneg (v : ℝ)
          have hδn : 0 ≤ δ := le_of_lt hδ_pos
          exact mul_nonneg hvn' hδn
        nlinarith
      have hGe1_B : 1 ≤ |x| + 1 := by nlinarith [abs_nonneg x]
      have hGe1_C : 1 ≤ Real.exp (δ * |x|) := by
        have : 0 ≤ δ * |x| := by
          have hδn : 0 ≤ δ := le_of_lt hδ_pos
          exact mul_nonneg hδn (abs_nonneg _)
        simpa using Real.one_le_exp_iff.mpr this
      have hAB : 1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1)) :=
        one_le_mul_of_one_le_of_one_le hGe1_A hGe1_B
      have hABC : 1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1)) * Real.exp (δ * |x|) := by
        have hAB_nonneg :
            0 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1)) := by
          have hA_nonneg : 0 ≤ (|(v : ℝ)| * δ + 1) := by
            have : 0 ≤ |(v : ℝ)| * δ := by
              have hvn' : 0 ≤ |(v : ℝ)| := abs_nonneg (v : ℝ)
              have hδn : 0 ≤ δ := le_of_lt hδ_pos
              exact mul_nonneg hvn' hδn
            linarith
          have hB_nonneg : 0 ≤ (|x| + 1) := by nlinarith [abs_nonneg x]
          exact mul_nonneg hA_nonneg hB_nonneg
        have := mul_le_mul_of_nonneg_left hGe1_C hAB_nonneg
        exact one_le_mul_of_one_le_of_one_le hAB hGe1_C
      have hprod :
          1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1) * Real.exp (δ * |x|)) := by
        exact hABC
      have := mul_le_mul_of_nonneg_left hprod (abs_nonneg (F x))
      simpa [B, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using this
    exact (hB_int.mono' (hFmeas.aestronglyMeasurable) (ae_of_all _ h1))
  exact
    gaussianTilt_hasDerivAt_left_of_dominated
      (v := v) (F := F)
      hFmeas hδ_pos B hB_int hBound hG0_int

/-! ##  Auxiliary lemmas for the right–shift derivative  -/

lemma gaussianTilt_deriv_dom
    {v : ℝ≥0} {F : ℝ → ℝ}
    (hMod : HasModerateGrowth F) :
  ∃ (C : ℝ) (m : ℕ) (_ : 0 < C),
    ∀ t, |t| ≤ 1 →
      ∀ x, |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
        ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m := by
  rcases hMod with ⟨C, m, hCpos, _hF, hF'⟩
  refine ⟨C, m, hCpos, ?_⟩
  intro t ht x
  have h_deriv : |deriv F (x + (v:ℝ) * t)| ≤ C * (1 + |x + (v:ℝ) * t|) ^ m := by
    simpa using hF' (x + (v:ℝ) * t)
  have h_tri : |x + (v:ℝ) * t| ≤ |x| + |(v:ℝ)| * |t| := by
    simpa [abs_add_le, abs_mul, mul_comm, mul_left_comm, mul_assoc]
      using abs_add_le_abs_add_abs x ((v:ℝ) * t)
  have ht' : |(v:ℝ)| * |t| ≤ |(v:ℝ)| := by
    have := mul_le_mul_of_nonneg_left ht (abs_nonneg (v:ℝ))
    simpa [mul_one] using this
  have h_lin : 1 + |x + (v:ℝ) * t| ≤ 1 + |x| + |(v:ℝ)| := by
    have : |x + (v:ℝ) * t| ≤ |x| + |(v:ℝ)| := le_trans h_tri (by simpa using ht')
    linarith
  have h_baseL : 0 ≤ 1 + |x + (v:ℝ) * t| := by nlinarith [abs_nonneg (x + (v:ℝ) * t)]
  have h_pow :
      (1 + |x + (v:ℝ) * t|) ^ m ≤ (1 + |x| + |(v:ℝ)|) ^ m :=
    Real.pow_le_pow_of_le_left h_baseL h_lin
  have hDerivBound :
      |deriv F (x + (v:ℝ) * t)|
        ≤ C * (1 + |x| + |(v:ℝ)|) ^ m := by
    have hCnn : 0 ≤ C := le_of_lt hCpos
    exact (le_trans h_deriv (mul_le_mul_of_nonneg_left h_pow hCnn))
  have hvnonneg : 0 ≤ (v : ℝ) := v.property
  have hMul :
      (v : ℝ) * |deriv F (x + (v:ℝ) * t)|
        ≤ C * ((v : ℝ) * (1 + |x| + |(v : ℝ)|) ^ m) := by
    have := mul_le_mul_of_nonneg_right hDerivBound hvnonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have : |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
        ≤ C * ((v : ℝ) * (1 + |x| + |(v : ℝ)|) ^ m) := by
    simpa [abs_mul, abs_of_nonneg hvnonneg, mul_comm, mul_left_comm, mul_assoc] using hMul
  simpa [abs_of_nonneg hvnonneg, mul_comm, mul_left_comm, mul_assoc] using this

/-- Integrability (under any centered Gaussian) of the dominating polynomial profile
appearing in `gaussianTilt_deriv_dom`, for the same constants `C, m`. -/
lemma gaussianTilt_deriv_dom_integrable
    {v : ℝ≥0} {F : ℝ → ℝ}
    (_ : HasModerateGrowth F)
    (C : ℝ) (m : ℕ) (hC : 0 < C) :
  Integrable (fun x => |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m)
      (gaussianReal 0 v) := by
  have hMom : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) m
  have hLe :
      ∀ x : ℝ, (1 + |x| + |(v : ℝ)|) ^ m
        ≤ (1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m := by
    intro x
    have hbaseL : 0 ≤ 1 + |x| + |(v:ℝ)| := by nlinarith [abs_nonneg x, abs_nonneg (v:ℝ)]
    have hxy : 1 + |x| + |(v:ℝ)| ≤ (1 + |x|) * (1 + |(v:ℝ)|) := by
      have hxv : 0 ≤ |x| * |(v:ℝ)| := by exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      nlinarith
    have hpow :=
      Real.pow_le_pow_of_le_left (k := m) hbaseL hxy
    have hfac : ((1 + |x|) * (1 + |(v:ℝ)|)) ^ m
                = (1 + |(v:ℝ)|) ^ m * (1 + |x|) ^ m := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_pow (1 + |x|) (1 + |(v:ℝ)|) m)
    exact le_of_le_of_eq hpow hfac
  have hIntDom :
      Integrable (fun x : ℝ =>
        (1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) (gaussianReal 0 v) :=
    (hMom.const_mul ((1 + |(v : ℝ)|) ^ m))
  have hMeas :
      AEStronglyMeasurable
        (fun x => |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m)
        (gaussianReal 0 v) := by
    have hPoly : Measurable (fun x : ℝ => (1 + |x| + |(v : ℝ)|) ^ m) :=
      (((measurable_const.add measurable_abs).add measurable_const).pow_const _)
    exact ((measurable_const.mul measurable_const).mul hPoly).aestronglyMeasurable
  have hAE :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ‖|(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m‖
          ≤ (|(v : ℝ)| * C) * ((1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) := by
    refine ae_of_all _ (fun x => ?_)
    have hnn1 : 0 ≤ |(v : ℝ)| := abs_nonneg _
    have hnn2 : 0 ≤ C := le_of_lt hC
    have hnn3 : 0 ≤ (1 + |x| + |(v : ℝ)|) ^ m := by
      have hbase : 0 ≤ 1 + |x| + |(v : ℝ)| := by
        have : 0 ≤ |x| := abs_nonneg _
        have : 0 ≤ |(v : ℝ)| := abs_nonneg _
        nlinarith
      exact pow_nonneg hbase _
    have hLHS_nonneg :
        0 ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m :=
      mul_nonneg (mul_nonneg hnn1 hnn2) hnn3
    have hDom :
        |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m
          ≤ (|(v : ℝ)| * C) *
              ((1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) := by
      have hpoly :=
        mul_le_mul_of_nonneg_left (hLe x) (mul_nonneg hnn1 hnn2)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hpoly
    have hAbs_eq :
        ‖|(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m‖
          = (|(v : ℝ)| * C) * (1 + |x| + |(v : ℝ)|) ^ m := by
      have hnonneg :
          0 ≤ (|(v : ℝ)| * C) * (1 + |x| + |(v : ℝ)|) ^ m :=
        mul_nonneg (mul_nonneg hnn1 hnn2) hnn3
      exact norm_of_nonneg hLHS_nonneg
    have : ‖|(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m‖
          ≤ (|(v : ℝ)| * C) * ((1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) := by
      aesop
    exact this
  exact (hIntDom.const_mul (|(v : ℝ)| * C)).mono' hMeas hAE

/-- Generic shift differentiation lemma:
Assumes integrability of F at t = 0, and domination/integrability for the derivative profile. -/
lemma gaussianTilt_hasDerivAt_right_aux
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hF_int : Integrable F (gaussianReal 0 v))
    {C : ℝ} {m : ℕ}
    (hDom : ∀ t, |t| ≤ 1 → ∀ x,
                |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
                  ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|)^m)
    (hInt : Integrable (fun x => |(v : ℝ)| * C *
                               (1 + |x| + |(v : ℝ)|)^m) (gaussianReal 0 v)) :
    HasDerivAt (gaussianTilt F v)
      ((v : ℝ) * ∫ x, deriv F x ∂ gaussianReal 0 v) 0 := by
  have hShift := gaussianTilt_eq_shift (v := v) hv (F := F)
  set G  : ℝ → ℝ → ℝ := fun t x => F (x + (v : ℝ) * t)
  set G' : ℝ → ℝ → ℝ := fun t x => (v : ℝ) * deriv F (x + (v : ℝ) * t)
  have hG_meas : ∀ t, AEStronglyMeasurable (G t) (gaussianReal 0 v) := by
    intro t
    have hAdd : Measurable (fun x : ℝ => x + (v : ℝ) * t) :=
      (measurable_id.add measurable_const)
    exact (hF.continuous.measurable.comp hAdd).aestronglyMeasurable
  have hG0_int : Integrable (G 0) (gaussianReal 0 v) := by
    simpa [G] using hF_int
  have hGp0_meas : AEStronglyMeasurable (G' 0) (gaussianReal 0 v) := by
    have hDer_meas : Measurable (deriv F) :=
      (hF.continuous_deriv le_rfl).measurable
    have hEq : (fun x => G' 0 x) = (fun x => (v : ℝ) * deriv F x) := by
      funext x; simp [G']
    change AEStronglyMeasurable (fun x => G' 0 x) (gaussianReal 0 v)
    rw [hEq]
    exact (measurable_const.mul hDer_meas).aestronglyMeasurable
  have h_bound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) (1 : ℝ), ‖G' t x‖
          ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|)^m := by
    refine ae_of_all _ (fun x => ?_)
    intro t ht
    have ht' : |t| ≤ 1 := (mem_ball_zero_iff.mp ht).le
    change |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
            ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|)^m
    exact hDom t ht' x
  have h_diff :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) (1 : ℝ),
          HasDerivAt (fun s => G s x) (G' t x) t := by
    refine ae_of_all _ (fun x => ?_)
    intro t _ht
    have hInner0 : HasDerivAt (fun s : ℝ => (v : ℝ) * s) (v : ℝ) t := by
      simpa [mul_one] using (hasDerivAt_id t).const_mul (v : ℝ)
    have hInner : HasDerivAt (fun s : ℝ => x + (v : ℝ) * s) (v : ℝ) t :=
      hInner0.const_add x
    have hOuter : HasDerivAt F (deriv F (x + (v : ℝ) * t)) (x + (v : ℝ) * t) :=
      (hF.differentiable one_ne_zero _).hasDerivAt
    change HasDerivAt
      (F ∘ fun s : ℝ => x + (v : ℝ) * s)
      ((v : ℝ) * deriv F (x + (v : ℝ) * t)) t
    simpa only [mul_comm] using hOuter.comp t hInner
  have hDer :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ              := gaussianReal 0 v)
      (F              := G)
      (F'             := G')
      (s              := Metric.ball (0 : ℝ) (1 : ℝ))
      (hs             := Metric.ball_mem_nhds (0 : ℝ) (by norm_num))
      (bound          := fun x => |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|)^m)
      (hF_meas        := Eventually.of_forall hG_meas)
      (hF_int         := hG0_int)
      (hF'_meas       := hGp0_meas)
      (h_bound        := h_bound)
      (bound_integrable := hInt)
      (h_diff         := h_diff)
  have hRewr : (fun t => ∫ x, G t x ∂ gaussianReal 0 v) = gaussianTilt F v := by
    funext t; simpa [G] using (hShift t).symm
  have hDerVal :
      (∫ x, G' 0 x ∂ gaussianReal 0 v)
        = (v : ℝ) * ∫ x, deriv F x ∂ gaussianReal 0 v := by
    simp [G', integral_const_mul]
  have : HasDerivAt (gaussianTilt F v)
            (∫ x, G' 0 x ∂ gaussianReal 0 v) 0 := by
    simpa [hRewr] using hDer.2
  simpa [hDerVal]

lemma gaussianTilt_hasDerivAt_right
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    HasDerivAt (gaussianTilt F v)
      ((v : ℝ) * ∫ x, deriv F x ∂ gaussianReal 0 v) 0 := by
  rcases gaussianTilt_deriv_dom (v := v) hMod with
    ⟨C, m, hCpos, hDom⟩
  have hInt :
      Integrable (fun x => |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m)
        (gaussianReal 0 v) :=
    gaussianTilt_deriv_dom_integrable (v := v) (F := F) hMod C m hCpos
  let δ : ℝ := 1
  let B : ℝ → ℝ :=
    fun x => |F x| * ((|(v : ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|)
  have hB_int :
      Integrable B (gaussianReal 0 v) := by
    have hFcont : Continuous F := hF.continuous
    simpa [B] using
      gaussianTilt_domination_bound (v := v) (F := F) δ (by norm_num) hMod hFcont
  have hFmeas : Measurable F := hF.continuous.measurable
  have hF_int : Integrable F (gaussianReal 0 v) := by
    have h1 : ∀ x, ‖F x‖ ≤ B x := by
      intro x
      have hA : 1 ≤ (|(v : ℝ)| * δ + 1) := by
        have hvn : 0 ≤ |(v : ℝ)| * δ :=
          mul_nonneg (abs_nonneg _) (by norm_num)
        nlinarith
      have hB' : 1 ≤ |x| + 1 := by nlinarith [abs_nonneg x]
      have hC : 1 ≤ Real.exp (δ * |x|) := by
        have : 0 ≤ δ * |x| := by nlinarith [abs_nonneg x]
        simpa using Real.one_le_exp_iff.mpr this
      have hprod :
          1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1) * Real.exp (δ * |x|)) := by
        have hAB := one_le_mul_of_one_le_of_one_le hA hB'
        have := one_le_mul_of_one_le_of_one_le hAB hC
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have := mul_le_mul_of_nonneg_left hprod (abs_nonneg (F x))
      simpa [B, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using this
    exact (hB_int.mono' (hFmeas.aestronglyMeasurable) (ae_of_all _ h1))
  exact gaussianTilt_hasDerivAt_right_aux hv hF hF_int hDom hInt

/-- **Stein's lemma (centered Gaussian)**; split proof via the two derivative lemmas.
This version assumes moderate growth (which implies the needed integrability). -/
theorem stein_lemma_gaussianReal
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ}
    (hF  : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    ∫ x, x * F x ∂ (gaussianReal 0 v)
      = (v : ℝ) * ∫ x, deriv F x ∂ (gaussianReal 0 v) := by
  -- Left and right derivatives of the Gaussian tilt at 0 coincide and identify both sides.
  have hL := gaussianTilt_hasDerivAt_left  (v := v) hv hF hMod
  have hR := gaussianTilt_hasDerivAt_right (v := v) hv hF hMod
  -- Uniqueness of the derivative at a point gives equality of the derivative values.
  exact hL.unique hR

/-- Measure-level Gaussian integration by parts (from Stein's lemma).
Assumes moderate growth (no separate integrability hypotheses needed). -/
lemma gaussianReal_integration_by_parts
    {F : ℝ → ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hF  : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    ∫ x, x * F x ∂(gaussianReal 0 v)
      = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) :=
  stein_lemma_gaussianReal hv hF hMod

lemma IsCenteredGaussianRV.expectation_comp
    {g : Ω → ℝ} {v : ℝ≥0} (hg : IsCenteredGaussianRV g v)
    (hgAE : AEMeasurable g ℙ)
    {Φ : ℝ → ℝ} (hInt : Integrable Φ (gaussianReal 0 v)) :
    ∫ ω, Φ (g ω) ∂ℙ = ∫ x, Φ x ∂(gaussianReal 0 v) := by
  unfold IsCenteredGaussianRV IsGaussianRV at hg
  have hIntLaw : Integrable Φ (Measure.map g ℙ) := by simpa [hg] using hInt
  have hΦ_aesm : AEStronglyMeasurable Φ (Measure.map g ℙ) := hIntLaw.aestronglyMeasurable
  have hMap := integral_map hgAE hΦ_aesm
  rw [← hMap, hg]

-- The second moment is integrable under any centered Gaussian.
lemma integrable_sq_gaussianReal_centered (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
  have hMom2 : Integrable (fun x : ℝ => (1 + |x|)^2) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) 2
  have hMeas : Measurable (fun x : ℝ => x^2) :=
    (continuous_id.pow 2).measurable
  have hAE :
      ∀ᵐ x ∂ gaussianReal 0 v, ‖x^2‖ ≤ (1 + |x|)^2 := by
    refine ae_of_all _ (fun x => ?_)
    have hx0 : 0 ≤ |x| := abs_nonneg _
    have hxle : |x| ≤ 1 + |x| := by nlinarith
    have hmul : |x| * |x| ≤ (1 + |x|) * (1 + |x|) :=
      mul_le_mul hxle hxle hx0 (by nlinarith)
    simpa [Real.norm_eq_abs, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hMom2.mono' (hMeas.aestronglyMeasurable) hAE

lemma IsCenteredGaussianRV.secondMoment
    {g : Ω → ℝ} {v : ℝ≥0}
    (hg : IsCenteredGaussianRV g v) (hgMeas : Measurable g) :
    ∫ ω, (g ω)^2 ∂ℙ = v := by
  unfold IsCenteredGaussianRV IsGaussianRV at hg
  have hIntGauss : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) :=
    integrable_sq_gaussianReal_centered (v := v)
  have hIntLaw : Integrable (fun x : ℝ => x^2) (Measure.map g ℙ) := by
    simpa [hg] using hIntGauss
  have hΦ_aesm :
      AEStronglyMeasurable (fun x : ℝ => x^2) (Measure.map g ℙ) :=
    hIntLaw.aestronglyMeasurable
  have hMap := integral_map hgMeas.aemeasurable hΦ_aesm
  rw [← hMap, hg, integral_sq_gaussianReal_centered (v := v)]

lemma gaussianRV_integration_by_parts
    {g : Ω → ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hg : IsCenteredGaussianRV g v) (hgMeas : Measurable g)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hMod : HasModerateGrowth F) :
    ∫ ω, g ω * F (g ω) ∂ℙ
      = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by
  have hΦ1m : Measurable (fun x : ℝ => x * F x) :=
    (measurable_id.mul hF.continuous.measurable)
  have hΦ2m : Measurable (fun x : ℝ => deriv F x) :=
    (hF.continuous_deriv le_rfl).measurable
  classical
  have hModCopy : HasModerateGrowth F := hMod
  rcases hMod with ⟨C, m, hCpos, hFbound, hF'bound⟩
  have hMom_m : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) m
  have hMom_m1 : Integrable (fun x : ℝ => (1 + |x|) ^ (m + 1)) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) (m + 1)
  have hInt1 : Integrable (fun x => x * F x) (gaussianReal 0 v) := by
    have hAE : ∀ᵐ x ∂ gaussianReal 0 v,
        ‖x * F x‖ ≤ C * (1 + |x|) ^ (m + 1) := by
      refine ae_of_all _ (fun x => ?_)
      have hFabs : ‖F x‖ ≤ C * (1 + |x|) ^ m := by
        simpa [Real.norm_eq_abs] using hFbound x
      have hineq : ‖x * F x‖ = |x| * ‖F x‖ := by
        simp [Real.norm_eq_abs]
      have hx : |x| ≤ 1 + |x| := by nlinarith [abs_nonneg x]
      calc
        ‖x * F x‖ = |x| * ‖F x‖ := hineq
        _ ≤ (1 + |x|) * ‖F x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        _ ≤ (1 + |x|) * (C * (1 + |x|) ^ m) :=
          mul_le_mul_of_nonneg_left hFabs (by nlinarith [abs_nonneg x])
        _ = C * (1 + |x|) ^ (m + 1) := by
          calc
            (1 + |x|) * (C * (1 + |x|) ^ m)
                = C * ((1 + |x|) * (1 + |x|) ^ m) := by ring
            _ = C * ((1 + |x|) ^ m * (1 + |x|)) := by ring
            _ = C * (1 + |x|) ^ (m + 1) := by
                  simp [pow_succ, mul_comm]
    have hDomInt : Integrable (fun x => C * (1 + |x|) ^ (m + 1)) (gaussianReal 0 v) :=
      (hMom_m1.const_mul C)
    exact hDomInt.mono' (hΦ1m.aestronglyMeasurable) hAE
  have hInt2 : Integrable (fun x => deriv F x) (gaussianReal 0 v) := by
    have hAE : ∀ᵐ x ∂ gaussianReal 0 v,
        ‖deriv F x‖ ≤ C * (1 + |x|) ^ m := by
      exact ae_of_all _ (fun x => by
        simpa [Real.norm_eq_abs] using hF'bound x)
    have hDomInt : Integrable (fun x => C * (1 + |x|) ^ m) (gaussianReal 0 v) :=
      (hMom_m.const_mul C)
    exact hDomInt.mono' ((hF.continuous_deriv le_rfl).measurable.aestronglyMeasurable) hAE
  have h1 := IsCenteredGaussianRV.expectation_comp (g := g) (v := v)
              hg hgMeas.aemeasurable hInt1
  have h2 := IsCenteredGaussianRV.expectation_comp (g := g) (v := v)
              hg hgMeas.aemeasurable hInt2
  calc
    ∫ ω, g ω * F (g ω) ∂ℙ
        = ∫ x, x * F x ∂(gaussianReal 0 v) := h1
    _ = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) :=
        gaussianReal_integration_by_parts (v := v) hv hF hModCopy
    _ = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by
        simp [h2]

lemma mul_pos_of_pos_of_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb_ne : b ≠ 0) : 0 < a * b := by
  have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_ne)
  exact Left.mul_pos ha hb_pos

theorem gaussian_integration_by_parts_general
    {g : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hg : IsGaussianRV g μ v) (hgMeas : Measurable g)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hMod : HasModerateGrowth F) :
    ∫ ω, (g ω - μ) * F (g ω) ∂ℙ = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by
  let Y : Ω → ℝ := fun ω => g ω - μ
  have hY : IsCenteredGaussianRV Y v := by
    unfold IsCenteredGaussianRV IsGaussianRV Y
    -- map g by (· - μ)
    have hmap :
        Measure.map (fun ω => g ω - μ) ℙ
          = (Measure.map g ℙ).map (fun x : ℝ => x - μ) := by
      change Measure.map ((fun x : ℝ => x - μ) ∘ g) ℙ
        = (Measure.map g ℙ).map (fun x : ℝ => x - μ)
      exact
        (Measure.map_map
          (hf := hgMeas)
          (hg := (measurable_id.sub measurable_const))
          (μ := ℙ) (f := g) (g := fun x : ℝ => x - μ)).symm
    calc
      Measure.map Y ℙ
          = (Measure.map g ℙ).map (fun x : ℝ => x - μ) := hmap
      _ = (gaussianReal μ v).map (fun x : ℝ => x - μ) := by
            simpa using
              congrArg (fun m : Measure ℝ =>
                Measure.map (fun x : ℝ => x - μ) m) hg
      _ = gaussianReal (μ - μ) v := gaussianReal_map_sub_const (μ := μ) (v := v) μ
      _ = gaussianReal 0 v := by simp
  have hYMeas : Measurable Y := hgMeas.sub measurable_const
  let F_shifted : ℝ → ℝ := fun x => F (x + μ)
  have hF_shifted : ContDiff ℝ 1 F_shifted :=
    hF.comp (contDiff_id.add contDiff_const)
  have h_deriv : deriv F_shifted = fun x => deriv F (x + μ) := by
    funext x
    have hAdd : HasDerivAt (fun x => x + μ) 1 x := by
      simpa using (hasDerivAt_id x).add_const μ
    have hF' : HasDerivAt F (deriv F (x + μ)) (x + μ) :=
      (hF.differentiable one_ne_zero _).hasDerivAt
    exact deriv_comp_add_const F μ x
  have hMod_shifted : HasModerateGrowth F_shifted := by
    rcases hMod with ⟨C, m, hCpos, hFbound, hF'bound⟩
    refine ⟨C * (1 + |μ|) ^ m, m, ?_, ?_, ?_⟩
    · -- show 0 < C * (1 + |μ|)^m
      have hPowPos : 0 < (1 + |μ|) ^ m := by
        have hbase : 0 < 1 + |μ| := by nlinarith [abs_nonneg μ]
        simpa using pow_pos hbase m
      exact Left.mul_pos hCpos hPowPos
    · -- bound for F_shifted
      intro x
      have htri : |x + μ| ≤ |x| + |μ| := by
        simp [abs_add_le]
      have hone_le : 1 + |x + μ| ≤ 1 + |x| + |μ| := by
        have := add_le_add_left htri 1
        simpa [add_comm, add_left_comm, add_assoc] using this
      have hbase : 0 ≤ 1 + |x + μ| := add_nonneg (by norm_num) (abs_nonneg _)
      have hpow_le :
          (1 + |x + μ|) ^ m ≤ (1 + |x| + |μ|) ^ m :=
        Real.pow_le_pow_of_le_left hbase hone_le
      have hmul_le :
          (1 + |x| + |μ|) ^ m ≤ (1 + |μ|) ^ m * (1 + |x|) ^ m := by
        have hbase' : 0 ≤ 1 + |x| + |μ| := by
          have : 0 ≤ |x| := abs_nonneg _; have : 0 ≤ |μ| := abs_nonneg _
          nlinarith
        have hxy : 1 + |x| + |μ| ≤ (1 + |x|) * (1 + |μ|) := by
          have hxμ : 0 ≤ |x| * |μ| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          nlinarith
        have hpow' := Real.pow_le_pow_of_le_left (k := m) hbase' hxy
        have hfac : ((1 + |x|) * (1 + |μ|)) ^ m
                  = (1 + |μ|) ^ m * (1 + |x|) ^ m := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using mul_pow (1 + |x|) (1 + |μ|) m
        simpa [hfac]
          using hpow'
      have hF_at := hFbound (x + μ)
      have : |F (x + μ)| ≤ C * ((1 + |μ|) ^ m * (1 + |x|) ^ m) :=
        le_trans hF_at (by
          have hCnn : 0 ≤ C := le_of_lt hCpos
          exact mul_le_mul_of_nonneg_left
                  (le_trans hpow_le hmul_le) hCnn)
      simpa [F_shifted, mul_comm, mul_left_comm, mul_assoc]
        using this
    · -- derivative bound for F_shifted
      intro x
      have hF'd_at : |deriv F (x + μ)| ≤ C * (1 + |x + μ|) ^ m := hF'bound (x + μ)
      have hpow_le :
          (1 + |x + μ|) ^ m ≤ (1 + |μ|) ^ m * (1 + |x|) ^ m := by
        have htri : |x + μ| ≤ |x| + |μ| := by
          simp [abs_add_le]
        have hone : 1 + |x + μ| ≤ 1 + |x| + |μ| := by
          have := add_le_add_left htri 1
          simpa [add_comm, add_left_comm, add_assoc] using this
        have hbase : 0 ≤ 1 + |x + μ| := add_nonneg (by norm_num) (abs_nonneg _)
        have h1 : (1 + |x + μ|) ^ m ≤ (1 + |x| + |μ|) ^ m :=
          Real.pow_le_pow_of_le_left (k := m) hbase hone
        have hbase' : 0 ≤ 1 + |x| + |μ| := by
          have : 0 ≤ |x| := abs_nonneg _; have : 0 ≤ |μ| := abs_nonneg _
          nlinarith
        have hxy : 1 + |x| + |μ| ≤ (1 + |x|) * (1 + |μ|) := by
          have hxμ : 0 ≤ |x| * |μ| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          nlinarith
        have hpow' := Real.pow_le_pow_of_le_left (k := m) hbase' hxy
        have hfac : ((1 + |x|) * (1 + |μ|)) ^ m
                  = (1 + |μ|) ^ m * (1 + |x|) ^ m := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using mul_pow (1 + |x|) (1 + |μ|) m
        exact le_trans h1 (by simpa [hfac] using hpow')
      have hDerAbs : |deriv F_shifted x| = |deriv F (x + μ)| := by
        simp [h_deriv]
      simpa [F_shifted, mul_comm, mul_left_comm, mul_assoc, hDerAbs]
        using
          (le_trans (by simpa [hDerAbs] using hF'd_at)
                    (by
                      have hCnn : 0 ≤ C := le_of_lt hCpos
                      exact mul_le_mul_of_nonneg_left hpow_le hCnn))
  have hIBP :=
    gaussianRV_integration_by_parts (v := v) hv hY hYMeas hF_shifted hMod_shifted
  convert hIBP using 1
  · congr with ω
    simp [Y, F_shifted]
  · congr with ω
    aesop

end ProbabilityTheory

/-!
# Gaussian Integration by Parts on a real Hilbert space (finite-dimensional, covariant form)

This file lifts the one-dimensional Gaussian integration by parts (Stein's lemma)
formalized in `PhysLean/Probability/GaussianIntegrationByParts.lean` to a
**finite-dimensional** real Hilbert space `H` by decomposing along an
orthonormal basis and applying the 1D result on each coordinate, with a
conditioning argument.

Compared with a "standard" (identity covariance) statement, we work directly at
**covariant** generality: the coordinates may have arbitrary (nonnegative)
variances `τ i`. The covariance operator is then

```
Σ h = ∑ i, (τ i : ℝ) * ⟪h, w i⟫ • w i,
```

and the IBP identity reads

```
E[⟪g, h⟫ F(g)] = E[(fderiv ℝ F (g)) (Σ h)].
```

The proof strategy:
* Fix an orthonormal basis `w : OrthonormalBasis ι ℝ H` with `[Fintype ι]`.
* Model a centered Gaussian `g : Ω → H` via independent centered normal
  coordinates `c i : Ω → ℝ` of variances `τ i` so that `g = ∑ i, (c i) • w i`.
* Expand `⟪g, h⟫ = ∑ i (c i) * ⟪h, w i⟫` and reduce to a 1D conditional step
  along each coordinate, which contributes a factor `τ i`.

We package the modeling assumptions into a predicate `IsGaussianHilbert`.

NOTE: For this version we restrict to a *finite* orthonormal basis index `ι`
with `[Fintype ι]`. Extending to separable infinite-dimensional spaces follows
by dominated convergence and standard Gaussian moment facts.
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set

noncomputable section

namespace PhysLean.Probability.GaussianIBP

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]

-- Expectation notation (local; avoids referring to section variables in the expansion)
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂ℙ

/-- A centered Gaussian `H`-valued random variable modeled by coordinates -/
structure IsGaussianHilbert (g : Ω → H) where
  /-- Finite index type for the orthonormal basis. -/
  ι : Type*
  /-- Finite type structure on the index `ι`. -/
  fintype_ι : Fintype ι
  /-- An orthonormal basis of `H` indexed by `ι`. -/
  w : OrthonormalBasis ι ℝ H
  /-- Coordinate variances `τ i ≥ 0` (as `NNReal`). -/
  τ : ι → NNReal
  /-- Coordinate random variables `c i : Ω → ℝ`. -/
  c : ι → Ω → ℝ
  /-- Measurability of each coordinate process `c i`. -/
  c_meas : ∀ i, Measurable (c i)
  /-- Each coordinate `c i` is centered Gaussian with variance `τ i`. -/
  c_gauss : ∀ i, ProbabilityTheory.IsCenteredGaussianRV (c i) (τ i)
  /-- Independence of the family of coordinates `(c i)_i`. -/
  c_indep : ProbabilityTheory.iIndepFun c ℙ
  /-- Representation of `g` as the finite ONB sum `∑ i, (c i) • w i`. -/
  repr : g = fun ω => ∑ i, (c i ω) • w i

attribute [instance] IsGaussianHilbert.fintype_ι

/-- Moderate growth on `H → ℝ` -/
structure HasModerateGrowth {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : H → ℝ) where
  /-- A positive constant controlling the growth bound. -/
  C : ℝ
  /-- A natural exponent controlling the polynomial growth. -/
  m : ℕ
  /-- Positivity of the growth constant. -/
  Cpos : 0 < C
  /-- Pointwise bound on `F`: `|F z| ≤ C * (1 + ‖z‖) ^ m`. -/
  F_bound : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m
  /-- Operator-norm bound on the Fréchet derivative:
      `‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m`. -/
  dF_bound : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m

namespace HasModerateGrowth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma bound_dF_apply {F : H → ℝ} (hMG : HasModerateGrowth F) (z h : H) :
    ‖(fderiv ℝ F z) h‖ ≤ hMG.C * (1 + ‖z‖) ^ hMG.m * ‖h‖ := by
  have h₁ : ‖(fderiv ℝ F z) h‖ ≤ ‖fderiv ℝ F z‖ * ‖h‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h₂ : ‖fderiv ℝ F z‖ * ‖h‖ ≤ (hMG.C * (1 + ‖z‖) ^ hMG.m) * ‖h‖ :=
    mul_le_mul_of_nonneg_right (hMG.dF_bound z) (norm_nonneg _)
  exact h₁.trans h₂

end HasModerateGrowth

namespace Aux

variable {ι : Type*} [Fintype ι]
variable (w : OrthonormalBasis ι ℝ H)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
@[simp] lemma inner_decomp (x y : H) :
    ⟪x, y⟫_ℝ = ∑ i, (⟪x, w i⟫_ℝ) * (⟪y, w i⟫_ℝ) := by
  simpa [real_inner_comm] using (w.sum_inner_mul_inner x y).symm

end Aux

/-- Coordinates of `g` in the basis `w`. -/
@[simp] def coord {ι : Type*} [Fintype ι]
    (w : OrthonormalBasis ι ℝ H) (g : Ω → H) (i : ι) : Ω → ℝ :=
  fun ω => ⟪g ω, w i⟫_ℝ

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Explicit formula for the coordinates of `g` in the basis `w`. -/
lemma coord_repr_eq
    {g : Ω → H} (hg : IsGaussianHilbert g) (i : hg.ι) :
    coord hg.w g i = fun ω => ⟪g ω, hg.w i⟫_ℝ := rfl

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- On a Gaussian Hilbert model, the abstract coordinate map coincides with the
explicit coefficient process supplied by the model. -/
lemma coord_eq_c {g : Ω → H} (hg : IsGaussianHilbert g) :
    coord hg.w g = hg.c := by
  classical
  funext i ω
  -- Expand g ω and move inner through the finite sum.
  have hrepr : g ω = ∑ j : hg.ι, (hg.c j ω) • hg.w j := by
    simpa using congrArg (fun f => f ω) hg.repr
  simp only [coord, hrepr, sum_inner, inner_smul_left]
  -- The sum collapses to the i-th term by orthonormality.
  convert Finset.sum_eq_single i (fun j _ hij => ?_) (fun hi => ?_)
  · -- The i-th term is `c i ω * ⟪w i, w i⟫ = c i ω * 1`.
    simp
  · -- Off-diagonal terms `j ≠ i` are zero.
    simp [hij]
  · -- The index `i` is always in the universe.
    exact (hi (Finset.mem_univ i)).elim

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- For a Gaussian Hilbert model, each coordinate is centered normal with the
specified variance, and the coordinates are independent. -/
lemma coord_isGaussian_and_indep {g : Ω → H}
    (hg : IsGaussianHilbert g) :
    (∀ i, ProbabilityTheory.IsCenteredGaussianRV (coord hg.w g i) (hg.τ i)) ∧
    ProbabilityTheory.iIndepFun (coord hg.w g) ℙ := by
  classical
  have hcoord : coord hg.w g = hg.c := coord_eq_c (g := g) hg
  refine ⟨?std, ?indep⟩
  · intro i; simpa [hcoord] using hg.c_gauss i
  · simpa [hcoord] using hg.c_indep

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Coordinates are measurable functions (inherited from the model `c`). -/
lemma coord_measurable {g : Ω → H} (hg : IsGaussianHilbert g) :
    ∀ i, Measurable (coord hg.w g i) := by
  intro i
  simpa [coord_eq_c (g := g) hg] using hg.c_meas i

/-! ## Integrability lemmas and linearity under sums
The following lemmas gather the integrability facts needed to justify using
`integral_finset_sum`, pulling constants outside expectations, and swapping a
finite sum with an expectation.

We also provide a *weighted* linearity lemma for `fderiv` inside a finite sum.
section Integrability-/

section AuxMeasAndMoments

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]
variable {g : Ω → H} {F : H → ℝ}
variable {g : Ω → H} {F : H → ℝ}


omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] in
/-- `g` is measurable from the coordinate representation in the Gaussian model. -/
lemma IsGaussianHilbert.repr_measurable (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) :
    Measurable g := by
  classical
  let Φ : (hg.ι → ℝ) → H := fun y => ∑ i, (y i) • hg.w i
  have hΦ_cont : Continuous Φ := by
    have h_i : ∀ i : hg.ι, Continuous fun y : (hg.ι → ℝ) => (y i) • hg.w i := by
      intro i
      exact (continuous_apply i).smul continuous_const
    simpa [Φ] using
      (continuous_finset_sum (s := (Finset.univ : Finset hg.ι)) (fun i _ => h_i i))
  let cvec : Ω → (hg.ι → ℝ) := fun ω i => hg.c i ω
  have hcvec_meas : Measurable cvec := by
    refine measurable_pi_iff.mpr ?_
    intro i
    simpa [cvec] using hg.c_meas i
  have : Measurable (fun ω => Φ (cvec ω)) := hΦ_cont.measurable.comp hcvec_meas
  simpa [hg.repr, Φ, cvec] using this

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- For a centered real Gaussian random variable, the square is integrable. -/
lemma ProbabilityTheory.IsCenteredGaussianRV.integrable_sq
    {X : Ω → ℝ} {v : ℝ≥0}
    (hX : ProbabilityTheory.IsCenteredGaussianRV X v)
    (hX_meas : Measurable X) :
    Integrable (fun ω => (X ω)^2) := by
  have h_int_gauss : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
    simpa using ProbabilityTheory.integrable_sq_gaussianReal_centered (v := v)
  have hmap : Measure.map X (ℙ : Measure Ω) = gaussianReal 0 v := hX
  have h_int_map : Integrable (fun x : ℝ => x^2) (Measure.map X (ℙ : Measure Ω)) := by
    simpa [hmap] using h_int_gauss
  exact h_int_map.comp_measurable (μ := (ℙ : Measure Ω)) hX_meas

end AuxMeasAndMoments

section Integrability

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]
variable {g : Ω → H} {F : H → ℝ}

omit [CompleteSpace H][MeasurableSpace H] [BorelSpace H] in
/-- The finite sum of absolute Gaussian coordinates is integrable. -/
lemma integrable_sum_abs_coords (hg : IsGaussianHilbert g) :
    Integrable (fun ω => ∑ i, |coord hg.w g i ω|) := by
  classical
  have hL1_each : ∀ i : hg.ι, Integrable (fun ω => |coord hg.w g i ω|) := by
    intro i
    have hL2 : Integrable (fun ω => (coord hg.w g i ω) ^ 2) := by
      have hGauss := (coord_isGaussian_and_indep (g := g) hg).1 i
      have hMeas := coord_measurable (g := g) hg i
      exact ProbabilityTheory.IsCenteredGaussianRV.integrable_sq (X := coord hg.w g i)
        (v := hg.τ i) hGauss hMeas
    have h_major_int : Integrable (fun ω => 1 + (coord hg.w g i ω) ^ 2) := by
      simpa using (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hL2
    have h_meas : AEStronglyMeasurable (fun ω => |coord hg.w g i ω|) ℙ :=
      (coord_measurable (g := g) hg i).abs.aestronglyMeasurable
    have h_dom : ∀ᵐ ω ∂ℙ, ‖|coord hg.w g i ω|‖ ≤ 1 + (coord hg.w g i ω) ^ 2 := by
      refine Eventually.of_forall (fun ω => ?_)

      set x := coord hg.w g i ω
      have h0 : 0 ≤ x ^ 2 := sq_nonneg x
      have h1 : (1 : ℝ) ≤ 1 + x ^ 2 := by exact le_add_of_nonneg_right h0
      by_cases hx : |x| ≤ 1
      · exact (le_trans (by simpa [Real.norm_eq_abs, abs_abs] using hx)
          (by simpa [Real.norm_eq_abs, abs_abs, add_comm] using h1))
      · have hgt : 1 < |x| := not_le.mp hx
        have habs_nonneg : 0 ≤ |x| := abs_nonneg x
        have h_le_sq : |x| ≤ |x| * |x| := by
          have := mul_le_mul_of_nonneg_left (le_of_lt hgt) habs_nonneg
          simpa [one_mul] using this
        have h_le_sq' : |x| ≤ x^2 := by simpa [pow_two, sq_abs] using h_le_sq
        have hx2_le : x^2 ≤ 1 + x^2 := by
          have : 0 ≤ (1 : ℝ) := by exact zero_le_one
          simp
        have : |x| ≤ 1 + x^2 := le_trans h_le_sq' hx2_le
        simpa [Real.norm_eq_abs, abs_abs] using this
    exact h_major_int.mono' h_meas h_dom
  simpa using
    (integrable_finset_sum
      (s := (Finset.univ : Finset hg.ι))
      (f := fun i ω => |coord hg.w g i ω|)
      (by intro i _; simpa using hL1_each i))

omit [CompleteSpace H] in
/-- A finite-dimensional Gaussian has integrable norm. -/
lemma integrable_norm_of_gaussian (hg : IsGaussianHilbert g) :
    Integrable (fun ω => ‖g ω‖) := by
  classical
  have hcoord : coord hg.w g = hg.c := coord_eq_c (g := g) hg
  have hsum : ∀ ω, g ω = ∑ i, (hg.c i ω) • hg.w i := by
    intro ω
    simpa using congrArg (fun f => f ω) hg.repr
  have hnorm_w_one : ∀ i : hg.ι, ‖hg.w i‖ = (1 : ℝ) := by
    intro i; simp
  have h_norm_le : ∀ ω, ‖g ω‖ ≤ ∑ i, |coord hg.w g i ω| := by
    intro ω
    have h_step :
        ‖g ω‖ ≤ ∑ i, ‖(hg.c i ω) • hg.w i‖ := by
      calc
        ‖g ω‖ = ‖∑ i, (hg.c i ω) • hg.w i‖ := by simp [hsum ω]
        _ ≤ ∑ i, ‖(hg.c i ω) • hg.w i‖ := by
          simpa using
            (norm_sum_le (s := (Finset.univ : Finset hg.ι))
              (f := fun i => (hg.c i ω) • hg.w i))
    have h_to_abs :
        ∑ i, ‖(hg.c i ω) • hg.w i‖ = ∑ i, |hg.c i ω| := by
      refine Finset.sum_congr rfl (by
        intro i _
        simp [norm_smul, hnorm_w_one i] )
    have h_to_coord :
        ∑ i, |hg.c i ω| = ∑ i, |coord hg.w g i ω| := by
      refine Finset.sum_congr rfl (by
        intro i _; simp only [coord]; rw [← hcoord]; rfl )
    exact h_step.trans (by simp [h_to_abs, h_to_coord])
  have h_sum_int := integrable_sum_abs_coords (hg := hg)
  refine h_sum_int.mono' (hg.repr_measurable.norm.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun ω => by
    have : ‖‖g ω‖‖ = ‖g ω‖ := by
      simp
    simpa [this] using (h_norm_le ω))

omit [CompleteSpace H] in
/-- Backwards-compatible wrapper: the only cases used below are `p = 1` and
polynomial profiles, both covered by the previous lemmas. For `p = 1`
we provide this alias. -/
lemma integrable_norm_pow_one_of_gaussian (hg : IsGaussianHilbert g) :
    Integrable (fun ω => ‖g ω‖ ^ (1 : ℝ)) := by
  simpa using (integrable_norm_of_gaussian (hg := hg))

/-! ### A clean domination by polynomial moments

For p ≥ 0 and any natural m with p ≤ m, we have the pointwise bound
  x^p ≤ (1 + x)^m  for all x ≥ 0.
This yields integrability of ‖g‖^p from the polynomial moment
integrability already proved in `integrable_one_add_norm_pow`.
-/


/-- Scalar inequality: for `p ≥ 0`, `p ≤ m : ℕ`, and `x ≥ 0`,
we have `x^p ≤ (1 + x)^m`. -/
lemma rpow_le_one_add_pow_nat_of_le (p : ℝ) (m : ℕ)
    (hp : 0 ≤ p) (hp_le : p ≤ m) :
    ∀ x : ℝ, 0 ≤ x → x ^ p ≤ (1 + x) ^ m := by
  intro x hx
  by_cases hxle1 : x ≤ 1
  · have hxp_le_one : x ^ p ≤ (1 : ℝ) ^ p :=
      Real.rpow_le_rpow hx hxle1 hp
    have hone : (1 : ℝ) ^ p = (1 : ℝ) := by simp
    have h1le : (1 : ℝ) ≤ (1 + x) ^ m := by
      have h01x : 1 ≤ 1 + x := by linarith
      have h0 : 0 ≤ 1 + x := by linarith
      simp only [ge_iff_le]
      exact one_le_pow₀ h01x
    exact (by
      have : x ^ p ≤ (1 : ℝ) := by simpa [hone] using hxp_le_one
      exact this.trans h1le)
  · have hx1 : 1 ≤ x := le_of_lt (lt_of_not_ge hxle1)
    have hxp_le_xm : x ^ p ≤ x ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hp_le
    have hx_nonneg : 0 ≤ x := hx
    have hx_le_1x : x ≤ 1 + x := by linarith
    have xpow_nat :
        (x : ℝ) ^ (m : ℝ) = (x ^ m : ℝ) := by
      simp
    have x_pow_le_one_add :
        (x ^ m : ℝ) ≤ (1 + x) ^ m :=
          ProbabilityTheory.Real.pow_le_pow_of_le_left hx hx_le_1x
    calc
      x ^ p ≤ x ^ (m : ℝ) := hxp_le_xm
      _ = (x ^ m : ℝ) := by simp [xpow_nat]
      _ ≤ (1 + x) ^ m := x_pow_le_one_add

section MeanIneqHelpers

open scoped BigOperators
open Finset

variable {ι : Type*}

/-- For `p ≥ 1` and nonnegative weights `z i ≥ 0`, the generalized mean inequality
(unnormalized) on a finite set `s`:

  (∑ i∈s, z i)^p ≤ (s.card : ℝ)^(p - 1) * ∑ i∈s, (z i)^p.

This is the equal-weights case of `Real.rpow_arith_mean_le_arith_mean_rpow`. -/
lemma sum_rpow_le_card_pow_sub_one_sum_rpow
    (s : Finset ι) (z : ι → ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∑ i ∈ s, z i) ^ p ≤ (s.card : ℝ) ^ (p - 1) * ∑ i ∈ s, (z i) ^ p := by
  classical
  by_cases h0 : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp h0
    have hp0 : 0 < p := by linarith
    simp [hs, hp0.ne']
  · have hcard_pos_nat : 0 < s.card := Nat.pos_of_ne_zero (by simpa using h0)
    have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hcard_pos_nat
    let c : ℝ := s.card
    have hc_pos : 0 < c := by simpa [c] using hcard_pos
    have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
    have hw_nonneg : ∀ i ∈ s, 0 ≤ c⁻¹ := fun _ _ => inv_nonneg.mpr hc_nonneg
    have hw_sum : ∑ i ∈ s, c⁻¹ = 1 := by
      simp [Finset.sum_const, nsmul_eq_mul, c, ne_of_gt hc_pos]
    have hmean :
        (∑ i ∈ s, c⁻¹ * z i) ^ p ≤ ∑ i ∈ s, c⁻¹ * (z i) ^ p :=
      Real.rpow_arith_mean_le_arith_mean_rpow
        (s := s) (w := fun _ => c⁻¹) (z := z) hw_nonneg hw_sum hz hp
    have hR : (∑ i ∈ s, c⁻¹ * (z i) ^ p) = c⁻¹ * ∑ i ∈ s, (z i) ^ p := by
      simp [mul_sum]
    have ha_nonneg : 0 ≤ ∑ i ∈ s, c⁻¹ * z i :=
      Finset.sum_nonneg (by
        intro i hi; exact mul_nonneg (inv_nonneg.mpr hc_nonneg) (hz i hi))
    have hmul :
        (c : ℝ) ^ p * (∑ i ∈ s, c⁻¹ * z i) ^ p
          ≤ (c : ℝ) ^ p * (c⁻¹ * ∑ i ∈ s, (z i) ^ p) := by
      exact mul_le_mul_of_nonneg_left (by simpa [hR] using hmean)
        (Real.rpow_nonneg hc_nonneg _)
    have c_mul_avg :
        c * (∑ i ∈ s, c⁻¹ * z i) = ∑ i ∈ s, z i := by
      calc
        c * (∑ i ∈ s, c⁻¹ * z i)
            = ∑ i ∈ s, c * (c⁻¹ * z i) := by simp [mul_sum]
        _ = ∑ i ∈ s, (c * c⁻¹) * z i := by
          refine Finset.sum_congr rfl (by intro i hi; simp [mul_assoc])
        _ = ∑ i ∈ s, z i := by
          simp [ne_of_gt hc_pos, mul_comm]
    have hL :
        (c : ℝ) ^ p * (∑ i ∈ s, c⁻¹ * z i) ^ p = (∑ i ∈ s, z i) ^ p := by
      have : (c * (∑ i ∈ s, c⁻¹ * z i)) ^ p
              = (c : ℝ) ^ p * (∑ i ∈ s, c⁻¹ * z i) ^ p :=
        Real.mul_rpow hc_nonneg ha_nonneg
      aesop
    have hpow_mul_right :
        (c : ℝ) ^ p * (c⁻¹ * ∑ i ∈ s, (z i) ^ p)
          = (c : ℝ) ^ (p - 1) * ∑ i ∈ s, (z i) ^ p := by
      have hpdecomp : (c : ℝ) ^ p = (c : ℝ) ^ (p - 1) * (c : ℝ) ^ 1 := by
        simpa [sub_eq_add_neg, Real.rpow_one, add_comm, add_left_comm, add_assoc] using
          (Real.rpow_add hc_pos (p - 1) (1 : ℝ))
      calc
        (c : ℝ) ^ p * (c⁻¹ * ∑ i ∈ s, (z i) ^ p)
            = ((c : ℝ) ^ (p - 1) * (c : ℝ) ^ 1) * (c⁻¹ * ∑ i ∈ s, (z i) ^ p) := by
              simp [hpdecomp]
        _ = (c : ℝ) ^ (p - 1) * ((c : ℝ) ^ 1 * (c⁻¹ * ∑ i ∈ s, (z i) ^ p)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _ = (c : ℝ) ^ (p - 1) * (∑ i ∈ s, (z i) ^ p) := by
          have : (c : ℝ) ^ 1 = c := by simp
          simp [this, ne_of_gt hc_pos]
    simpa [hL, hpow_mul_right] using hmul

end MeanIneqHelpers

section PolynomialMoments

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Finset

variable {g : Ω → H}


/-! 1D Gaussian moment helpers (all nat moments are finite). -/
namespace ProbabilityTheory

/-- All absolute moments `|x|^k` are integrable under any centered real Gaussian. -/
lemma integrable_abs_pow_gaussianReal_centered_nat
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (ProbabilityTheory.gaussianReal 0 v) := by
  have h_poly : Integrable (fun x : ℝ => (1 + |x|) ^ k)
      (ProbabilityTheory.gaussianReal 0 v) := by
    simpa using
      ProbabilityTheory.gaussianReal_integrable_one_add_abs_pow_centered (v := v) (k := k)
  have h_meas :
      AEStronglyMeasurable (fun x : ℝ => |x| ^ k) (ProbabilityTheory.gaussianReal 0 v) := by
    exact ((measurable_id'.abs.pow_const k)).aestronglyMeasurable
  have h_dom :
      ∀ᵐ x ∂(ProbabilityTheory.gaussianReal 0 v),
        ‖|x| ^ k‖ ≤ (1 + |x|) ^ k := by
    refine ae_of_all _ (fun x => ?_)
    have hx : 0 ≤ |x| := abs_nonneg x
    have hle : |x| ≤ 1 + |x| := by linarith
    have : |x| ^ k ≤ (1 + |x|) ^ k := ProbabilityTheory.Real.pow_le_pow_of_le_left hx hle
    simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx _)] using this
  exact h_poly.mono' h_meas h_dom

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Lift to an RV: a centered Gaussian RV has all finite absolute moments. -/
lemma IsCenteredGaussianRV.integrable_abs_pow_nat
    {X : Ω → ℝ} {v : ℝ≥0}
    (hX : ProbabilityTheory.IsCenteredGaussianRV X v)
    (hX_meas : Measurable X) (k : ℕ) :
    Integrable (fun ω => |X ω| ^ k) := by
  have hmap : Measure.map X (ℙ : Measure Ω) = ProbabilityTheory.gaussianReal 0 v := hX
  have h_int_map :
      Integrable (fun x : ℝ => |x| ^ k) (Measure.map X (ℙ : Measure Ω)) := by
    simpa [hmap] using
      integrable_abs_pow_gaussianReal_centered_nat (v := v) (k := k)
  exact h_int_map.comp_measurable (μ := (ℙ : Measure Ω)) hX_meas

end ProbabilityTheory

-- Monotonicity of natural powers on ℝ for nonnegative bases.
namespace Real

lemma pow_le_pow_of_le_left {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by exact ProbabilityTheory.Real.pow_le_pow_of_le_left ha hab

end Real

section FiniteOnbPowerDomination

open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory

variable {ι Ω H : Type*}
variable [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a finite orthonormal basis `w` and coefficients `c : ι → ℝ`, raise the
norm of the finite sum to a natural power and dominate it by the sum of powers
of the coefficients (generalized mean inequality, equal-weights case). -/
lemma norm_pow_nat_le_card_pow_pred_sum_abs_pow
  (w : OrthonormalBasis ι ℝ H) (c : ι → ℝ) (m : ℕ) (hm : 1 ≤ m) :
  ‖∑ i, c i • w i‖ ^ m ≤ (Fintype.card ι : ℝ) ^ (m - 1) * ∑ i, |c i| ^ m := by
  classical
  cases m with
  | zero => cases hm
  | succ k =>
    have h₁ : ‖∑ i, c i • w i‖ ≤ ∑ i, ‖c i • w i‖ := by
      simpa using norm_sum_le (s := (Finset.univ : Finset ι)) (f := fun i => c i • w i)
    have h₂ : ∀ i, ‖c i • w i‖ = |c i| := fun i => by
      -- `‖w i‖ = 1`
      have hw : ‖w i‖ = (1 : ℝ) := by simp
      simp [norm_smul, hw]
    have hsum_univ :
        ∑ i ∈ (Finset.univ : Finset ι), ‖c i • w i‖
          = ∑ i ∈ (Finset.univ : Finset ι), |c i| := by
      refine Finset.sum_congr rfl ?_
      intro i hi; simp [h₂ i]
    have hsum : ∑ i, ‖c i • w i‖ = ∑ i, |c i| := by
      simpa using hsum_univ
    let n := Nat.succ k
    have hnn : 0 ≤ ‖∑ i, c i • w i‖ := norm_nonneg _
    have h₁m : ‖∑ i, c i • w i‖ ^ n ≤ (∑ i, |c i|) ^ n := by
      exact Real.pow_le_pow_of_le_left hnn (by simpa [hsum] using h₁) n
    have hmean_main :
        (∑ i, |c i|) ^ n
          ≤ (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i| ^ n := by
      by_cases h0 : Fintype.card ι = 0
      · have : (Finset.univ : Finset ι) = ∅ := by
          simpa using Finset.card_eq_zero.mp h0
        simp [this, h0]
      · set s : Finset ι := Finset.univ
        set cR : ℝ := (Fintype.card ι : ℝ)
        have hc_pos_nat : 0 < Fintype.card ι := Nat.pos_of_ne_zero h0
        have hc_pos : 0 < cR := by
          have : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hc_pos_nat
          simpa [cR] using this
        have hw_nonneg : ∀ i ∈ s, 0 ≤ cR⁻¹ := fun _ _ => inv_nonneg.mpr (le_of_lt hc_pos)
        have hw_sum : ∑ i ∈ s, cR⁻¹ = 1 := by
          simp [s, cR, Finset.sum_const, nsmul_eq_mul, ne_of_gt hc_pos]
        have hz_nonneg : ∀ i ∈ s, 0 ≤ |c i| := by
          intro i _; exact abs_nonneg _
        have hmean :=
          Real.pow_arith_mean_le_arith_mean_pow (s := s)
            (w := fun _ => cR⁻¹) (z := fun i => |c i|)
            (hw := fun i hi => by exact hw_nonneg i hi)
            (hw' := by simpa [s] using hw_sum)
            (hz := fun i hi => hz_nonneg i hi)
            (n := n)
        have hL :
            (∑ i ∈ s, cR⁻¹ * |c i|) ^ n
              = (cR ^ n)⁻¹ * (∑ i, |c i|) ^ n := by
          have : (∑ i ∈ s, cR⁻¹ * |c i|) = cR⁻¹ * (∑ i, |c i|) := by
            simp [s, mul_sum]
          calc
            (∑ i ∈ s, cR⁻¹ * |c i|) ^ n
                = (cR⁻¹ * (∑ i, |c i|)) ^ n := by simp [this]
            _ = (cR⁻¹) ^ n * (∑ i, |c i|) ^ n := by
                  simpa using (mul_pow (cR⁻¹) (∑ i, |c i|) n)
            _ = (cR ^ n)⁻¹ * (∑ i, |c i|) ^ n := by
                  simp [inv_pow]
        have hR :
            (∑ i ∈ s, cR⁻¹ * (|c i|) ^ n)
              = cR⁻¹ * ∑ i, (|c i|) ^ n := by
          simp [s, mul_sum]
        have hrew : (cR ^ n)⁻¹ * (∑ i, |c i|) ^ n
                      ≤ cR⁻¹ * ∑ i, (|c i|) ^ n := by
          simpa [hL, hR, s] using hmean
        have hc_pow_pos : 0 < (cR : ℝ) ^ n := pow_pos hc_pos _
        have hmul := mul_le_mul_of_nonneg_left hrew (le_of_lt hc_pow_pos)
        have hc_ne : (cR : ℝ) ≠ 0 := ne_of_gt hc_pos
        have hc_pow_ne : (cR : ℝ) ^ n ≠ 0 := by exact pow_ne_zero _ hc_ne
        have hLcancel :
            cR ^ n * ((cR ^ n)⁻¹ * (∑ i, |c i|) ^ n) = (∑ i, |c i|) ^ n := by
          simp_all only [le_add_iff_nonneg_left, zero_le, norm_nonneg, Nat.succ_eq_add_one,
            Nat.cast_pos, Finset.mem_univ, inv_nonneg, Nat.cast_nonneg, imp_self, implies_true,
            sum_const, card_univ, nsmul_eq_mul, ne_eq, Nat.cast_eq_zero, not_false_eq_true,
            mul_inv_cancel₀, abs_nonneg, pow_pos, Nat.add_eq_zero_iff,
            one_ne_zero, and_false, pow_eq_zero_iff, mul_inv_cancel_left₀, cR, s, n]
        have hRcancel :
            cR ^ n * (cR⁻¹ * ∑ i, |c i| ^ n) = cR ^ k * ∑ i, |c i| ^ n := by
          have : cR * (cR ^ k * (cR⁻¹ * ∑ i, |c i| ^ n))
                  = cR ^ k * ∑ i, |c i| ^ n := by
            have hc_ne' : cR ≠ 0 := hc_ne
            calc
              cR * (cR ^ k * (cR⁻¹ * ∑ i, |c i| ^ n))
                  = cR ^ k * (cR * (cR⁻¹ * ∑ i, |c i| ^ n)) := by
                      simp [mul_left_comm]
              _ = cR ^ k * ((cR * cR⁻¹) * ∑ i, |c i| ^ n) := by
                      simp [mul_left_comm, mul_assoc]
              _ = cR ^ k * (1 * ∑ i, |c i| ^ n) := by
                      simp [hc_ne']
              _ = cR ^ k * ∑ i, |c i| ^ n := by simp
          simpa [n, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
        have hmul' :
            (∑ i, |c i|) ^ n ≤ cR ^ k * ∑ i, |c i| ^ n := by
          simpa [hLcancel, hRcancel] using hmul
        simpa [n, Nat.succ_sub_one, mul_comm, mul_left_comm, mul_assoc] using hmul'
    simpa [n] using (h₁m.trans hmean_main)

variable [MeasurableSpace H] [BorelSpace H]


/-- Integrability lift: if each `|c i|^m` is integrable (under `ℙ`) and `m ≥ 1`,
then `‖∑ i, c i • w i‖^m` is integrable (under `ℙ`). For `m = 0` it is the constant `1`. -/
lemma integrable_norm_pow_nat_of_onb_sum
  {Ω ι H : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  (w : OrthonormalBasis ι ℝ H) (c : ι → Ω → ℝ) (m : ℕ)
  (hc_meas : ∀ i, Measurable (c i))
  (hc_int : ∀ i, Integrable (fun ω => |c i ω| ^ m)) :
  Integrable (fun ω => ‖∑ i, c i ω • w i‖ ^ m) := by
  classical
  cases m with
  | zero =>
      simp
  | succ k =>
      let n := Nat.succ k
      have h_pt :
          ∀ ω, ‖∑ i, c i ω • w i‖ ^ n
                ≤ (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i ω| ^ n := by
        intro ω
        have := norm_pow_nat_le_card_pow_pred_sum_abs_pow (w := w) (c := fun i => c i ω) (m := n) (by aesop)
        simpa using this
      have h_sum_int : Integrable (fun ω => ∑ i, |c i ω| ^ n) := by
        have h_each : ∀ i, Integrable (fun ω => |c i ω| ^ n) := by
          intro i
          simpa [n] using hc_int i
        simpa using (integrable_finset_sum (s := (Finset.univ : Finset ι))
                    (f := fun i ω => |c i ω| ^ n) (fun i _ => h_each i))
      have h_rhs_int :
          Integrable (fun ω => (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i ω| ^ n) :=
        h_sum_int.const_mul _
      have h_meas_sum : Measurable (fun ω => ∑ i, c i ω • w i) := by
        classical
        let Φ : (ι → ℝ) → H := fun y => ∑ i, (y i) • w i
        have hΦ_cont : Continuous Φ := by
          have h_i : ∀ i : ι, Continuous fun y : (ι → ℝ) => (y i) • w i := by
            intro i
            exact (continuous_apply i).smul continuous_const
          simpa [Φ] using
            (continuous_finset_sum (s := (Finset.univ : Finset ι)) (fun i _ => h_i i))
        let cvec : Ω → (ι → ℝ) := fun ω i => c i ω
        have hcvec_meas : Measurable cvec := by
          refine measurable_pi_iff.mpr ?_
          intro i
          simpa [cvec] using hc_meas i
        change Measurable (Φ ∘ cvec)
        exact hΦ_cont.measurable.comp hcvec_meas
      have h_measL : AEStronglyMeasurable (fun ω => ‖∑ i, c i ω • w i‖ ^ n) (ℙ : Measure Ω) := by
        have : Measurable (fun ω => ‖∑ i, c i ω • w i‖) := h_meas_sum.norm
        exact (this.pow_const n).aestronglyMeasurable
      refine h_rhs_int.mono' h_measL (Filter.Eventually.of_forall ?_)
      intro ω
      have hR : 0 ≤ (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i ω| ^ n := by
        have : 0 ≤ ∑ i, |c i ω| ^ n := by
          exact Finset.sum_nonneg (by intro i _; exact pow_nonneg (abs_nonneg _) _)
        have hc : 0 ≤ (Fintype.card ι : ℝ) ^ (n - 1) := by
          exact pow_nonneg (by exact_mod_cast (Nat.cast_nonneg (Fintype.card ι))) _
        exact mul_nonneg hc this
      have hL : 0 ≤ ‖∑ i, c i ω • w i‖ ^ n := by exact pow_nonneg (norm_nonneg _) _
      have := h_pt ω
      simpa [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR] using this

end FiniteOnbPowerDomination

section GaussianONB_Moments

open MeasureTheory ProbabilityTheory Finset PhysLean.Probability.GaussianIBP

variable {Ω ι H : Type*}
variable [MeasureSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
variable [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H]

/-- If `g = ∑ i, c i • w i` with ONB `w` and each `c i` integrable in `|·|^m`,
then `‖g‖^m` is integrable (under `ℙ`). -/
lemma integrable_norm_pow_nat_of_onb_sum_of_gaussian_coords
  (w : OrthonormalBasis ι ℝ H) (c : ι → Ω → ℝ) (m : ℕ)
  (hc_meas : ∀ i, Measurable (c i))
  (hc_gauss : ∀ i, ProbabilityTheory.IsCenteredGaussianRV (c i) (0 : ℝ≥0)) :
  Integrable (fun ω => ‖∑ i, c i ω • w i‖ ^ m) := by
  classical
  have hc_int : ∀ i, Integrable (fun ω => |c i ω| ^ m) := by
    intro i
    exact ProbabilityTheory.IsCenteredGaussianRV.integrable_abs_pow_nat
      (hX := hc_gauss i) (hX_meas := hc_meas i) (k := m)
  exact integrable_norm_pow_nat_of_onb_sum
    (w := w) (c := c) (m := m) (hc_meas := hc_meas) (hc_int := hc_int)

/-- For the `IsGaussianHilbert` model, all natural moments of `‖g‖` are integrable (under `ℙ`). -/
lemma integrable_norm_pow_nat_of_gaussian
  {g : Ω → H} (hg : IsGaussianHilbert g) (m : ℕ) :
  Integrable (fun ω => ‖g ω‖ ^ m) := by
  classical
  cases m with
  | zero =>
      simp
  | succ k =>
      have h_repr : ∀ ω, g ω = ∑ i, (hg.c i ω) • hg.w i := fun ω =>
        by simpa using congrArg (fun f => f ω) hg.repr
      have h_meas : ∀ i, Measurable (hg.c i) := hg.c_meas
      have h_gauss : ∀ i, ProbabilityTheory.IsCenteredGaussianRV (hg.c i) (hg.τ i) := hg.c_gauss
      let mNat := Nat.succ k
      have h_int_sum :
          Integrable (fun ω => ‖∑ i, hg.c i ω • hg.w i‖ ^ mNat) := by
        have hc_int : ∀ i, Integrable (fun ω => |hg.c i ω| ^ mNat) := by
          intro i
          exact ProbabilityTheory.IsCenteredGaussianRV.integrable_abs_pow_nat
            (hX := h_gauss i) (hX_meas := h_meas i) (k := mNat)
        exact integrable_norm_pow_nat_of_onb_sum
          (w := hg.w) (c := hg.c) (m := mNat) (hc_meas := h_meas) (hc_int := hc_int)
      simpa [h_repr] using h_int_sum


end GaussianONB_Moments

end PolynomialMoments
open MeasureTheory ProbabilityTheory Finset PhysLean.Probability.GaussianIBP

namespace Real

/-- For `a, b ≥ 0` and `p ≥ 1`, `(a + b)^p ≤ 2^(p - 1) * (a^p + b^p)` (real-exponent version). -/
lemma add_rpow_le_mul_rpow_add_rpow {a b p : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 1 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hp1

/-- Nat-exponent version: for `a, b ≥ 0` and `n ≥ 1`,
    `(a + b)^n ≤ 2^(n - 1) * (a^n + b^n)`. -/
lemma add_pow_le_two_pow_mul_add_pow {a b : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 1 ≤ n) :
    (a + b) ^ n ≤ (2 : ℝ) ^ (n - 1) * (a ^ n + b ^ n) := by
  classical
  have hmean :
      ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) ^ n
        ≤ (1 / 2 : ℝ) * a ^ n + (1 / 2 : ℝ) * b ^ n := by
    let s := (Finset.univ : Finset (Fin 2))
    have hw_nonneg : ∀ i ∈ s, 0 ≤ (1 / 2 : ℝ) := by
      intro _ _; norm_num
    have hw_sum : ∑ i ∈ s, (1 / 2 : ℝ) = 1 := by
      simpa using by
        simp [s]
    have hz_nonneg : ∀ i ∈ s, 0 ≤ (if (i = 0) then a else b) := by
      intro i _; fin_cases i <;> simp [ha, hb]
    have h :=
      Real.pow_arith_mean_le_arith_mean_pow (s := s)
        (w := fun _ => (1 / 2 : ℝ))
        (z := fun i => if (i = 0) then a else b)
        (hw := hw_nonneg) (hw' := hw_sum) (hz := hz_nonneg) (n := n)
    have hL :
        (∑ i ∈ s, (1 / 2 : ℝ) * (if i = 0 then a else b)) =
          (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b := by
      simp; exact Fin.sum_univ_two fun i => if i = 0 then 2⁻¹ * a else 2⁻¹ * b
    clear hL
    simpa [s, Fin.sum_univ_succ, one_div] using h
  have h2pos : 0 ≤ (2 : ℝ) := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hmean (pow_nonneg h2pos n)
  have hL :
      (2 : ℝ) ^ n * (((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) ^ n)
        = (a + b) ^ n := by
    have := by
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun x => x ^ n) (by ring_nf : (1 / 2 : ℝ) * (a + b) = (1 / 2) * a + (1 / 2) * b)
    calc
      (2 : ℝ) ^ n * (((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) ^ n)
          = (2 : ℝ) ^ n * (((1 / 2 : ℝ) * (a + b)) ^ n) := by
              simp [mul_comm]
              exact id (Eq.symm this)
      _ = ((2 : ℝ) * (1 / 2 : ℝ)) ^ n * (a + b) ^ n := by simp [mul_pow]
      _ = (1 : ℝ) ^ n * (a + b) ^ n := by simp
      _ = (a + b) ^ n := by simp
  have hn_pos : 0 < n := Nat.succ_le_iff.mp hn
  have hR :
      (2 : ℝ) ^ n * ((1 / 2 : ℝ) * a ^ n + (1 / 2 : ℝ) * b ^ n)
        = (2 : ℝ) ^ (n - 1) * (a ^ n + b ^ n) := by
    have hn_eq : n = (n - 1) + 1 := by
      exact (Nat.succ_pred_eq_of_pos hn_pos).symm
    calc
      (2 : ℝ) ^ n * ((1 / 2 : ℝ) * a ^ n + (1 / 2 : ℝ) * b ^ n)
          = (2 : ℝ) ^ n * (1 / 2 : ℝ) * (a ^ n + b ^ n) := by ring
      _ = ((2 : ℝ) ^ ((n - 1) + 1) * (1 / 2 : ℝ)) * (a ^ n + b ^ n) := by
            rw [hn_eq]; rw [Nat.add_succ_sub_one]
      _ = ((2 : ℝ) ^ (n - 1) * 2 * (1 / 2 : ℝ)) * (a ^ n + b ^ n) := by
            simp [pow_succ, mul_comm, mul_assoc]
      _ = ((2 : ℝ) ^ (n - 1) * 1) * (a ^ n + b ^ n) := by
            simp
      _ = (2 : ℝ) ^ (n - 1) * (a ^ n + b ^ n) := by
            simp [mul_comm]
  exact add_pow_le ha hb n

end Real


open MeasureTheory ProbabilityTheory

omit [CompleteSpace H] in
/-- All polynomial profiles `(1 + ‖g‖)^m` are integrable. -/
lemma integrable_one_add_norm_pow
    (hg : IsGaussianHilbert g) (m : ℕ) :
    Integrable (fun ω => (1 + ‖g ω‖) ^ m) := by
  classical
  cases m with
  | zero => simp
  | succ m' =>
      let n := Nat.succ m'
      have h_dom : ∀ ω,
          (1 + ‖g ω‖) ^ n ≤
            (2 : ℝ) ^ (n - 1) * (1 + (‖g ω‖) ^ n) := by
        intro ω
        have hn : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le m')
        have h := Real.add_pow_le_two_pow_mul_add_pow
                    (a := (1 : ℝ)) (b := ‖g ω‖) (n := n)
                    (ha := by norm_num) (hb := norm_nonneg _) (hn := hn)
        simpa [one_pow, add_comm, add_left_comm, add_assoc] using h
      have h_int_right :
          Integrable (fun ω => 1 + (‖g ω‖) ^ n) := by
        have h1 : Integrable (fun _ : Ω => (1 : ℝ)) := by simp
        have h2 : Integrable (fun ω => (‖g ω‖) ^ n) :=
          integrable_norm_pow_nat_of_gaussian (hg := hg) (m := n)
        simpa using h1.add h2
      have h_int_dom :
          Integrable (fun ω => (2 : ℝ) ^ (n - 1) * (1 + (‖g ω‖) ^ n)) :=
        h_int_right.const_mul _
      have h_meas : AEStronglyMeasurable (fun ω => (1 + ‖g ω‖) ^ n) ℙ := by
        have : Measurable (fun ω => 1 + ‖g ω‖) :=
          (measurable_const).add (hg.repr_measurable.norm)
        exact (this.pow_const n).aestronglyMeasurable
      refine h_int_dom.mono' h_meas (Filter.Eventually.of_forall (fun ω => ?_))
      have hR : 0 ≤ (2 : ℝ) ^ (n - 1) * (1 + (‖g ω‖) ^ n) := by
        have h1 : 0 ≤ (2 : ℝ) ^ (n - 1) := pow_nonneg (by norm_num) _
        have h2 : 0 ≤ (1 + (‖g ω‖) ^ n) := add_nonneg (by norm_num) (pow_nonneg (norm_nonneg _) _)
        exact mul_nonneg h1 h2
      have hbase : 0 ≤ 1 + ‖g ω‖ := by nlinarith [norm_nonneg (g ω)]
      have hL : 0 ≤ (1 + ‖g ω‖) ^ n := pow_nonneg hbase _
      have := h_dom ω
      simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg hbase, abs_of_nonneg hR] using this

omit [CompleteSpace H] in
/-- Parameterized integrability: if `p ≥ 0` and `p ≤ m` for some natural `m`,
then `‖g‖^p` is integrable. -/
lemma integrable_norm_rpow_of_gaussian_of_nat_ub
    (hg : IsGaussianHilbert g) (p : ℝ) (hp : 0 ≤ p)
    (m : ℕ) (hp_le : p ≤ m) :
    Integrable (fun ω => ‖g ω‖ ^ p) := by
  classical
  have h_dom :
      ∀ ω, ‖g ω‖ ^ p ≤ (1 + ‖g ω‖) ^ m :=
    fun ω => rpow_le_one_add_pow_nat_of_le (p := p) (m := m) hp hp_le (‖g ω‖) (norm_nonneg _)
  have h_int_poly : Integrable (fun ω => (1 + ‖g ω‖) ^ m) :=
    integrable_one_add_norm_pow (hg := hg) (m := m)
  have h_meas : AEStronglyMeasurable (fun ω => ‖g ω‖ ^ p) ℙ := by
    have h1 : Measurable (fun ω => ‖g ω‖) := hg.repr_measurable.norm
    have h2 : Measurable (fun t : ℝ => t ^ p) := by
      measurability
    exact (h2.comp h1).aestronglyMeasurable
  refine h_int_poly.mono' h_meas (Filter.Eventually.of_forall ?_)
  intro ω
  have hR : 0 ≤ (1 + ‖g ω‖) ^ m := by
    have : 0 ≤ 1 + ‖g ω‖ := by nlinarith [norm_nonneg (g ω)]
    exact pow_nonneg this _
  have hL : 0 ≤ ‖g ω‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  simpa [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR] using h_dom ω

omit [CompleteSpace H] in
/-- All moments of the norm of a finite-dimensional Gaussian are finite (for `p ≥ 0`).
This wrapper chooses a natural upper bound `m ≥ p` by existence. -/
lemma integrable_norm_pow_of_gaussian
    (hg : IsGaussianHilbert g) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun ω => ‖g ω‖ ^ p) := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_ge p
  exact integrable_norm_rpow_of_gaussian_of_nat_ub (hg := hg) (p := p) hp (m := m) (hp_le := by exact_mod_cast hm)

omit [CompleteSpace H] in
/-- Convenience: natural moments are integrable. -/
lemma integrable_norm_pow_nat_of_gaussian'
    (hg : IsGaussianHilbert g) (k : ℕ) :
    Integrable (fun ω => (‖g ω‖) ^ k) := by
  have h := integrable_norm_rpow_of_gaussian_of_nat_ub (hg := hg)
              (p := (k : ℝ)) (hp := by exact_mod_cast (Nat.cast_nonneg k))
              (m := k) (hp_le := by exact_mod_cast (le_of_eq rfl))
  exact integrable_norm_pow_nat_of_gaussian hg k

omit [CompleteSpace H] in
/-- All polynomial profiles in the norm are integrable. -/
lemma integrable_one_add_norm_pow' (hg : IsGaussianHilbert g) (m : ℕ) :
    Integrable (fun ω => (1 + ‖g ω‖) ^ m) := by
  classical
  have h_term :
      ∀ k ∈ Finset.range (m + 1),
        Integrable (fun ω => (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    intro k hk
    have hk_int : Integrable (fun ω => (‖g ω‖) ^ k) := by
      cases k with
      | zero => simp
      | succ k' =>
          have h := integrable_norm_pow_of_gaussian (g := g) (hg := hg) (p := (Nat.succ k' : ℝ))
            (hp := by exact Nat.cast_nonneg' k'.succ)
          exact integrable_norm_pow_nat_of_gaussian hg (k' + 1)
    simpa using hk_int.const_mul (Nat.choose m k : ℝ)
  have h_sum :
      Integrable (fun ω =>
        ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    simpa using
      (integrable_finset_sum
        (s := Finset.range (m + 1))
        (f := fun k ω => (Nat.choose m k : ℝ) * (‖g ω‖) ^ k)
        (by intro k hk; exact h_term k hk))
  have : (fun ω => (1 + ‖g ω‖) ^ m)
      = (fun ω =>
          ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    funext ω
    simp [add_comm, add_pow, one_pow, mul_comm]
  simpa [this]

omit [CompleteSpace H] in
/-- Under polynomial growth of `F` and Gaussian tails of `g`, `F ∘ g` is integrable. -/
lemma integrable_F_of_growth
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    Integrable (fun ω => F (g ω)) := by
  have h_bound : ∀ ω, |F (g ω)| ≤ hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m :=
    fun ω => hF_growth.F_bound (g ω)
  have h_int_poly : Integrable (fun ω => (1 + ‖g ω‖) ^ hF_growth.m) := by
    simpa using integrable_one_add_norm_pow (hg := hg) (m := hF_growth.m)
  have h_int_bound : Integrable (fun ω => hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m) :=
    h_int_poly.const_mul hF_growth.C
  have hg_meas : Measurable g := hg.repr_measurable
  have hF_meas : Measurable F := hF_diff.continuous.measurable
  apply Integrable.mono h_int_bound (hF_meas.comp hg_meas).aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun ω => ?_)
  have hbase : 0 ≤ 1 + ‖g ω‖ := by nlinarith [norm_nonneg (g ω)]
  have hCabs : |hF_growth.C| = hF_growth.C := abs_of_nonneg (le_of_lt hF_growth.Cpos)
  have h1abs : |1 + ‖g ω‖| = 1 + ‖g ω‖ := abs_of_nonneg hbase
  simpa [Function.comp, Real.norm_eq_abs, hCabs, h1abs] using h_bound ω

omit [CompleteSpace H] in
/-- Each coordinate has finite moments; multiplying by `F(g)` preserves integrability. -/
lemma integrable_coord_mul_F
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) (i : hg.ι) :
    Integrable (fun ω => (coord hg.w g i ω) * F (g ω)) := by
  classical
  let c_i := coord hg.w g i
  have hc_i_L2 : Integrable (fun ω => c_i ω ^ 2) :=
    ProbabilityTheory.IsCenteredGaussianRV.integrable_sq
      (hX := (coord_isGaussian_and_indep hg).1 i)
      (hX_meas := (coord_measurable (g := g) hg i))
  have hF_L2 : Integrable (fun ω => F (g ω) ^ 2) := by
    have h_bound_sq :
        ∀ ω, |F (g ω) ^ 2| ≤ hF_growth.C ^ 2 * (1 + ‖g ω‖) ^ (2 * hF_growth.m) := by
      intro ω
      have hb : |F (g ω)| ≤ hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m :=
        hF_growth.F_bound (g ω)
      have hb2 : |F (g ω)| ^ 2
                    ≤ (hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m) ^ 2 :=
        Real.pow_le_pow_of_le_left (abs_nonneg _) hb 2
      have hR :
          (hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m) ^ 2
            = hF_growth.C ^ 2 * (1 + ‖g ω‖) ^ (2 * hF_growth.m) := by
        simp [pow_two, pow_mul, mul_comm, mul_left_comm, mul_assoc]
      simpa [abs_pow, hR] using hb2
    have h_int_poly :
        Integrable (fun ω => (1 + ‖g ω‖) ^ (2 * hF_growth.m)) := by
      simpa using integrable_one_add_norm_pow (hg := hg) (m := 2 * hF_growth.m)
    have h_int_bound := h_int_poly.const_mul (hF_growth.C ^ 2)
    have hg_meas : Measurable g := hg.repr_measurable
    have hF_meas : Measurable F := hF_diff.continuous.measurable
    refine h_int_bound.mono' ((hF_meas.comp hg_meas).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hpow_nonneg : 0 ≤ (1 + ‖g ω‖) ^ (2 * hF_growth.m) := by
      have : 0 ≤ 1 + ‖g ω‖ := by nlinarith [norm_nonneg (g ω)]
      exact pow_nonneg this _
    have hrhs_nonneg : 0 ≤ hF_growth.C ^ 2 * (1 + ‖g ω‖) ^ (2 * hF_growth.m) :=
      mul_nonneg (by exact sq_nonneg _) hpow_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hrhs_nonneg] using h_bound_sq ω
  have h_int_rhs :
      Integrable (fun ω => (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2)) :=
    (hc_i_L2.add hF_L2).const_mul (1 / 2 : ℝ)
  have hc_meas : Measurable c_i := (coord_measurable (g := g) hg i)
  have hFcomp_meas : Measurable (fun ω => F (g ω)) :=
    (hF_diff.continuous.measurable).comp hg.repr_measurable
  have h_meas_prod :
      AEStronglyMeasurable (fun ω => c_i ω * F (g ω)) ℙ :=
    (hc_meas.mul hFcomp_meas).aestronglyMeasurable
  have h_dom :
      ∀ ω, |c_i ω * F (g ω)| ≤ (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2) := by
    intro ω
    have hsq : 0 ≤ (|c_i ω| - |F (g ω)|) ^ 2 := sq_nonneg _
    have hcs' :
        2 * (|c_i ω| * |F (g ω)|) ≤ |c_i ω| ^ 2 + |F (g ω)| ^ 2 := by
      have := hsq
      nlinarith [pow_two (|c_i ω|), pow_two (|F (g ω)|)]
    have hcs :
        2 * |c_i ω * F (g ω)| ≤ |c_i ω| ^ 2 + |F (g ω)| ^ 2 := by
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hcs'
    have : |c_i ω * F (g ω)| ≤ (|c_i ω| ^ 2 + |F (g ω)| ^ 2) / 2 := by
      have hpos : (0 : ℝ) < 2 := by norm_num
      exact (le_div_iff₀' hpos).mpr hcs
    simpa [div_eq_mul_inv, one_div, pow_two, abs_pow, mul_add, mul_comm, mul_left_comm, mul_assoc]
      using this
  refine h_int_rhs.mono' h_meas_prod (Filter.Eventually.of_forall (fun ω => ?_))
  have hR : 0 ≤ (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2) := by
    have : 0 ≤ (c_i ω) ^ 2 + (F (g ω)) ^ 2 := by exact add_nonneg (sq_nonneg _) (sq_nonneg _)
    have : 0 ≤ (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2) :=
      mul_nonneg (by norm_num) this
    simpa using this
  exact h_dom ω

omit [CompleteSpace H] in
/-- The Fréchet derivative applied to a fixed direction is integrable under the growth bound. -/
lemma integrable_fderiv_apply
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F) (h : H) :
    Integrable (fun ω => (fderiv ℝ F (g ω)) h) := by
  have h_bound : ∀ ω, ‖(fderiv ℝ F (g ω)) h‖
      ≤ hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m * ‖h‖ :=
    fun ω => HasModerateGrowth.bound_dF_apply hF_growth (g ω) h
  have h_int_poly : Integrable (fun ω => (1 + ‖g ω‖) ^ hF_growth.m) := by
    simpa using integrable_one_add_norm_pow (hg := hg) (m := hF_growth.m)
  have h_int_bound : Integrable (fun ω => (hF_growth.C * ‖h‖) * ((1 + ‖g ω‖) ^ hF_growth.m)) :=
    h_int_poly.const_mul (hF_growth.C * ‖h‖)
  have hg_meas : Measurable g := hg.repr_measurable
  have hF_deriv_cont : Continuous (fderiv ℝ F) :=
    hF_diff.continuous_fderiv (Ne.symm (zero_ne_one' (WithTop ℕ∞)))
  have h_comp_meas : Measurable (fun ω => fderiv ℝ F (g ω)) :=
    hF_deriv_cont.measurable.comp hg_meas
  have h_apply_meas : Measurable (fun ω => (fderiv ℝ F (g ω)) h) :=
    (ContinuousLinearMap.apply ℝ ℝ h).measurable.comp h_comp_meas
  refine h_int_bound.mono' h_apply_meas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro ω
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_bound ω

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Interchange expectation with a finite sum. -/
lemma expectation_finset_sum
    (hg : IsGaussianHilbert g) --(hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F)
    (f : hg.ι → Ω → ℝ)
    (hint : ∀ i, Integrable (f i)) :
    𝔼[(fun ω => ∑ i, f i ω)] = ∑ i, 𝔼[(f i ·)] := by
  classical
  have hint' : ∀ i ∈ (Finset.univ : Finset hg.ι), Integrable (f i) := by
    intro i _; simpa using hint i
  change (∫ ω, (∑ i : hg.ι, f i ω) ∂ℙ) = ∑ i : hg.ι, (∫ ω, f i ω ∂ℙ)
  simpa using
    (integral_finset_sum (s := (Finset.univ : Finset hg.ι)) (f := fun i ω => f i ω) hint')

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Pull out a *constant* scalar factor from expectation. -/
lemma expectation_const_mul
    (c : ℝ) {f : Ω → ℝ} (_ : Integrable f) :
    𝔼[(fun ω => c * f ω)] = c * 𝔼[f] := by
  classical
  change (∫ ω, c * f ω ∂ℙ) = c * (∫ ω, f ω ∂ℙ)
  exact MeasureTheory.integral_const_mul c f

omit [CompleteSpace H] in
/-- Weighted version: pull a finite *weighted* sum inside a continuous linear
map applied pointwise, then exchange the finite sum with expectation. -/
lemma fderiv_expectation_weighted_sum
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F)
    (a : hg.ι → ℝ) :
    𝔼[(fun ω => (fderiv ℝ F (g ω)) (∑ i : hg.ι, (a i) • hg.w i))]
      = ∑ i : hg.ι, (a i) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] := by
  classical
  have hint : ∀ i : hg.ι, Integrable (fun ω => (fderiv ℝ F (g ω)) (hg.w i)) :=
    fun i => integrable_fderiv_apply (hg := hg) (hF_diff := hF_diff)
      (hF_growth := hF_growth) (h := hg.w i)
  have pointwise :
    (fun ω => (fderiv ℝ F (g ω)) (∑ i : hg.ι, (a i) • hg.w i))
      = (fun ω => ∑ i : hg.ι, (a i) * ((fderiv ℝ F (g ω)) (hg.w i))) := by
    funext ω
    have L : H →L[ℝ] ℝ := fderiv ℝ F (g ω)
    simp [map_sum, smul_eq_mul]
  calc
    𝔼[(fun ω => (fderiv ℝ F (g ω)) (∑ i : hg.ι, (a i) • hg.w i))]
        = 𝔼[(fun ω => ∑ i : hg.ι, (a i) * ((fderiv ℝ F (g ω)) (hg.w i)))] := by
          simp
    _ = ∑ i : hg.ι, 𝔼[(fun ω => (a i) * ((fderiv ℝ F (g ω)) (hg.w i)))] := by
          simpa using
            expectation_finset_sum (hg := hg)
              (f := fun i ω => (a i) * ((fderiv ℝ F (g ω)) (hg.w i)))
              (hint := fun i => (hint i).const_mul (a i))
    _ = ∑ i : hg.ι, (a i) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using expectation_const_mul (c := (a i))
              (f := fun ω => (fderiv ℝ F (g ω)) (hg.w i))
              ((hint i))

end Integrability

/-! ## Covariance operator as a continuous linear map (rank‑one sum)
We package the covariance weights `(τ i)` and basis vectors `(w i)` into a
bounded operator `Σ : H →L[ℝ] H`. This lets us present the IBP identity in a
clean, coordinate‑free form.
-/
section CovarianceOperator

variable {g : Ω → H}
section InnerProductSpace
open scoped InnerProductSpace

/-- The continuous linear map `x ↦ ⟪v, x⟫` for a fixed `v`.
Note: this is linear in `x` for general `RCLike 𝕜`. -/
def ContinuousLinearMap.innerSL (𝕜 : Type*) [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v : E) : E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟪v, x⟫_𝕜
      map_add' := by
        intro x y
        -- ⟪v, x + y⟫ = ⟪v, x⟫ + ⟪v, y⟫
        simpa using (inner_add_right v x y)
      map_smul' := by
        intro c x
        -- ⟪v, c • x⟫ = c * ⟪v, x⟫
        simpa using (inner_smul_right v x c) }
    ‖v‖
    (fun x => by
      simpa using (norm_inner_le_norm v x))

@[simp] lemma ContinuousLinearMap.innerSL_apply
    (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v x : E) :
    (ContinuousLinearMap.innerSL 𝕜 (E := E) v) x = ⟪v, x⟫_𝕜 := rfl

end InnerProductSpace

/-- Covariance operator `Σ` built from the finite spectral data `(w, τ)`.
It is the finite sum of rank‑one projections `h ↦ ⟪h, w i⟫ • w i`, scaled by `τ i`. -/
noncomputable def covOp (hg : IsGaussianHilbert g) : H →L[ℝ] H :=
  (Finset.univ : Finset hg.ι).sum fun i =>
    (hg.τ i : ℝ) •
      ContinuousLinearMap.smulRight (ContinuousLinearMap.innerSL ℝ (hg.w i)) (hg.w i)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
@[simp] lemma covOp_apply
    {g : Ω → H} (hg : IsGaussianHilbert g) (h : H) :
    (covOp (g := g) hg) h
      = ∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪h, hg.w i⟫_ℝ) • hg.w i := by
  classical
  rw [covOp, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [smul_smul, real_inner_comm]

/-- We write `Σ_hg` for the covariance operator associated
with a Gaussian Hilbert model `hg`. -/
notation3 "Σ_" hg => covOp (g := _ ) hg

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
lemma covOp_symmetric
    {g : Ω → H} (hg : IsGaussianHilbert g) (x y : H) :
    ⟪(covOp (g := g) hg) x, y⟫_ℝ = ⟪x, (covOp (g := g) hg) y⟫_ℝ := by
  classical
  have L : ⟪(covOp (g := g) hg) x, y⟫_ℝ
      = ∑ i : hg.ι, (hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ * ⟪hg.w i, y⟫_ℝ := by
    have hsum :=
      (sum_inner (𝕜 := ℝ) (E := H)
        (s := (Finset.univ : Finset hg.ι))
        (f := fun i => ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i)
        (x := y))
    simpa [covOp_apply (g := g) (hg := hg) x,
           real_inner_smul_left, mul_comm, mul_left_comm, mul_assoc]
      using hsum
  have R : ⟪x, (covOp (g := g) hg) y⟫_ℝ
      = ∑ i : hg.ι, (hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ * ⟪hg.w i, y⟫_ℝ := by
    have hsum :=
      (inner_sum (𝕜 := ℝ) (E := H)
        (s := (Finset.univ : Finset hg.ι))
        (f := fun i => ((hg.τ i : ℝ) * ⟪y, hg.w i⟫_ℝ) • hg.w i)
        (x := x))
    simpa [covOp_apply (g := g) (hg := hg) y,
           real_inner_smul_right, real_inner_comm,
           mul_comm, mul_left_comm, mul_assoc]
      using hsum
  aesop

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
lemma covOp_pos
    {g : Ω → H} (hg : IsGaussianHilbert g) (x : H) :
    0 ≤ ⟪(covOp (g := g) hg) x, x⟫_ℝ := by
  classical
  have hx :
      ⟪(covOp (g := g) hg) x, x⟫_ℝ
        = ∑ i : hg.ι, (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
    have hsum :
        ⟪∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ
          = ∑ i : hg.ι, ⟪((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ := by
      simpa using
        (sum_inner (𝕜 := ℝ) (E := H)
          (s := (Finset.univ : Finset hg.ι))
          (f := fun i => ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i)
          (x := x))
    have : ∑ i : hg.ι, ⟪((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ
            = ∑ i : hg.ι, (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      calc
        ⟪((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ
            = ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) * ⟪hg.w i, x⟫_ℝ := by
              rw [inner_smul_left]; simp
        _ = (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ * ⟪hg.w i, x⟫_ℝ) := by
              simp [mul_assoc]
        _ = (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ * ⟪x, hg.w i⟫_ℝ) := by
              simp [real_inner_comm]
        _ = (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
              simp [pow_two]
    simpa [covOp_apply (g := g) (hg := hg) x] using hsum.trans this
  have hterm : ∀ i : hg.ι, 0 ≤ (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
    intro i
    exact mul_nonneg (by exact (hg.τ i).coe_nonneg) (sq_nonneg _)
  have hsum : 0 ≤ ∑ i : hg.ι, (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 :=
    Finset.sum_nonneg (by intro i _; exact hterm i)
  aesop

end CovarianceOperator

/-! ## Linear test functions and covariance corollaries
For linear (or constant) test functions, the hypotheses are automatic. This
section packages some convenient special cases and algebraic consequences.
-/
section LinearTestFunctions

variable {g : Ω → H}

/-- Constant functions have moderate growth. -/
def hasModerateGrowth_const (c : ℝ) :
    HasModerateGrowth (fun _ : H => c) := by
  classical
  refine ⟨|c| + 1, 0, by exact add_pos_of_nonneg_of_pos (abs_nonneg c) zero_lt_one, ?F, ?dF⟩
  · intro z
    have : |c| ≤ |c| + 1 := by nlinarith [abs_nonneg c]
    simp [pow_zero]
  · intro z
    have : (0 : ℝ) ≤ |c| + 1 := by nlinarith [abs_nonneg c]
    simpa [fderiv_const, pow_zero, one_mul] using this

/-- Continuous linear maps have moderate growth with linear exponent. -/
def hasModerateGrowth_of_clm (L : H →L[ℝ] ℝ) :
    HasModerateGrowth (fun z : H => L z) := by
  classical
  refine ⟨‖L‖ + 1, 1, by exact add_pos_of_nonneg_of_pos (norm_nonneg (L : H →L[ℝ] ℝ)) zero_lt_one, ?F, ?dF⟩
  · intro z
    have h₁ : |L z| ≤ ‖L‖ * ‖z‖ := by simpa using L.le_opNorm z
    have h₂ : ‖L‖ * ‖z‖ ≤ (‖L‖ + 1) * (1 + ‖z‖) := by
      have hL : ‖L‖ ≤ ‖L‖ + 1 := by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)]
      have hz : ‖z‖ ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
      exact (mul_le_mul_of_nonneg_left hz (by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)])).trans
        (by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ), norm_nonneg z])
    have : |L z| ≤ (‖L‖ + 1) * (1 + ‖z‖) := h₁.trans h₂
    simpa [pow_one] using this
  · intro z
    have hderiv : fderiv ℝ (fun x : H => L x) z = L := by
      simp
    have hL' : ‖L‖ ≤ (‖L‖ + 1) * (1 + ‖z‖) := by
      have h1 : ‖L‖ ≤ ‖L‖ + 1 := by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)]
      have h2 : (1 : ℝ) ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
      have h3 : ‖L‖ * 1 ≤ (‖L‖ + 1) * (1 + ‖z‖) := by
        exact mul_le_mul h1 h2 (by norm_num) (by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)])
      simpa using h3
    simpa [hderiv, pow_one] using hL'

end LinearTestFunctions

/-! ## Parameterized 1D Stein step along a coordinate
Fix a basis index `i`. Write the coordinate vector as `x := coord w g i` and
collect the remaining coordinates as a parameter `y`. For

```
φ (x : ℝ) (y : (hg.ι \ {i}) → ℝ) := F ( ∑ j ≠ i, (y j) • w j + x • w i ),
```

the 1D Stein identity applied to `x` (with `y` fixed) yields

```
E[ x * φ(x,y) ] = (τ i) * E[ ∂_x φ(x,y) ].
```

Integrating both sides with respect to `y` gives the desired coordinate step.
We package this as a lemma whose proof will unfold the conditional expectation
arguments.
-/
section CoordLineAndDecomposition

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]

namespace CoordLine
section
/-- Index of the “complement” coordinates when singling out `i`. -/
@[simp] def Comp (ι : Type*) (i : ι) := { j : ι // j ≠ i }

variable {ι : Type*} [Fintype ι]
variable (w : OrthonormalBasis ι ℝ H)


/-- Finite instance for the complement subtype `{j // j ≠ i}`. -/
noncomputable instance instFintypeComp (i : ι) [DecidableEq ι] : Fintype (Comp ι i) :=
  Subtype.fintype (fun j : ι => j ≠ i)

/-- Build back a vector in `H` from a complement family and a coordinate along `w i`. -/
@[simp] def buildAlong [DecidableEq ι] (i : ι) (y : Comp ι i → ℝ) (x : ℝ) : H :=
  (∑ j : Comp ι i, (y j) • w j.1) + x • w i

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Finite-sum splitting identity along a fixed coordinate `i`. -/
lemma sum_split_along [DecidableEq ι] (i : ι) (a : ι → ℝ) :
  (∑ j, (a j) • w j) = (∑ j : Comp ι i, (a j.1) • w j.1) + (a i) • w i := by
  classical
  have hi : i ∈ (Finset.univ : Finset ι) := by simp
  have hsplit :
      (∑ j ∈ (Finset.univ.erase i), (a j) • w j) + (a i) • w i
        = ∑ j, (a j) • w j := by
    simp
  have hattach :
      (∑ j : {j // j ∈ (Finset.univ.erase i)}, (a j.1) • w j.1)
        = (∑ j ∈ (Finset.univ.erase i), (a j) • w j) := by
    simpa using
      (Finset.sum_attach (s := (Finset.univ.erase i))
        (f := fun j => (a j) • w j))
  let e : Comp ι i ≃ {j // j ∈ (Finset.univ.erase i)} :=
  { toFun := fun j =>
      ⟨j.1, by
        exact Finset.mem_erase.mpr ⟨j.2, by simp⟩⟩
    , invFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
    , left_inv := by
        intro j; cases j with
        | mk x hx => simp
    , right_inv := by
        intro j; cases j with
        | mk x hx =>
            rcases Finset.mem_erase.mp hx with ⟨hxi, hxU⟩
            simp}
  have htransport :
      (∑ j : {j // j ∈ (Finset.univ.erase i)}, (a j.1) • w j.1)
        = ∑ j : Comp ι i, (a j.1) • w j.1 := by
    refine Fintype.sum_equiv e.symm _ _ ?_
    intro j
    rfl
  have hsub :
      (∑ j ∈ (Finset.univ.erase i), (a j) • w j)
        = ∑ j : Comp ι i, (a j.1) • w j.1 := by
    calc
      (∑ j ∈ (Finset.univ.erase i), (a j) • w j)
          = (∑ j : {j // j ∈ (Finset.univ.erase i)}, (a j.1) • w j.1) := by
            simpa using hattach.symm
      _ = (∑ j : Comp ι i, (a j.1) • w j.1) := htransport
  simpa [hsub] using hsplit.symm

/-- With coefficients `c : ι → Ω → ℝ`, the random vector `g` splits into complement + i-th. -/
lemma repr_split_along
  {Ω : Type*} [MeasureSpace Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  (w : OrthonormalBasis ι ℝ H) (i : ι) (c : ι → Ω → ℝ) :
  ∀ ω, (∑ j, (c j ω) • w j) = buildAlong (w := w) i (fun j => c j.1 ω) (c i ω) := by
  intro ω
  classical
  simpa [buildAlong] using
    sum_split_along (w := w) (i := i) (a := fun j => c j ω)

/-- Decomposition of `g` along `w i`: complement + `i`-th coordinate. -/
lemma g_decomp_along
  {Ω : Type*} [MeasureSpace Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  {g : Ω → H}
  (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert (Ω := Ω) (H := H) g)
  [DecidableEq hg.ι]
  (i : hg.ι) :
  ∀ ω, g ω = buildAlong (w := hg.w) i (fun j => hg.c j.1 ω) (hg.c i ω) := by
  intro ω
  classical
  simpa [hg.repr] using
    repr_split_along (w := hg.w) (i := i) (c := hg.c) ω
end
end CoordLine
end CoordLineAndDecomposition

section JointLawFubini

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- If `Y` and `X` are independent measurable maps, the law of `(Y,X)` is the product of laws. -/
lemma map_pair_eq_prod_of_indep
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X (ℙ : Measure Ω)) :
  Measure.map (fun ω => (Y ω, X ω)) (ℙ : Measure Ω)
    = (Measure.map Y (ℙ : Measure Ω)).prod (Measure.map X (ℙ : Measure Ω)) := by
  classical
  exact
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (μ := (ℙ : Measure Ω)) (hf := hY.aemeasurable) (hg := hX.aemeasurable)).1 hIndep

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Change of variables for the pair map `(Y, X)`: no independence needed. -/
lemma integral_pair_change_of_variables
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  {φ : α × β → ℝ} (hφ_meas : Measurable φ) :
  ∫ ω, φ (Y ω, X ω) ∂ℙ = ∫ p, φ p ∂(Measure.map (fun ω => (Y ω, X ω)) ℙ) := by
  have hYX : AEMeasurable (fun ω => (Y ω, X ω)) ℙ := (hY.prodMk hX).aemeasurable
  have hφ : AEStronglyMeasurable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) :=
    hφ_meas.aestronglyMeasurable
  have h := MeasureTheory.integral_map hYX hφ
  simpa [Function.comp_def] using h.symm

/-- Same as `map_pair_eq_prod_of_indep` but only assuming a.e.-measurability of `Y` and `X`. -/
lemma map_pair_eq_prod_of_indep₀
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : AEMeasurable Y ℙ) (hX : AEMeasurable X ℙ)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ) :
  Measure.map (fun ω => (Y ω, X ω)) ℙ
    = (Measure.map Y ℙ).prod (Measure.map X ℙ) := by
  classical
  exact
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (μ := (ℙ : Measure Ω)) (hf := hY) (hg := hX)).1 hIndep

/-- Integration against the joint distribution of independent random variables
can be rewritten against the product of marginals (no integrability assumption needed). -/
lemma integral_joint_eq_integral_prod_of_indep_min
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  {φ : α × β → ℝ} (hφ_meas : Measurable φ) :
  ∫ ω, φ (Y ω, X ω) ∂ℙ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
  have hchg := integral_pair_change_of_variables Y X hY hX hφ_meas
  have hmap := map_pair_eq_prod_of_indep Y X hY hX hIndep
  simp [hchg, hmap]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/- Transfer L¹-finiteness from composition to pushforward measure via change of variables. -/
/-- Change of variables for the pair map `(Y, X)` (no independence needed). -/
lemma lintegral_map_pair_eq_lintegral_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    {φ : α × β → ℝ} (hφ_meas : Measurable φ) :
    ∫⁻ p, (‖φ p‖₊ : ℝ≥0∞) ∂(Measure.map (fun ω => (Y ω, X ω)) ℙ)
      = ∫⁻ ω, (‖φ (Y ω, X ω)‖₊ : ℝ≥0∞) ∂ℙ := by
  have h_meas_norm : Measurable (fun p : α × β => (‖φ p‖₊ : ℝ≥0∞)) := by
    have h_norm_phi_meas : Measurable fun p => ‖φ p‖ := hφ_meas.norm
    have h_ofReal_meas : Measurable ENNReal.ofReal := ENNReal.measurable_ofReal
    simp only [measurable_coe_nnreal_ennreal_iff]
    exact Measurable.nnnorm hφ_meas
  refine lintegral_map h_meas_norm ?_
  exact Measurable.prodMk hY hX

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Transfer integrability from the composition `φ ∘ (Y,X)` to `φ` under the push-forward law. -/
lemma integrable_map_pair_of_integrable_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    {φ : α × β → ℝ} (hφ_meas : Measurable φ)
    (hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
    Integrable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) := by
  classical
  have hφ_aes : AEStronglyMeasurable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) :=
    hφ_meas.aestronglyMeasurable
  have h_norm_id :=
    lintegral_map_pair_eq_lintegral_comp Y X hY hX hφ_meas
  have hFin_comp : HasFiniteIntegral (fun ω => φ (Y ω, X ω)) ℙ := hInt.hasFiniteIntegral
  have hFin_push :
      HasFiniteIntegral φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) := by
    refine (hasFiniteIntegral_def φ (Measure.map (fun ω => (Y ω, X ω)) ℙ)).mpr ?_
    exact lt_of_eq_of_lt h_norm_id hFin_comp
  exact ⟨hφ_aes, hFin_push⟩

/-- Transfer integrability from the push-forward law to the product law, using independence. -/
lemma integrable_prod_of_integrable_map_pair_of_indep
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    {φ : α × β → ℝ} --(hφ_meas : Measurable φ)
    (hInt_map : Integrable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ)) :
    Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
  have hmap :
      Measure.map (fun ω => (Y ω, X ω)) ℙ
        = (Measure.map Y ℙ).prod (Measure.map X ℙ) :=
    map_pair_eq_prod_of_indep Y X hY hX hIndep
  simpa [hmap] using hInt_map

/-- Transfer integrability from the composition to the product law (needed for Fubini). -/
lemma integrable_on_prod_of_indep_of_integrable_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    {φ : α × β → ℝ} (hφ_meas : Measurable φ)
    (hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
    Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
  have hInt_map :=
    integrable_map_pair_of_integrable_comp Y X hY hX hφ_meas hInt
  exact
    integrable_prod_of_integrable_map_pair_of_indep
      Y X hY hX hIndep hInt_map

/-- Wrapper with the original name/signature kept for compatibility:
the integrability assumption is not needed for the equality, so it is ignored. -/
lemma integral_joint_eq_integral_prod_of_indep
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  {φ : α × β → ℝ}
  (hφ_meas : Measurable φ)
  (_hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
  ∫ ω, φ (Y ω, X ω) ∂ℙ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
  integral_joint_eq_integral_prod_of_indep_min Y X hY hX hIndep hφ_meas

/-- Fubini factorisation when `Y` and `X` are independent. -/
lemma integral_pair_via_prod
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    {Ψ : α → β → ℝ}
    (hΨ_meas : Measurable (fun p : α × β => Ψ p.1 p.2))
    (hInt : Integrable (fun ω => Ψ (Y ω) (X ω)) ℙ) :
    ∫ ω, Ψ (Y ω) (X ω) ∂ℙ
      = ∫ y, ∫ x, Ψ y x ∂(Measure.map X ℙ) ∂(Measure.map Y ℙ) := by
  classical
  set φ : α × β → ℝ := fun p => Ψ p.1 p.2
  have h1 :=
    integral_joint_eq_integral_prod_of_indep_min Y X hY hX hIndep (hφ_meas := hΨ_meas)
  have hInt_prod :
      Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
    integrable_on_prod_of_indep_of_integrable_comp
      Y X hY hX hIndep (hφ_meas := hΨ_meas) (hInt := by simpa [φ] using hInt)
  have h2 :
      ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ))
        = ∫ y, ∫ x, Ψ y x ∂(Measure.map X ℙ) ∂(Measure.map Y ℙ) := by
    simpa [φ] using
      MeasureTheory.integral_prod
        (μ := Measure.map Y ℙ) (ν := Measure.map X ℙ) φ hInt_prod
  simpa [φ] using (h1.trans h2)

/-- If `X` is a real-valued random variable with Gaussian law `gaussianReal 0 v`,
independent of `Y`, and if `ω ↦ φ (Y ω, X ω)` is integrable, then `φ` is integrable
with respect to the product measure `(map Y ℙ) × (gaussianReal 0 v)`.

This is a Gaussian specialization of `integrable_on_prod_of_indep_of_integrable_comp`. -/
lemma integrable_phi_on_mapY_prod_gauss
  {α : Type*} [MeasurableSpace α]
  (Y : Ω → α) (X : Ω → ℝ)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  (v : ℝ≥0) (hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 v)
  {φ : α × ℝ → ℝ} (hφ_meas : Measurable φ)
  (hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
  Integrable φ ((Measure.map Y ℙ).prod (ProbabilityTheory.gaussianReal 0 v)) := by
  have hInt_prod :
      Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
    integrable_on_prod_of_indep_of_integrable_comp
      Y X hY hX hIndep hφ_meas hInt
  simpa [hXlaw] using hInt_prod

lemma integrable_psi_on_mapY_prod_gauss
  {α : Type*} [MeasurableSpace α]
  (Y : Ω → α) (X : Ω → ℝ)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  (v : ℝ≥0) (hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 v)
  {ψ : α × ℝ → ℝ} (hψ_meas : Measurable ψ)
  (hInt : Integrable (fun ω => ψ (Y ω, X ω)) ℙ) :
  Integrable ψ ((Measure.map Y ℙ).prod (ProbabilityTheory.gaussianReal 0 v)) := by
  have hInt_prod :
      Integrable ψ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
    integrable_on_prod_of_indep_of_integrable_comp
      Y X hY hX hIndep hψ_meas hInt
  simpa [hXlaw] using hInt_prod

end JointLawFubini

section SliceCalculus

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]

namespace CoordLine

variable {ι : Type*} [Fintype ι]
variable (w : OrthonormalBasis ι ℝ H) (i : ι)

/-- The linear map `ℝ →L[ℝ] H`, `x ↦ x • w i`. -/
@[simp] def lineCLM : ℝ →L[ℝ] H := (1 : ℝ →L[ℝ] ℝ).smulRight (w i)

/-- Affine line map `x ↦ z + x • w i`. -/
@[simp] def line (z : H) : ℝ → H := fun x => z + (lineCLM (w := w) (i := i)) x

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
lemma line_def (z : H) (x : ℝ) : line (w := w) (i := i) z x = z + x • w i := rfl

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Chain rule for the 1D slice of a `C¹` test `F : H → ℝ`. -/
lemma deriv_F_along (F : H → ℝ) (hF : ContDiff ℝ 1 F) (z : H) :
  ∀ x, deriv (fun t => F (line (w := w) (i := i) z t)) x
        = (fderiv ℝ F (line (w := w) (i := i) z x)) (w i) := by
  intro x
  have hline : HasFDerivAt (line (w := w) (i := i) z)
      (lineCLM (w := w) (i := i)) x :=
    (lineCLM (w := w) (i := i)).hasFDerivAt.const_add z
  have hF' : HasFDerivAt F (fderiv ℝ F (line (w := w) (i := i) z x))
      (line (w := w) (i := i) z x) :=
    (hF.differentiable one_ne_zero _).hasFDerivAt
  have hcomp := hF'.comp x hline
  have hderiv :
      HasDerivAt (fun t => F (line (w := w) (i := i) z t))
        (((fderiv ℝ F (line (w := w) (i := i) z x)).comp
            (lineCLM (w := w) (i := i))) 1) x := by
    change HasDerivAt (F ∘ line (w := w) (i := i) z)
      (((fderiv ℝ F (line (w := w) (i := i) z x)).comp
          (lineCLM (w := w) (i := i))) 1) x
    exact hcomp.hasDerivAt
  have hCLM1 : (lineCLM (w := w) (i := i)) 1 = w i := by
    simp [lineCLM]
  simpa [ContinuousLinearMap.comp_apply, hCLM1] using hderiv.deriv

/-!
Split moderateGrowth_along into general affine lemmas and a thin ONB wrapper.
-/
namespace AffineModerateGrowth

open Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Basic affine bound along a line:
`1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + |x|)`. -/
lemma one_add_norm_comp_affine_le
    (z : E) (L : ℝ →L[ℝ] E) (x : ℝ) :
  1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + |x|) := by
  have h_tri : ‖z + L x‖ ≤ ‖z‖ + ‖L x‖ := norm_add_le _ _
  have h_op : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have hx : ‖x‖ = |x| := by simp [Real.norm_eq_abs]
  have h1 : 1 + ‖z + L x‖ ≤ 1 + ‖z‖ + ‖L‖ * |x| := by
    calc
      1 + ‖z + L x‖ ≤ 1 + (‖z‖ + ‖L x‖) := by simpa only [add_assoc] using ((add_le_add_iff_left 1).mpr h_tri)
      _ = 1 + ‖z‖ + ‖L x‖ := by simp [add_assoc]
      _ ≤ 1 + ‖z‖ + ‖L‖ * |x| := by simpa [hx] using add_le_add_left h_op (1 + ‖z‖)
  have h_nonneg_z : 0 ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
  have h_one_le : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have h_left_mul : 1 + ‖z‖ ≤ (1 + ‖z‖) * (1 + |x|) :=
    le_mul_of_one_le_right h_nonneg_z h_one_le
  have h_x_le : |x| ≤ 1 + |x| := by linarith [abs_nonneg x]
  have h_right_mul : ‖L‖ * |x| ≤ ‖L‖ * (1 + |x|) :=
    mul_le_mul_of_nonneg_left h_x_le (norm_nonneg (L : ℝ →L[ℝ] E))
  have h_sum : 1 + ‖z‖ + ‖L‖ * |x| ≤ (1 + ‖z‖) * (1 + |x|) + ‖L‖ * (1 + |x|) :=
    add_le_add h_left_mul h_right_mul
  have : (1 + ‖z‖) * (1 + |x|) + ‖L‖ * (1 + |x|) = (1 + ‖z‖ + ‖L‖) * (1 + |x|) := by
    simp [mul_add, add_comm, add_left_comm, add_assoc, mul_comm]
  calc
    1 + ‖z + L x‖ ≤ 1 + ‖z‖ + ‖L‖ * |x| := h1
    _ ≤ (1 + ‖z‖ + ‖L‖) * (1 + |x|) := by simpa using (le_trans h_sum (le_of_eq this))

/-- Power version of the previous bound. -/
lemma pow_le_pow_one_add_norm_comp_affine
    (z : E) (L : ℝ →L[ℝ] E) (x : ℝ) (m : ℕ) :
  (1 + ‖z + L x‖) ^ m ≤ ((1 + ‖z‖ + ‖L‖) * (1 + |x|)) ^ m := by
  have hbase : 0 ≤ 1 + ‖z + L x‖ := by nlinarith [norm_nonneg (z + L x)]
  exact Real.pow_le_pow_of_le_left hbase (one_add_norm_comp_affine_le z L x) m

/-- Chain rule for slicing `F : E → ℝ` along an affine line `x ↦ z + L x`. -/
lemma deriv_comp_affine
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) (z : E) (L : ℝ →L[ℝ] E) (x : ℝ) :
  deriv (fun t => F (z + L t)) x = (fderiv ℝ F (z + L x)) (L 1) := by
  have hline : HasFDerivAt (fun t : ℝ => z + L t) L x := L.hasFDerivAt.const_add z
  have hF' : HasFDerivAt F (fderiv ℝ F (z + L x)) (z + L x) :=
    (hF.differentiable one_ne_zero _).hasFDerivAt
  have hcomp := hF'.comp x hline
  have : HasDerivAt (fun t => F (z + L t))
          (((fderiv ℝ F (z + L x)).comp L) 1) x := hcomp.hasDerivAt
  simpa [ContinuousLinearMap.comp_apply] using this.deriv

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma bound_dF_apply {F : H → ℝ} (hMG : HasModerateGrowth F) (z h : H) :
    ‖(fderiv ℝ F z) h‖ ≤ hMG.C * (1 + ‖z‖) ^ hMG.m * ‖h‖ := by
  have h_op : ‖(fderiv ℝ F z) h‖ ≤ ‖fderiv ℝ F z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
  have h_coeff_nonneg : 0 ≤ ‖h‖ := norm_nonneg _
  have h_body_le : ‖fderiv ℝ F z‖ * ‖h‖ ≤ (hMG.C * (1 + ‖z‖) ^ hMG.m) * ‖h‖ :=
    mul_le_mul_of_nonneg_right (hMG.dF_bound z) h_coeff_nonneg
  exact h_op.trans h_body_le

/-- General affine bound: `1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + ‖x‖)` for L : E' →L[ℝ] E. -/
lemma one_add_norm_comp_affine_le'
    {E' E : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (L : E' →L[ℝ] E) (x : E') :
  1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + ‖x‖) := by
  have h_tri : ‖z + L x‖ ≤ ‖z‖ + ‖L x‖ := norm_add_le _ _
  have h_op : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have h1 : 1 + ‖z + L x‖ ≤ 1 + ‖z‖ + ‖L‖ * ‖x‖ := by
    calc
      1 + ‖z + L x‖ ≤ 1 + (‖z‖ + ‖L x‖) := by simpa [add_assoc] using (norm_add_le z (L x))
      _ = 1 + ‖z‖ + ‖L x‖ := by simp [add_assoc]
      _ ≤ 1 + ‖z‖ + ‖L‖ * ‖x‖ := by simpa using add_le_add_left h_op (1 + ‖z‖)
  have hx : ‖x‖ ≤ 1 + ‖x‖ := by nlinarith [norm_nonneg (x : E')]
  have hz : 0 ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg (z : E)]
  have h_left : 1 + ‖z‖ ≤ (1 + ‖z‖) * (1 + ‖x‖) := le_mul_of_one_le_right hz (by nlinarith [norm_nonneg (x : E')])
  have h_right : ‖L‖ * ‖x‖ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left hx (norm_nonneg (L : E' →L[ℝ] E))
  have h_sum := add_le_add h_left h_right
  have : (1 + ‖z‖) * (1 + ‖x‖) + ‖L‖ * (1 + ‖x‖) = (1 + ‖z‖ + ‖L‖) * (1 + ‖x‖) := by ring
  exact (le_trans h1 (le_trans (le_of_eq (by simp)) h_sum)).trans (le_of_eq (by simp [this]))

/-- Power version. -/
lemma pow_le_pow_one_add_norm_comp_affine'
    {E' E : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (L : E' →L[ℝ] E) (x : E') (m : ℕ) :
  (1 + ‖z + L x‖) ^ m ≤ ((1 + ‖z‖ + ‖L‖) * (1 + ‖x‖)) ^ m := by
  have hbase : 0 ≤ 1 + ‖z + L x‖ := by nlinarith [norm_nonneg (z + L x)]
  exact Real.pow_le_pow_of_le_left hbase (one_add_norm_comp_affine_le' z L x) m

/-- Value bound after composing F : E → ℝ with affine line x ↦ z + L x (real parameter). -/
lemma growth_bound_comp_affine_real_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ}
    (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
    (z : E) (L : ℝ →L[ℝ] E) :
  ∀ x : ℝ,
    |F (z + L x)|
      ≤ (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m) * (1 + |x|) ^ hMG.m := by
  intro x
  have hF := hMG.F_bound (z + L x)
  have hpow := pow_le_pow_one_add_norm_comp_affine' (z := z) (L := L) (x := x) (m := hMG.m)
  have hx : ‖x‖ = |x| := by simp
  calc
    |F (z + L x)| ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m := hF
    _ ≤ hMG.C * (((1 + ‖z‖ + ‖L‖) * (1 + ‖x‖)) ^ hMG.m) := by exact mul_le_mul_of_nonneg_left hpow (le_of_lt hMG.Cpos)
    _ = (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m) * (1 + |x|) ^ hMG.m := by simp [mul_pow, hx, mul_comm, mul_left_comm]

/-- Derivative bound after composing F : E → ℝ with affine line x ↦ z + L x (real parameter). -/
lemma growth_bound_comp_affine_real_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ}
    (hF_diff : ContDiff ℝ 1 F)
    (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
    (z : E) (L : ℝ →L[ℝ] E) :
  ∀ x : ℝ,
    |deriv (fun t => F (z + L t)) x|
      ≤ (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖)) * (1 + |x|) ^ hMG.m := by
  intro x
  have hderiv := deriv_comp_affine (hF := hF_diff) (z := z) (L := L) (x := x)
  have hL1 : ‖L 1‖ ≤ ‖L‖ := by
    simpa [Real.norm_eq_abs, abs_one, mul_one] using (L.le_opNorm (1 : ℝ))
  have h_df : ‖fderiv ℝ F (z + L x)‖ ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m := hMG.dF_bound _
  have hval :
      |(fderiv ℝ F (z + L x)) (L 1)| ≤ ‖fderiv ℝ F (z + L x)‖ * ‖L 1‖ := by
    simpa [Real.norm_eq_abs] using
      (ContinuousLinearMap.le_opNorm (fderiv ℝ F (z + L x)) (L 1))
  have h1 :
      |deriv (fun t => F (z + L t)) x|
        ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m * ‖L‖ := by
    have := calc
      |(fderiv ℝ F (z + L x)) (L 1)|
            ≤ ‖fderiv ℝ F (z + L x)‖ * ‖L 1‖ := hval
      _ ≤ ‖fderiv ℝ F (z + L x)‖ * ‖L‖ := mul_le_mul_of_nonneg_left hL1 (norm_nonneg _)
      _ ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m * ‖L‖ :=
            mul_le_mul_of_nonneg_right h_df (norm_nonneg _)
    simpa [hderiv, mul_comm, mul_left_comm, mul_assoc] using this
  have hL_le : ‖L‖ ≤ 1 + ‖L‖ := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
  have coeff_nonneg :
      0 ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m :=
    mul_nonneg (le_of_lt hMG.Cpos) (pow_nonneg (by nlinarith [norm_nonneg (z + L x)]) _)
  have h2 :
      hMG.C * (1 + ‖z + L x‖) ^ hMG.m * ‖L‖
        ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m * (1 + ‖L‖) :=
    mul_le_mul_of_nonneg_left hL_le coeff_nonneg
  have hx : ‖x‖ = |x| := by simp
  have hpow₀ :=
    pow_le_pow_one_add_norm_comp_affine' (z := z) (L := L) (x := x) (m := hMG.m)
  have hpow' :
      (1 + ‖z + L x‖) ^ hMG.m
        ≤ (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + |x|) ^ hMG.m := by
    simpa [mul_pow, hx] using hpow₀
  have h3 :
      hMG.C * (1 + ‖z + L x‖) ^ hMG.m * (1 + ‖L‖)
        ≤ (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖)) * (1 + |x|) ^ hMG.m := by
    have t1 := mul_le_mul_of_nonneg_left hpow' (le_of_lt hMG.Cpos)
    have h1L : 0 ≤ 1 + ‖L‖ := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
    have t2 := mul_le_mul_of_nonneg_right t1 h1L
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_pow] using t2
  exact (h1.trans (h2.trans h3))

/-- Thin wrapper: moderate growth for x ↦ F (z + L x). -/
lemma moderateGrowth_comp_affine_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} (hF_diff : ContDiff ℝ 1 F)
    (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
    (z : E) (L : ℝ →L[ℝ] E) :
  ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + L x)) := by
  set A : ℝ := 1 + ‖z‖ + ‖L‖
  set C' : ℝ := hMG.C * A ^ hMG.m * (1 + ‖L‖)
  have hApos : 0 < A := by nlinarith [norm_nonneg z, norm_nonneg (L : ℝ →L[ℝ] E)]
  have hAmpos : 0 < A ^ hMG.m := pow_pos hApos _
  have hLpos : 0 < (1 + ‖L‖) := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
  have hC'pos : 0 < C' := mul_pos (mul_pos hMG.Cpos hAmpos) hLpos
  refine ⟨C', hMG.m, hC'pos, ?_, ?_⟩
  · intro x
    exact (growth_bound_comp_affine_real_value (hMG := hMG) (z := z) (L := L) x).trans (by
      have hfac : (hMG.C * A ^ hMG.m) ≤ C' := by
        have hL1 : 1 ≤ 1 + ‖L‖ := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
        have hnonneg : 0 ≤ hMG.C * A ^ hMG.m :=
          mul_nonneg (le_of_lt hMG.Cpos) (pow_nonneg (le_of_lt hApos) _)
        calc
          hMG.C * A ^ hMG.m = (hMG.C * A ^ hMG.m) * 1 := by ring
          _ ≤ (hMG.C * A ^ hMG.m) * (1 + ‖L‖) := mul_le_mul_of_nonneg_left hL1 hnonneg
          _ = C' := by simp [C']
      have hx_nonneg : 0 ≤ (1 + |x|) ^ hMG.m := pow_nonneg (by linarith [abs_nonneg x]) _
      exact mul_le_mul_of_nonneg_right hfac hx_nonneg)
  · intro x
    exact (growth_bound_comp_affine_real_deriv (hF_diff := hF_diff) (hMG := hMG) (z := z) (L := L) x).trans (by
      have hcoeff :
          hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖) = C' := by aesop
      have : (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖)) * (1 + |x|) ^ hMG.m
            = C' * (1 + |x|) ^ hMG.m := by simp [hcoeff]
      exact le_of_eq this)

end AffineModerateGrowth

open AffineModerateGrowth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
variable {ι : Type*} [Fintype ι]

variable (w : OrthonormalBasis ι ℝ H) (i : ι)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Wrapper: moderate growth along the ONB coordinate line. -/
lemma moderateGrowth_along
  (F : H → ℝ)
  (hF_diff : ContDiff ℝ 1 F)
  (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (z : H) :
  ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + x • w i)) := by
  have h := AffineModerateGrowth.moderateGrowth_comp_affine_real
            (hF_diff := hF_diff) (hMG := hMG) (z := z) (L := lineCLM (w := w) (i := i))
  simpa [lineCLM] using h

end CoordLine
end SliceCalculus

section OneDStepWithParameter

open MeasureTheory ProbabilityTheory
open CoordLine

variable {vτ : ℝ≥0}

/-- 1D Gaussian IBP along a coordinate line, with an external parameter `y`. -/
lemma gaussian_IBP_along_line
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (y : CoordLine.Comp ι i → ℝ) :
  ∫ (x : ℝ), x * (F (buildAlong (w := w) (i := i) y x)) ∂(ProbabilityTheory.gaussianReal 0 vτ)
    = (vτ : ℝ) * ∫ (x : ℝ), (deriv (fun t => F (buildAlong (w := w) (i := i) y t)) x)
        ∂(ProbabilityTheory.gaussianReal 0 vτ) := by
  classical
  let z : H := ∑ j : CoordLine.Comp ι i, (y j) • w j.1
  have hMG1D : ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + x • w i)) :=
    CoordLine.moderateGrowth_along (w := w) (i := i) F hF_diff hF_growth z
  have hF1D : ContDiff ℝ 1 (fun x : ℝ => F (z + x • w i)) := by
    exact hF_diff.comp ((contDiff_const.add (contDiff_id.smul contDiff_const)) : ContDiff ℝ 1 (fun x : ℝ => z + x • w i))
  by_cases hv : vτ = 0
  · subst hv
    simp [CoordLine.buildAlong, add_comm]
  · have hIBP :=
      ProbabilityTheory.gaussianReal_integration_by_parts
        (v := vτ) (hv := hv)
        (F := fun x : ℝ => F (z + x • w i))
        (hF := hF1D)
        (hMod := hMG1D)
    simpa [z, CoordLine.buildAlong, add_comm, add_left_comm, add_assoc] using hIBP

end OneDStepWithParameter

section SteinAlongOneCoordinate

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open CoordLine

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ProductIBP

open MeasureTheory

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- Fubini transport of a section-wise identity to the product. -/
lemma integral_prod_of_section_eq
  (μα : Measure α) (μβ : Measure β) (hα : SFinite μα) (hβ : SFinite μβ)
  {φ ψ : α × β → ℝ}
  (hφ_int : Integrable φ (μα.prod μβ))
  (hψ_int : Integrable ψ (μα.prod μβ))
  (hSec : ∀ a, ∫ b, φ (a, b) ∂μβ = ∫ b, ψ (a, b) ∂μβ) :
  ∫ p, φ p ∂(μα.prod μβ) = ∫ p, ψ p ∂(μα.prod μβ) := by
  classical
  haveI : SFinite μα := hα
  have hφ_prod :
      (∫ p, φ p ∂(μα.prod μβ))
        = (∫ a, ∫ b, φ (a, b) ∂μβ ∂μα) :=
    MeasureTheory.integral_prod (μ := μα) (ν := μβ) (f := φ) hφ_int
  have hψ_prod :
      (∫ p, ψ p ∂(μα.prod μβ))
        = (∫ a, ∫ b, ψ (a, b) ∂μβ ∂μα) :=
    MeasureTheory.integral_prod (μ := μα) (ν := μβ) (f := ψ) hψ_int
  have h_congr :
      (∫ a, ∫ b, φ (a, b) ∂μβ ∂μα)
        = (∫ a, ∫ b, ψ (a, b) ∂μβ ∂μα) :=
    MeasureTheory.integral_congr_ae (μ := μα)
      (Filter.Eventually.of_forall (fun a => by simpa using hSec a))
  simpa [hφ_prod, hψ_prod] using h_congr

end ProductIBP

namespace CoordLine

open Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Continuity of the affine ONB coordinate-line map (y,x) ↦ buildAlong w i y x. -/
lemma buildAlong_continuous
  (w : OrthonormalBasis ι ℝ H) (i : ι) :
  Continuous (fun p : (Comp ι i → ℝ) × ℝ => buildAlong (w := w) (i := i) p.1 p.2) := by
  classical
  have h_eval_sum :
      Continuous (fun y : Comp ι i → ℝ =>
        (∑ j : Comp ι i, (y j) • w j.1 : H)) := by
    refine
      continuous_finset_sum
        (s := (Finset.univ : Finset (Comp ι i)))
        (f := fun (j : Comp ι i) (y : Comp ι i → ℝ) => (y j) • w j.1)
        ?_
    intro j hj
    change Continuous
      ((fun y : Comp ι i → ℝ => y j) • (fun _ : Comp ι i → ℝ => w j.1))
    exact (continuous_apply j).smul continuous_const
  have h1 : Continuous (fun p : (Comp ι i → ℝ) × ℝ =>
      ∑ j : Comp ι i, (p.1 j) • w j.1) :=
    h_eval_sum.comp continuous_fst
  have h2 : Continuous (fun p : (Comp ι i → ℝ) × ℝ => p.2 • w i) :=
    continuous_snd.smul continuous_const
  change Continuous
    ((fun p : (Comp ι i → ℝ) × ℝ => ∑ j : Comp ι i, p.1 j • w j.1) +
      (fun p : (Comp ι i → ℝ) × ℝ => p.2 • w i))
  exact h1.add h2

section meas
variable [MeasurableSpace H] [BorelSpace H]

/-- Measurability of the affine ONB coordinate-line map. -/
lemma buildAlong_measurable
  (w : OrthonormalBasis ι ℝ H) (i : ι) :
  Measurable (fun p : (Comp ι i → ℝ) × ℝ => buildAlong (w := w) (i := i) p.1 p.2) :=
  (buildAlong_continuous (w := w) (i := i)).measurable

end meas

end CoordLine

/-- Pointwise-in-parameter 1D Stein identity along ONB coordinate `i`. -/
lemma stein_section_along_coord
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (vτ : ℝ≥0)
  (y : CoordLine.Comp ι i → ℝ) :
  ∫ x, x * F (CoordLine.buildAlong (w := w) (i := i) y x) ∂(ProbabilityTheory.gaussianReal 0 vτ)
    = (vτ : ℝ) * ∫ x, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) y t)) x
        ∂(ProbabilityTheory.gaussianReal 0 vτ) :=
  gaussian_IBP_along_line (w := w) (i := i) (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth) (y := y)

open ProductIBP CoordLine

/-- Core product-level Stein step (pulls the scalar `(vτ : ℝ)` inside the integrand). -/
lemma stein_coord_on_product_core
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (μY : Measure (CoordLine.Comp ι i → ℝ))
  (vτ : ℝ≥0)
  (hμY_sfinite : SFinite μY)
  (hInt_left :
     Integrable (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
       p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) (μY.prod (ProbabilityTheory.gaussianReal 0 vτ)))
  (hInt_right :
     Integrable (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
       (vτ : ℝ) * deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2)
     (μY.prod (ProbabilityTheory.gaussianReal 0 vτ))) :
  ∫ p, p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2) ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ))
    =
  ∫ p, (vτ : ℝ) * deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
    ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := by
  let γ : Measure ℝ := ProbabilityTheory.gaussianReal 0 vτ
  let φ : ((CoordLine.Comp ι i → ℝ) × ℝ) → ℝ :=
    fun p => p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)
  let ψ : ((CoordLine.Comp ι i → ℝ) × ℝ) → ℝ :=
    fun p => (vτ : ℝ) * deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
  have hSec : ∀ y, ∫ x, φ (y, x) ∂γ = ∫ x, ψ (y, x) ∂γ := by
    intro y
    simp [φ, ψ]; erw [stein_section_along_coord (w := w) (i := i) (F := F) (hF_diff := hF_diff)
      (hF_growth := hF_growth) (vτ := vτ) (y := y)]
    rw [← stein_section_along_coord w i F hF_diff hF_growth vτ y]; rw [stein_section_along_coord
        w i F hF_diff hF_growth vτ y]; simp; rw [integral_const_mul]
  exact ProductIBP.integral_prod_of_section_eq (μα := μY) (μβ := γ) (hα := hμY_sfinite)
    (hβ := (instSFiniteOfSigmaFinite)) (hφ_int := hInt_left) (hψ_int := hInt_right) (hSec := hSec)

/-- Backwards-compatible wrapper: original signature (keeps `(vτ : ℝ)` outside). -/
lemma stein_coord_on_product
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (μY : Measure (CoordLine.Comp ι i → ℝ))
  (vτ : ℝ≥0)
  (hμY_sfinite : SFinite μY)
  (hInt_left :
     Integrable
       (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
          p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2))
       (μY.prod (ProbabilityTheory.gaussianReal 0 vτ)))
  (hInt_right₀ :
     Integrable
       (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
          deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2)
       (μY.prod (ProbabilityTheory.gaussianReal 0 vτ))) :
  ∫ p, p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2) ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ))
    =
  (vτ : ℝ) * ∫ p, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
      ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := by
  have hInt_right := hInt_right₀.const_mul (vτ : ℝ)
  have hcore := stein_coord_on_product_core (w := w) (i := i) (F := F) (hF_diff := hF_diff)
    (hF_growth := hF_growth) (μY := μY) (vτ := vτ) (hμY_sfinite := hμY_sfinite)
    (hInt_left := hInt_left) (hInt_right := hInt_right)
  calc
      ∫ p, p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)
        ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ))
        =
      ∫ p, (vτ : ℝ) * deriv
          (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
        ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := hcore
    _ =
      (vτ : ℝ) *
      ∫ p, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
        ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := by
      simp [integral_const_mul]

namespace ProbabilityTheory

open MeasureTheory Set

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- If, for a measurable map `f : Ω → Π i, α i`, each coordinate has Dirac law at `c i`,
then the law of `f` is the Dirac mass at the whole point `c`.

Hypotheses:
- `μ` is a probability measure;
- the index type `ι` is countable (in particular, this includes finite index sets);
- each `α i` has measurable singletons;
- `f` is (globally) measurable;
- for each `i`, the pushforward of the coordinate `ω ↦ f ω i` is `dirac (c i)`.

Conclusion:
`map f μ = dirac c`. -/
lemma map_fun_dirac_of_coord_dirac
    [IsProbabilityMeasure μ] [Countable ι]
    [∀ i, MeasurableSingletonClass (α i)]
    {f : Ω → (∀ i, α i)} {c : ∀ i, α i}
    (hf : Measurable f)
    (hcoord : ∀ i, Measure.map (fun ω => f ω i) μ = Measure.dirac (c i)) :
    Measure.map f μ = Measure.dirac c := by
  classical
  have hAE_coord : ∀ i, ∀ᵐ ω ∂ μ, f ω i = c i := by
    intro i
    have hfi : Measurable (fun ω => f ω i) := (measurable_pi_apply i).comp hf
    have h1 : (Measure.map (fun ω => f ω i) μ) {c i} = 1 := by
      simpa using (by
        have := hcoord i
        simpa using congrArg (fun (m : Measure (α i)) => m {c i}) this)
    have : μ ((fun ω => f ω i) ⁻¹' {c i}) = 1 := by
      have hmap :
          (Measure.map (fun ω => f ω i) μ) {c i}
            = μ ((fun ω => f ω i) ⁻¹' {c i}) :=
        Measure.map_apply (μ := μ) (f := fun ω => f ω i) (s := {c i})
          hfi (measurableSet_singleton (c i))
      simpa [hmap] using h1
    have hcompl0 : μ (((fun ω => f ω i) ⁻¹' {c i})ᶜ) = 0 := by
      have : MeasurableSet ((fun ω => f ω i) ⁻¹' {c i}) :=
        hfi (measurableSet_singleton _)
      aesop
    exact (ae_iff.mpr hcompl0).mono (by intro ω hω; simpa using hω)
  have hAE_all : ∀ᵐ ω ∂ μ, ∀ i, f ω i = c i := by
    simpa using (ae_all_iff.mpr hAE_coord)
  have hAE_funext : f =ᵐ[μ] fun _ => c := by
    refine hAE_all.mono ?_
    intro ω hω; funext i; exact hω i
  ext s hs
  have hconst : Measurable fun (_ : Ω) => c := by
    simp
  have hf_map : (Measure.map f μ) s = μ (f ⁻¹' s) := Measure.map_apply hf hs
  have hconst_map : (Measure.map (fun (_ : Ω) => c) μ) s
      = μ ((fun _ => c) ⁻¹' s) := Measure.map_apply hconst hs
  have h_sets_ae :
      {ω | f ω ∈ s} =ᵐ[μ] {ω | (fun _ => c) ω ∈ s} :=
    hAE_funext.mono (by
      intro ω hω; aesop)
  have h_eq_measure : μ (f ⁻¹' s) = μ ((fun _ => c) ⁻¹' s) := by
    exact measure_congr h_sets_ae
  simpa [hf_map, hconst_map] using
    show (Measure.map f μ) s = (Measure.map (fun _ => c) μ) s from by
      aesop
  --done

end ProbabilityTheory

section Gauss1D_helpers

namespace ProbabilityTheory

/-- Under a centered real Gaussian law, `(1 + |x|)^n` is integrable for all `n`. -/
lemma integrable_one_add_abs_pow_nat_gaussian
    (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n) (ProbabilityTheory.gaussianReal 0 v) := by
  classical
  cases n with
  | zero =>
      simp
  | succ k =>
    have hdom :
        ∀ x : ℝ, (1 + |x|) ^ (Nat.succ k)
          ≤ (2 : ℝ) ^ (Nat.succ k - 1) * (1 + |x| ^ (Nat.succ k)) := by
      intro x
      have := Real.add_pow_le_two_pow_mul_add_pow
        (a := 1) (b := |x|) (n := Nat.succ k)
        (ha := by norm_num) (hb := by exact abs_nonneg x)
        (hn := Nat.succ_le_succ (Nat.zero_le k))
      simpa [one_pow] using this
    have h_meas : AEStronglyMeasurable
        (fun x : ℝ => (1 + |x|) ^ (Nat.succ k)) (ProbabilityTheory.gaussianReal 0 v) := by
      have hcont : Continuous (fun x : ℝ => (1 + |x|) ^ (Nat.succ k)) :=
        (continuous_const.add continuous_abs).pow _
      simpa using hcont.measurable.aestronglyMeasurable
    have h_rhs_int :
        Integrable (fun x : ℝ => (2 : ℝ) ^ (Nat.succ k - 1) * (1 + |x| ^ (Nat.succ k)))
          (ProbabilityTheory.gaussianReal 0 v) := by
      have h1 : Integrable (fun _ : ℝ => (2 : ℝ) ^ (Nat.succ k - 1))
            (ProbabilityTheory.gaussianReal 0 v) := by
        simp
      have h2 : Integrable (fun x : ℝ => |x| ^ (Nat.succ k))
            (ProbabilityTheory.gaussianReal 0 v) :=
        integrable_abs_pow_gaussianReal_centered_nat (v := v) (k := Nat.succ k)
      have : Integrable
          (fun x : ℝ =>
            (2 : ℝ) ^ (Nat.succ k - 1) + (2 : ℝ) ^ (Nat.succ k - 1) * |x| ^ (Nat.succ k))
          (ProbabilityTheory.gaussianReal 0 v) :=
        h1.add (h2.const_mul _)
      simpa [mul_add, mul_one] using this
    refine h_rhs_int.mono' h_meas (ae_of_all _ (fun x => ?_))
    have hL : 0 ≤ (1 + |x|) ^ (Nat.succ k) :=
      pow_nonneg (by linarith [abs_nonneg x]) _
    calc
      ‖(1 + |x|) ^ (Nat.succ k)‖
          = (1 + |x|) ^ (Nat.succ k) := by rw [Real.norm_of_nonneg hL]
      _ ≤ (2 : ℝ) ^ (Nat.succ k - 1) * (1 + |x| ^ (Nat.succ k)) := hdom x

end ProbabilityTheory
end Gauss1D_helpers

section AlongLine_integrability

open ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (w : OrthonormalBasis ι ℝ H) (i : ι)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [DecidableEq ι] in
/-- 1D along-line integrability (value): `x ↦ x · F(z + x • w i)` is `L¹(gauss)`. -/
lemma integrable_along_line_mul_gauss
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (z : H) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x * F (z + x • w i)) (ProbabilityTheory.gaussianReal 0 v) := by
  classical
  have hMG1D : ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + x • w i)) :=
    CoordLine.moderateGrowth_along (w := w) (i := i)
      (F := F) (hF_diff := hF_diff) (hMG := hF_growth) z
  have h_meas : AEStronglyMeasurable
      (fun x : ℝ => x * F (z + x • w i)) (ProbabilityTheory.gaussianReal 0 v) := by
    have hArg : Continuous (fun x : ℝ => z + (CoordLine.lineCLM (w := w) (i := i)) x) :=
      continuous_const.add (CoordLine.lineCLM (w := w) (i := i)).continuous
    have hcont : Continuous (fun x : ℝ => F (z + x • w i)) :=
      hF_diff.continuous.comp hArg
    exact (measurable_id.aestronglyMeasurable.mul hcont.measurable.aestronglyMeasurable)
  have h_dom :
      ∀ x, |x * F (z + x • w i)| ≤
        (hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m)
        * (|x| * (1 + |x|) ^ hF_growth.m) := by
    intro x
    have hv :=
      CoordLine.AffineModerateGrowth.growth_bound_comp_affine_real_value
        (hMG := hF_growth) (z := z) (L := CoordLine.lineCLM (w := w) (i := i)) x
    have hLnorm : ‖CoordLine.lineCLM (w := w) (i := i)‖ = ‖w i‖ := by
      simp [CoordLine.lineCLM]
    have hRew : 1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖
              = 1 + ‖z‖ + ‖w i‖ := by simp
    have hv' := hv.trans (by
      have hC : hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m
                ≤ hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m := by
        simp
      have hx : 0 ≤ (1 + |x|) ^ hF_growth.m := by
        exact pow_nonneg (by linarith [abs_nonneg x]) _
      exact mul_le_mul_of_nonneg_right hC hx)
    have hv'' :
        |x * F (z + x • w i)|
          ≤ |x| * (hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m) * (1 + |x|) ^ hF_growth.m := by
      have := mul_le_mul_of_nonneg_left hv' (by exact abs_nonneg x)
      simpa [mul_comm, mul_left_comm, mul_assoc, abs_mul] using this
    have hnormwi : ‖w i‖ = (1 : ℝ) := by simp
    have hConstRew :
        |x| * (hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m)
              * (1 + |x|) ^ hF_growth.m
          = (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m) := by
      have hstep :
          hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m
            = hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m := by
        simp [hnormwi]
      simp [mul_comm, mul_left_comm, mul_assoc]
    have hv''' :
        |x * F (z + x • w i)|
          ≤ (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m) := by
      aesop
    aesop
  have h_int_mplus1 :
      Integrable (fun x : ℝ => (1 + |x|) ^ (hF_growth.m + 1))
        (ProbabilityTheory.gaussianReal 0 v) :=
    (ProbabilityTheory.integrable_one_add_abs_pow_nat_gaussian (v := v) (n := hF_growth.m + 1))
  have h_meas_rhs :
      AEStronglyMeasurable (fun x : ℝ => |x| * (1 + |x|) ^ hF_growth.m)
        (ProbabilityTheory.gaussianReal 0 v) := by
    have hcont : Continuous (fun x : ℝ => |x| * (1 + |x|) ^ hF_growth.m) :=
      continuous_abs.mul ((continuous_const.add continuous_abs).pow _)
    simpa using hcont.measurable.aestronglyMeasurable
  have h_base_int :
      Integrable (fun x : ℝ => |x| * (1 + |x|) ^ hF_growth.m)
        (ProbabilityTheory.gaussianReal 0 v) := by
    refine h_int_mplus1.mono' h_meas_rhs (ae_of_all _ (fun x => ?_))
    have hx_pow_nonneg : 0 ≤ (1 + |x|) ^ hF_growth.m :=
      pow_nonneg (by linarith [abs_nonneg x]) _
    have hnonneg : 0 ≤ |x| * (1 + |x|) ^ hF_growth.m :=
      mul_nonneg (abs_nonneg _) hx_pow_nonneg
    have hx_le : |x| ≤ 1 + |x| := by linarith [abs_nonneg x]
    have hstep :
        |x| * (1 + |x|) ^ hF_growth.m
          ≤ (1 + |x|) * (1 + |x|) ^ hF_growth.m :=
      mul_le_mul_of_nonneg_right hx_le hx_pow_nonneg
    have habs : |(1 + |x|)| = 1 + |x| := by
      have : 0 ≤ 1 + |x| := by linarith [abs_nonneg x]
      simp [abs_of_nonneg this]
    have hx_pow_nonneg' : 0 ≤ |(1 + |x|)| ^ hF_growth.m :=
      pow_nonneg (abs_nonneg (1 + |x|)) _
    have hstep' :
        |x| * |(1 + |x|)| ^ hF_growth.m
          ≤ |(1 + |x|)| ^ (hF_growth.m + 1) := by
      have hx_le' : |x| ≤ |(1 + |x|)| := by simp [habs]
      have := mul_le_mul_of_nonneg_right hx_le' hx_pow_nonneg'
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    have : ‖|x| * (1 + |x|) ^ hF_growth.m‖
            ≤ (1 + |x|) ^ (hF_growth.m + 1) := by
      have hnonneg' : 0 ≤ |x| * |(1 + |x|)| ^ hF_growth.m :=
        mul_nonneg (abs_nonneg _) hx_pow_nonneg'
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg', habs] using hstep'
    exact this
  have h_rhs_int :
      Integrable
        (fun x : ℝ =>
          (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m))
        (ProbabilityTheory.gaussianReal 0 v) :=
    h_base_int.const_mul _
  exact h_rhs_int.mono' h_meas (ae_of_all _ (fun x => by
    have hR : 0 ≤
        (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m) := by
      have hx : 0 ≤ (|x| * (1 + |x|) ^ hF_growth.m) :=
        mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [abs_nonneg x]) _)
      have hK : 0 ≤ (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) :=
        mul_nonneg (le_of_lt hF_growth.Cpos)
          (pow_nonneg (by nlinarith [norm_nonneg z]) _)
      exact mul_nonneg hK hx
    simpa [Real.norm_eq_abs, abs_mul] using h_dom x))

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [DecidableEq ι] in
/-- 1D along-line integrability (derivative). -/
lemma integrable_along_line_deriv_gauss
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (z : H) (v : ℝ≥0) :
    Integrable (fun x : ℝ =>
      deriv (fun t => F (z + t • w i)) x) (ProbabilityTheory.gaussianReal 0 v) := by
  classical
  have hF1D : ContDiff ℝ 1 (fun x : ℝ => F (z + (CoordLine.lineCLM (w := w) (i := i)) x)) :=
    hF_diff.comp (contDiff_const.add (CoordLine.lineCLM (w := w) (i := i)).contDiff)
  have h_meas :
      AEStronglyMeasurable
        (fun x : ℝ => deriv (fun t => F (z + t • w i)) x)
        (ProbabilityTheory.gaussianReal 0 v) := by
    measurability
  have h_dom :
      ∀ x, |deriv (fun t => F (z + t • w i)) x|
        ≤ (hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m
              * (1 + ‖CoordLine.lineCLM (w := w) (i := i)‖))
          * ((1 + |x|) ^ hF_growth.m) := by
    intro x
    have hbound :=
      CoordLine.AffineModerateGrowth.growth_bound_comp_affine_real_deriv
        (hF_diff := hF_diff) (hMG := hF_growth) (z := z) (L := CoordLine.lineCLM (w := w) (i := i)) x
    have hLnorm : ‖CoordLine.lineCLM (w := w) (i := i)‖ = ‖w i‖ := by
      simp [CoordLine.lineCLM]
    have hw1 : ‖w i‖ = (1 : ℝ) := by simp
    simpa [hLnorm, hw1, mul_comm, mul_left_comm, mul_assoc] using hbound
  have h_base : Integrable (fun x : ℝ => (1 + |x|) ^ hF_growth.m)
        (ProbabilityTheory.gaussianReal 0 v) :=
    ProbabilityTheory.integrable_one_add_abs_pow_nat_gaussian (v := v) (n := hF_growth.m)
  have h_rhs_int :
      Integrable
        (fun x : ℝ =>
          (hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m
              * (1 + ‖CoordLine.lineCLM (w := w) (i := i)‖))
            * ((1 + |x|) ^ hF_growth.m))
        (ProbabilityTheory.gaussianReal 0 v) :=
    h_base.const_mul _
  exact h_rhs_int.mono' h_meas (ae_of_all _ (fun x => by
    simpa [Real.norm_eq_abs] using h_dom x))

end AlongLine_integrability

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable {E : Type*} [NormedAddCommGroup E]
variable {μ : Measure α}

/-- If `f =ᵐ[μ] g`, then `Integrable f μ ↔ Integrable g μ`. -/
lemma integrable_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) :
    Integrable f μ ↔ Integrable g μ := by
  classical
  constructor
  · intro hf
    refine ⟨hf.aestronglyMeasurable.congr hfg, ?_⟩
    have hnn : (fun x => (‖g x‖₊ : ℝ≥0∞)) =ᵐ[μ]
                (fun x => (‖f x‖₊ : ℝ≥0∞)) := by
      refine hfg.mono ?_
      intro x hx; simp [hx]
    have hlin : ∫⁻ x, ‖g x‖₊ ∂μ = ∫⁻ x, ‖f x‖₊ ∂μ := by
      simpa using lintegral_congr_ae hnn
    rw [propext (hasFiniteIntegral_congr (id (EventuallyEq.symm hfg)))]
    exact hf.hasFiniteIntegral
  · intro hg
    refine ⟨hg.aestronglyMeasurable.congr hfg.symm, ?_⟩
    have hnn : (fun x => (‖f x‖₊ : ℝ≥0∞)) =ᵐ[μ]
                (fun x => (‖g x‖₊ : ℝ≥0∞)) := by
      refine hfg.mono ?_
      intro x hx; simp [hx]
    have hlin : ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ‖g x‖₊ ∂μ := by
      simpa using lintegral_congr_ae hnn
    rw [propext (hasFiniteIntegral_congr hfg)]
    simpa [hlin] using hg.hasFiniteIntegral

end MeasureTheory

section Pullback_to_Omega

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (w : OrthonormalBasis ι ℝ H) (i : ι)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- If `X` has centered Gaussian law and `Y =ᵐ const y₀`, then
`ω ↦ X ω · F(buildAlong w i (Y ω) (X ω))` is integrable. -/
lemma integrable_coord_mul_F_of_gauss_and_aeConstY
    {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_gauss : Measure.map X μ = ProbabilityTheory.gaussianReal 0 vτ)
    (Y : Ω → (CoordLine.Comp ι i → ℝ)) {y0 : (CoordLine.Comp ι i → ℝ)}
    (hY_ae : Y =ᵐ[μ] fun _ => y0) :
    Integrable (fun ω => X ω * F ( CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω) )) μ := by
  classical
  have hae :
      (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω)))
        =ᵐ[μ]
      (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) y0 (X ω))) := by
    refine hY_ae.mono ?_
    intro ω hω
    simp [hω]
  let z0 : H := ∑ j : CoordLine.Comp ι i, (y0 j) • w j.1
  have hint_gauss :
      Integrable (fun x : ℝ => x * F (z0 + x • w i))
        (ProbabilityTheory.gaussianReal 0 vτ) :=
    integrable_along_line_mul_gauss (w := w) (i := i) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth) (z := z0) (v := vτ)
  have : Integrable
      (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) y0 (X ω))) μ := by
    have hmap_int :
        Integrable (fun x : ℝ => x * F (z0 + x • w i)) (Measure.map X μ) := by
      simpa [hX_gauss] using hint_gauss
    change Integrable
      ((fun x : ℝ => x * F ((∑ j : CoordLine.Comp ι i, y0 j • w j.1) + x • w i)) ∘ X) μ
    exact hmap_int.comp_measurable hX_meas
  exact (integrable_congr_ae hae).2 this

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- If `X` has centered Gaussian law and `Y =ᵐ const y₀`, then
`ω ↦ deriv (t ↦ F(buildAlong w i (Y ω) t)) (X ω)` is integrable. -/
lemma integrable_deriv_F_along_coord_of_gauss_and_aeConstY
    {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_gauss : Measure.map X μ = ProbabilityTheory.gaussianReal 0 vτ)
    (Y : Ω → (CoordLine.Comp ι i → ℝ)) {y0 : (CoordLine.Comp ι i → ℝ)}
    (hY_ae : Y =ᵐ[μ] fun _ => y0) :
    Integrable (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω)) μ := by
  classical
  have hae : (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω))
      =ᵐ[μ]
      (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) y0 t)) (X ω)) := by
    refine hY_ae.mono ?_
    intro ω hω
    simp [hω]
  let z0 : H := ∑ j : CoordLine.Comp ι i, (y0 j) • w j.1
  have hint_gauss :
      Integrable (fun x : ℝ =>
        deriv (fun t => F (z0 + t • w i)) x) (ProbabilityTheory.gaussianReal 0 vτ) :=
    integrable_along_line_deriv_gauss (w := w) (i := i) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth) (z := z0) (v := vτ)
  have : Integrable (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) y0 t)) (X ω)) μ := by
    have hmap_int :
        Integrable (fun x : ℝ =>
          deriv (fun t => F (z0 + t • w i)) x) (Measure.map X μ) := by
      simpa [hX_gauss] using hint_gauss
    change Integrable
      ((fun x : ℝ => deriv
        (fun t => F ((∑ j : CoordLine.Comp ι i, y0 j • w j.1) + t • w i)) x) ∘ X) μ
    exact hmap_int.comp_measurable hX_meas
  exact (integrable_congr_ae hae).2 this

end Pullback_to_Omega

section AEconst_helper

open ProbabilityTheory

/-- If each coordinate of `Y` (to `Comp ι i → ℝ`) has pushforward law `gaussianReal 0 0`
with respect to `μ` (i.e. Dirac at `0`), then `Y =ᵐ[μ] const 0`. -/
lemma ae_const_zero_of_coord_gauss0
    {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (Y : Ω → (CoordLine.Comp ι i → ℝ)) (hY_meas : Measurable Y)
    (hY_gauss0 : ∀ j, Measure.map (fun ω => Y ω j) μ = ProbabilityTheory.gaussianReal 0 0) :
    Y =ᵐ[μ] (fun _ => (fun _ => (0 : ℝ))) := by
  classical
  have hAEcoord : ∀ j, ∀ᵐ ω ∂ μ, Y ω j = 0 := by
    intro j
    have hmap : Measure.map (fun ω => Y ω j) μ
                = ProbabilityTheory.gaussianReal 0 0 := hY_gauss0 j
    have hmeasj : Measurable (fun ω => Y ω j) :=
      (measurable_pi_apply j).comp hY_meas
    have hdirac : ProbabilityTheory.gaussianReal 0 0 = Measure.dirac (0 : ℝ) := by
      simp
    have hcompl0 :
        μ (((fun ω => Y ω j) ⁻¹' {0})ᶜ) = 0 := by
      have hs : MeasurableSet (({0} : Set ℝ)ᶜ) :=
        (measurableSet_singleton (0 : ℝ)).compl
      have hmap_apply :
          (Measure.map (fun ω => Y ω j) μ) (({0} : Set ℝ)ᶜ)
            = μ (((fun ω => Y ω j) ⁻¹' (({0} : Set ℝ)ᶜ))) := by
        simpa using
          (Measure.map_apply (μ := μ) (f := fun ω => Y ω j) (s := (({0} : Set ℝ)ᶜ))
            hmeasj hs)
      have hpush0 :
          (Measure.map (fun ω => Y ω j) μ) (({0} : Set ℝ)ᶜ) = 0 := by
        classical
        simp [hmap, hdirac]
      have : μ (((fun ω => Y ω j) ⁻¹' (({0} : Set ℝ)ᶜ))) = 0 := by
        simpa [hmap_apply] using hpush0
      simpa using this
    exact (ae_iff.mpr hcompl0).mono (by intro ω hω; simpa using hω)
  have : ∀ᵐ ω ∂ μ, ∀ j, Y ω j = 0 := by
    refine ae_all_iff.2 (by intro j; exact hAEcoord j)
  exact this.mono (by intro ω hω; funext j; exact hω j)

end AEconst_helper

section Wrappers_old_names

open ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Wrapper (old name): integrability of `X · F(buildAlong (Y,X))` under independence,
using the a.e.-const helper for zero-variance coordinates. -/
lemma integrable_coord_mul_F_of_indep
    (w : OrthonormalBasis ι ℝ H) (i : ι)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (Y : Ω → (CoordLine.Comp ι i → ℝ))
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (_hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    (hX_gauss : ProbabilityTheory.IsCenteredGaussianRV X vτ)
    (hY_gauss0 : ∀ j, ProbabilityTheory.IsCenteredGaussianRV (fun ω => Y ω j) 0) :
    Integrable (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω))) ℙ := by
  classical
  have hYpush :
      ∀ j, Measure.map (fun ω => Y ω j) (ℙ : Measure Ω)
            = ProbabilityTheory.gaussianReal 0 0 := by
    intro j
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hY_gauss0 j
  have hYae : Y =ᵐ[ℙ] fun _ => (fun _ => (0 : ℝ)) :=
    ae_const_zero_of_coord_gauss0 (μ := (ℙ : Measure Ω))
      (i := i) (Y := Y) (hY_meas := hY_meas) (hY_gauss0 := hYpush)
  have hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 vτ := by
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hX_gauss
  simpa using
    integrable_coord_mul_F_of_gauss_and_aeConstY
      (w := w) (i := i) (μ := (ℙ : Measure Ω))
      (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
      (vτ := vτ) (X := X) (hX_meas := hX_meas) (hX_gauss := hXlaw)
      (Y := Y) (y0 := fun _ => 0) (hY_ae := hYae)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Wrapper (old name): integrability of the derivative along the coordinate line under independence. -/
lemma integrable_deriv_F_along_coord_of_indep
    (w : OrthonormalBasis ι ℝ H) (i : ι)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (Y : Ω → (CoordLine.Comp ι i → ℝ))
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (_hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    (hX_gauss : ProbabilityTheory.IsCenteredGaussianRV X vτ)
    (hY_gauss0 : ∀ j, ProbabilityTheory.IsCenteredGaussianRV (fun ω => Y ω j) 0) :
    Integrable (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω)) ℙ := by
  classical
  -- Y is a.e. zero
  have hYpush :
      ∀ j, Measure.map (fun ω => Y ω j) (ℙ : Measure Ω)
            = ProbabilityTheory.gaussianReal 0 0 := by
    intro j
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hY_gauss0 j
  have hYae : Y =ᵐ[ℙ] fun _ => (fun _ => (0 : ℝ)) :=
    ae_const_zero_of_coord_gauss0 (μ := (ℙ : Measure Ω))
      (i := i) (Y := Y) (hY_meas := hY_meas) (hY_gauss0 := hYpush)
  have hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 vτ := by
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hX_gauss
  simpa using
    integrable_deriv_F_along_coord_of_gauss_and_aeConstY
      (w := w) (i := i) (μ := (ℙ : Measure Ω))
      (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
      (vτ := vτ) (X := X) (hX_meas := hX_meas) (hX_gauss := hXlaw)
      (Y := Y) (y0 := fun _ => 0) (hY_ae := hYae)

end Wrappers_old_names
open ProbabilityTheory MeasureTheory

/-- If a real-valued map `X` is a.e. equal to the constant `0` under a probability measure `μ`,
then its pushforward law is the Dirac mass at `0`. Requires measurability of `X`. -/
lemma map_eq_dirac_of_ae_eq_const_zero
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    (hConst : X =ᵐ[μ] fun _ => (0 : ℝ)) :
    Measure.map X μ = Measure.dirac (0 : ℝ) := by
  classical
  ext s hs
  have hmapX : (Measure.map X μ) s = μ (X ⁻¹' s) :=
    Measure.map_apply hX_meas hs
  have hmap0 : (Measure.map (fun (_ : Ω) => (0 : ℝ)) μ) s
      = μ ((fun _ => (0 : ℝ)) ⁻¹' s) :=
    Measure.map_apply (measurable_const : Measurable fun (_ : Ω) => (0 : ℝ)) hs
  have hpreimage_ae :
      (X ⁻¹' s) =ᵐ[μ] ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) := by
    refine hConst.mono ?_
    intro ω hω
    have hiff : (ω ∈ X ⁻¹' s) ↔ (ω ∈ ((fun _ : Ω => (0 : ℝ)) ⁻¹' s)) := by
      simp [Set.mem_preimage, hω]
    exact propext hiff
  have hEq : μ (X ⁻¹' s) = μ ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) :=
    measure_congr hpreimage_ae
  have hEq : μ (X ⁻¹' s) = μ ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) :=
    measure_congr hpreimage_ae
  have hConstPush :
      (Measure.map (fun _ : Ω => (0 : ℝ)) μ) s = (Measure.dirac (0 : ℝ)) s := by
    by_cases h0 : (0 : ℝ) ∈ s
    · have : ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) = Set.univ := by
        ext ω; simp [h0]
      simp [h0]
    · have : ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) = (∅ : Set Ω) := by
        ext ω; simp [h0]
      simp [h0]
  have hChain : μ (X ⁻¹' s) = (Measure.dirac (0 : ℝ)) s :=
    (hEq.trans hmap0.symm).trans hConstPush
  simpa [hmapX] using hChain

/-- If a real-valued map `X` is a.e. equal to the constant `0` under a probability measure `μ`,
then its pushforward law is the centered degenerate Gaussian `gaussianReal 0 0`. -/
lemma map_eq_gaussianReal0_of_ae_eq_const_zero
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    (hConst : X =ᵐ[μ] fun _ => (0 : ℝ)) :
    Measure.map X μ = ProbabilityTheory.gaussianReal 0 0 := by
  classical
  simpa [ProbabilityTheory.gaussianReal_dirac] using
    map_eq_dirac_of_ae_eq_const_zero (μ := μ) (hX_meas := hX_meas) (hConst := hConst)

namespace ProbabilityTheory

/-- Wrapper with the ambient probability measure `ℙ`:
if `X =ᵐ[ℙ] 0` and `X` is measurable, then `X` is a centered Gaussian with
variance `0`. -/
lemma IsCenteredGaussianRV.of_ae_eq_const
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    (hConst : X =ᵐ[ℙ] fun _ => (0 : ℝ)) :
    ProbabilityTheory.IsCenteredGaussianRV X 0 := by
  classical
  have hmap : Measure.map X (ℙ : Measure Ω) =
      ProbabilityTheory.gaussianReal 0 0 := by
    simpa [ProbabilityTheory.gaussianReal_dirac] using
      map_eq_dirac_of_ae_eq_const_zero (μ := (ℙ : Measure Ω))
        (hX_meas := hX_meas) (hConst := hConst)
  dsimp [ProbabilityTheory.IsCenteredGaussianRV,
         ProbabilityTheory.IsGaussianRV] at *
  exact hmap

/-- If a family `f` is mutually independent, then the tuple on the complement
of `i` is independent from the coordinate `i` itself. -/
lemma iIndepFun.indepFun_subtype_prod_singleton
  {Ω ι : Type*} {β : ι → Type*}
  [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype ι] [DecidableEq ι]
  [∀ i, MeasurableSpace (β i)]
  {f : ∀ i, Ω → β i}
  (hind : ProbabilityTheory.iIndepFun f μ)
  (hf : ∀ i, Measurable (f i))
  (i : ι) :
  ProbabilityTheory.IndepFun
    (fun ω => fun j : {j // j ≠ i} => f j.1 ω)
    (fun ω => f i ω) μ := by
  classical
  let S : Finset ι := Finset.univ.erase i
  let T : Finset ι := {i}
  have hST : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro x hxS hxT
    exact (Finset.mem_erase.mp hxS).1 (Finset.mem_singleton.mp hxT)
  have h0 :
      ProbabilityTheory.IndepFun
        (fun ω (j : {x // x ∈ S}) => f j.1 ω)
        (fun ω (k : {x // x ∈ T}) => f k.1 ω) μ :=
    (ProbabilityTheory.iIndepFun.indepFun_finset
      (f := f) (μ := μ) (S := S) (T := T) hST hind hf)
  let e : {j // j ≠ i} ≃ {j // j ∈ S} :=
  { toFun := fun j =>
      ⟨j.1, by
        have : j.1 ≠ i ∧ j.1 ∈ Finset.univ := ⟨j.2, by simp⟩
        simpa [S, Finset.mem_erase] using this⟩
    , invFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
    , left_inv := by intro j; rfl
    , right_inv := by intro j; rfl }
  let φ :
      (∀ j : {j // j ∈ S}, β j.1) → (∀ j : {j // j ≠ i}, β j.1) :=
    fun v j => v (e j)
  have hφ_meas : Measurable φ := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    simpa using (measurable_pi_apply (e j))
  let ψ : (∀ _k : {x // x ∈ T}, β _k.1) → β i :=
    fun v => v ⟨i, by simp [T]⟩
  have hψ_meas : Measurable ψ := by measurability
  have h' := (ProbabilityTheory.IndepFun.comp h0 hφ_meas hψ_meas)
  have h_left :
      (φ ∘ fun ω (j : {j // j ∈ S}) => f j.1 ω)
        =
      (fun ω (j : {j // j ≠ i}) => f j.1 ω) := by
    funext ω j; rfl
  have h_right :
      (ψ ∘ fun ω (k : {x // x ∈ T}) => f k.1 ω)
        = (fun ω => f i ω) := by
    funext ω; rfl
  simpa [h_left, h_right] using h'

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Independence of i-th coordinate and complement under the Gaussian model. -/
lemma indep_coord_complement
  {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
  (i : hg.ι) :
  ProbabilityTheory.IndepFun
    (fun ω => fun j : CoordLine.Comp hg.ι i => coord hg.w g j.1 ω)
    (coord hg.w g i) ℙ := by
  classical
  have hind :
      ProbabilityTheory.iIndepFun (coord hg.w g) ℙ :=
    (PhysLean.Probability.GaussianIBP.coord_isGaussian_and_indep (g := g) hg).2
  have hf : ∀ j, Measurable (coord hg.w g j) :=
    PhysLean.Probability.GaussianIBP.coord_measurable (g := g) hg
  change ProbabilityTheory.IndepFun
    (fun (ω : Ω) (j : {j // j ≠ i}) => ⟪g ω, hg.w j.1⟫_ℝ)
    (fun ω : Ω => ⟪g ω, hg.w i⟫_ℝ) ℙ
  exact ProbabilityTheory.iIndepFun.indepFun_subtype_prod_singleton
    (μ := ℙ) (f := coord hg.w g) hind hf i

lemma stein_coord_with_param_of_indep
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (vτ : ℝ≥0)
  (X : Ω → ℝ) (Y : Ω → (CoordLine.Comp ι i → ℝ))
  (hX_meas : Measurable X) (hY_meas : Measurable Y)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  (hX_gauss : ProbabilityTheory.IsCenteredGaussianRV X vτ)
  (hY_gauss0 : ∀ j, ProbabilityTheory.IsCenteredGaussianRV (fun ω => Y ω j) 0) :
  ∫ ω, X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω)) ∂ℙ
    =
  (vτ : ℝ) *
  ∫ ω, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω) ∂ℙ := by
  classical
  set P := (CoordLine.Comp ι i → ℝ) × ℝ
  set φ : P → ℝ :=
    fun p => p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)
  set ψ : P → ℝ :=
    fun p => deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
  have hφ_meas : Measurable φ := by
    have h_eval_sum :
        Continuous (fun y : CoordLine.Comp ι i → ℝ =>
          ∑ j : CoordLine.Comp ι i, (y j) • w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (CoordLine.Comp ι i)))
          (f := fun (j : CoordLine.Comp ι i) (y : CoordLine.Comp ι i → ℝ) => (y j) • w j.1)
          ?_
      intro j _
      change Continuous
        ((fun y : CoordLine.Comp ι i → ℝ => y j) •
          (fun _ : CoordLine.Comp ι i → ℝ => w j.1))
      exact (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P => ∑ j : CoordLine.Comp ι i, (p.1 j) • w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • w i) := continuous_snd.smul continuous_const
    have h_build_cont : Continuous (fun p : P =>
        CoordLine.buildAlong (w := w) (i := i) p.1 p.2) := by
      change Continuous
        ((fun p : P => ∑ j : CoordLine.Comp ι i, p.1 j • w j.1) +
          (fun p : P => p.2 • w i))
      exact h1.add h2
    have hFcont : Continuous (fun p : P =>
        F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) :=
      hF_diff.continuous.comp h_build_cont
    have hSnd : Continuous (fun p : P => p.2) := continuous_snd
    exact (hSnd.measurable.mul hFcont.measurable)
  have hψ_meas : Measurable ψ := by
    have h_eval_sum :
        Continuous (fun y : CoordLine.Comp ι i → ℝ =>
          ∑ j : CoordLine.Comp ι i, (y j) • w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (CoordLine.Comp ι i)))
          (f := fun (j : CoordLine.Comp ι i) (y : CoordLine.Comp ι i → ℝ) => (y j) • w j.1)
          ?_
      intro j _
      change Continuous
        ((fun y : CoordLine.Comp ι i → ℝ => y j) •
          (fun _ : CoordLine.Comp ι i → ℝ => w j.1))
      exact (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P => ∑ j : CoordLine.Comp ι i, (p.1 j) • w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • w i) := continuous_snd.smul continuous_const
    have h_build_meas : Measurable (fun p : P =>
        CoordLine.buildAlong (w := w) (i := i) p.1 p.2) := by
      have h_build_cont : Continuous (fun p : P =>
          CoordLine.buildAlong (w := w) (i := i) p.1 p.2) := by
        change Continuous
          ((fun p : P => ∑ j : CoordLine.Comp ι i, p.1 j • w j.1) +
            (fun p : P => p.2 • w i))
        exact h1.add h2
      exact h_build_cont.measurable
    have hFderiv_meas :
        Measurable (fun p : P =>
          fderiv ℝ F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) :=
      (hF_diff.continuous_fderiv (Ne.symm (zero_ne_one' (WithTop ℕ∞)))).measurable.comp h_build_meas
    have hEval : Measurable (fun L : H →L[ℝ] ℝ => L (w i)) :=
      ContinuousLinearMap.measurable_apply (w i)
    have h_rhs :
        Measurable (fun p : P =>
          (fderiv ℝ F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) (w i)) :=
      hEval.comp hFderiv_meas
    have h_eq :
        (fun p : P =>
          deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2)
        =
        (fun p : P =>
          (fderiv ℝ F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) (w i)) := by
      funext p
      have : ∀ t : ℝ,
          CoordLine.buildAlong (w := w) (i := i) p.1 t
            = (∑ j, (p.1 j) • w j.1) + t • w i := by
        intro t; simp [CoordLine.buildAlong, add_comm]
      simpa [this, CoordLine.line_def] using
        (CoordLine.deriv_F_along (w := w) (i := i) (F := F)
          (hF := hF_diff) (z := ∑ j, (p.1 j) • w j.1) (x := p.2))
    simpa [ψ, h_eq] using h_rhs
  have hmap_pair := map_pair_eq_prod_of_indep Y X hY_meas hX_meas hIndep
  have hchg_pair_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hφ_meas
  have hchg_pair_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hψ_meas
  have hchg_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    rw [hmap_pair] at hchg_pair_φ
    exact hchg_pair_φ
  have hchg_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    rw [hmap_pair] at hchg_pair_ψ
    exact hchg_pair_ψ
  have hX_law : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 vτ := hX_gauss
  have hInt_φΩ :
      Integrable (fun ω =>
        φ (Y ω, X ω)) ℙ := by
    simpa [φ] using
      (integrable_coord_mul_F_of_indep (w := w) (i := i)
        (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
        (vτ := vτ) (X := X) (Y := Y)
        (hX_meas := hX_meas) (hY_meas := hY_meas)
        (_hIndep := hIndep) (hX_gauss := hX_gauss)
        (hY_gauss0 := hY_gauss0))
  have hInt_ψΩ :
      Integrable (fun ω =>
        ψ (Y ω, X ω)) ℙ := by
    simpa [ψ] using
      (integrable_deriv_F_along_coord_of_indep (w := w) (i := i)
        (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
        (vτ := vτ) (X := X) (Y := Y)
        (hX_meas := hX_meas) (hY_meas := hY_meas)
        (_hIndep := hIndep) (hX_gauss := hX_gauss)
        (hY_gauss0 := hY_gauss0))

  have hprod' :
      ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ))
        =
      (vτ : ℝ) *
      ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    haveI : SFinite (Measure.map Y ℙ) := Measure.instSFiniteMap ℙ Y
    have h :=
      stein_coord_on_product (w := w) (i := i) (F := F)
        (hF_diff := hF_diff) (hF_growth := hF_growth)
        (μY := Measure.map Y ℙ) (vτ := vτ)
        (hμY_sfinite := inferInstance)
        (hInt_left := by
          exact integrable_phi_on_mapY_prod_gauss (Y := Y) (X := X)
            (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
            (v := vτ) (hXlaw := hX_law) (hφ_meas := hφ_meas)
            (hInt := hInt_φΩ))
        (hInt_right₀ := by
          exact integrable_psi_on_mapY_prod_gauss (Y := Y) (X := X)
            (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
            (v := vτ) (hXlaw := hX_law) (hψ_meas := hψ_meas)
            (hInt := hInt_ψΩ))
    simpa [φ, ψ, hX_law] using h
  calc
    ∫ ω, X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω)) ∂ℙ
        = ∫ ω, φ (Y ω, X ω) ∂ℙ := by
          simp [φ]
    _ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hchg_φ
    _ = (vτ : ℝ) * ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hprod'
    _ = (vτ : ℝ) * ∫ ω, ψ (Y ω, X ω) ∂ℙ := by
          have := congrArg (fun z => (vτ : ℝ) * z) (hchg_ψ.symm)
          simpa using this
    _ = (vτ : ℝ) * ∫ ω, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω) ∂ℙ := by
          simp [ψ]

/-- Final split that replaces the old `stein_coord_with_param_split`. -/
lemma stein_coord_with_param'
  {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
  {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (i : hg.ι) :
  ∫ ω, (PhysLean.Probability.GaussianIBP.coord hg.w g i ω) * F (g ω) ∂ℙ
    = (hg.τ i : ℝ) * ∫ ω, (fderiv ℝ F (g ω)) (hg.w i) ∂ℙ := by
  classical
  let X := PhysLean.Probability.GaussianIBP.coord hg.w g i
  let Y := fun ω => fun j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i =>
    PhysLean.Probability.GaussianIBP.coord hg.w g j.1 ω
  have hX_meas : Measurable X :=
    (PhysLean.Probability.GaussianIBP.coord_measurable (g := g) hg) i
  have hY_meas : Measurable Y :=
    measurable_pi_iff.mpr (fun j =>
      (PhysLean.Probability.GaussianIBP.coord_measurable (g := g) hg) j.1)
  have hIndep := ProbabilityTheory.indep_coord_complement (hg := hg) (i := i)
  have hX_gauss := (PhysLean.Probability.GaussianIBP.coord_isGaussian_and_indep (g := g) hg).1 i
  have hcoord_eq_c :
      PhysLean.Probability.GaussianIBP.coord hg.w g = hg.c :=
    PhysLean.Probability.GaussianIBP.coord_eq_c (g := g) hg
  have h_decomp : ∀ ω, g ω =
      PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) (Y ω) (X ω) := by
    intro ω
    have hrepr : g ω = ∑ j : hg.ι, (hg.c j ω) • hg.w j := by
      simpa using congrArg (fun f => f ω) hg.repr
    have hsplit :
        ∑ j : hg.ι, (hg.c j ω) • hg.w j
          =
        (∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
           (hg.c j.1 ω) • hg.w j.1) + (hg.c i ω) • hg.w i := by
      simpa using
        PhysLean.Probability.GaussianIBP.CoordLine.repr_split_along
          (w := hg.w) (i := i) (c := hg.c) ω
    have hY' : (fun j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i => Y ω j)
                = (fun j => hg.c j.1 ω) := by
      funext j
      simp [Y]; rw [← hcoord_eq_c]; aesop
    have hX' : X ω = hg.c i ω := by
      simp [X, hcoord_eq_c]
    calc
      g ω = ∑ j, (hg.c j ω) • hg.w j := hrepr
      _ = (∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
              (hg.c j.1 ω) • hg.w j.1) + (hg.c i ω) • hg.w i := hsplit
      _ = (∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
              (Y ω j) • hg.w j.1) + (X ω) • hg.w i := by
            simp [hY', hX']
      _ = PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
              (w := hg.w) (i := i) (Y ω) (X ω) := by
            simp [PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
                  add_comm]
  set P := (PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ) × ℝ
  set φ : P → ℝ :=
    fun p => p.2 * F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)
  set ψ : P → ℝ :=
    fun p => deriv (fun t =>
      F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
            (w := hg.w) (i := i) p.1 t)) p.2
  have hφ_meas : Measurable φ := by
    have h_eval_sum :
        Continuous (fun y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ =>
          ∑ j, (y j) • hg.w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)))
          (f := fun (j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)
                       (y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ) =>
                       (y j) • hg.w j.1)
          ?_
      intro j _
      change Continuous
        ((fun y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ => y j) •
          (fun _ : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ => hg.w j.1))
      exact (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P =>
        ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i, (p.1 j) • hg.w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • hg.w i) :=
      continuous_snd.smul continuous_const
    have h_build_cont : Continuous (fun p : P =>
        PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2) := by
      change Continuous
        ((fun p : P => ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
            p.1 j • hg.w j.1) +
          (fun p : P => p.2 • hg.w i))
      exact h1.add h2
    have hFcont : Continuous (fun p : P =>
        F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2)) :=
      hF_diff.continuous.comp h_build_cont
    have hSnd : Continuous (fun p : P => p.2) := continuous_snd
    exact (hSnd.measurable.mul hFcont.measurable)
  have hψ_meas : Measurable ψ := by
    have h_eval_sum :
        Continuous (fun y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ =>
          ∑ j, (y j) • hg.w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)))
          (f := fun (j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)
                       (y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ) =>
                       (y j) • hg.w j.1)
          ?_
      intro j _
      change Continuous
        ((fun y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ => y j) •
          (fun _ : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ => hg.w j.1))
      exact (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P =>
        ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i, (p.1 j) • hg.w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • hg.w i) :=
      continuous_snd.smul continuous_const
    have h_build_meas : Measurable (fun p : P =>
        PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2) := by
      have h_build_cont : Continuous (fun p : P =>
          PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2) := by
        change Continuous
          ((fun p : P => ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
              p.1 j • hg.w j.1) +
            (fun p : P => p.2 • hg.w i))
        exact h1.add h2
      exact h_build_cont.measurable
    have hFderiv_meas :
        Measurable (fun p : P =>
          fderiv ℝ F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)) :=
      (hF_diff.continuous_fderiv (Ne.symm (zero_ne_one' (WithTop ℕ∞)))).measurable.comp h_build_meas
    have hEval : Measurable (fun L : H →L[ℝ] ℝ => L (hg.w i)) :=
      ContinuousLinearMap.measurable_apply (hg.w i)
    have h_rhs :
        Measurable (fun p : P =>
          (fderiv ℝ F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)) (hg.w i)) :=
      hEval.comp hFderiv_meas
    have h_eq :
        (fun p : P =>
          deriv (fun t =>
            F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                  (w := hg.w) (i := i) p.1 t)) p.2)
        =
        (fun p : P =>
          (fderiv ℝ F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)) (hg.w i)) := by
      funext p
      have : ∀ t : ℝ,
          PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 t
            = (∑ j, (p.1 j) • hg.w j.1) + t • hg.w i := by
        intro t; simp [PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
                       add_comm]
      simpa [this, PhysLean.Probability.GaussianIBP.CoordLine.line_def] using
        (PhysLean.Probability.GaussianIBP.CoordLine.deriv_F_along
          (w := hg.w) (i := i) (F := F)
          (hF := hF_diff)
          (z := ∑ j, (p.1 j) • hg.w j.1) (x := p.2))
    simpa [ψ, h_eq] using h_rhs
  have hmap_pair := map_pair_eq_prod_of_indep Y X hY_meas hX_meas hIndep
  have hchg_pair_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hφ_meas
  have hchg_pair_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hψ_meas
  have hchg_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    rw [hmap_pair] at hchg_pair_φ
    exact hchg_pair_φ
  have hchg_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    rw [hmap_pair] at hchg_pair_ψ
    exact hchg_pair_ψ
  have hInt_φΩ :
      Integrable (fun ω =>
        φ (Y ω, X ω)) ℙ := by
    have : Integrable (fun ω => X ω * F (g ω)) ℙ :=
      integrable_coord_mul_F hg hF_diff hF_growth i
    simpa [φ, h_decomp] using this
  have hInt_ψΩ :
      Integrable (fun ω =>
        ψ (Y ω, X ω)) ℙ := by
    have h_deriv_pointwise : ∀ ω,
        deriv (fun t =>
          F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                (w := hg.w) (i := i) (Y ω) t)) (X ω)
          = (fderiv ℝ F (g ω)) (hg.w i) := by
      intro ω
      have := PhysLean.Probability.GaussianIBP.CoordLine.deriv_F_along
        (w := hg.w) (i := i) (F := F) (hF := hF_diff)
        (z := ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
                  (Y ω j) • hg.w j.1)
        (x := X ω)
      simpa [PhysLean.Probability.GaussianIBP.CoordLine.line_def,
             PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
             h_decomp ω, add_comm, add_left_comm, add_assoc] using this
    have hInt_fderiv :
        Integrable (fun ω => (fderiv ℝ F (g ω)) (hg.w i)) ℙ :=
      integrable_fderiv_apply hg hF_diff hF_growth (hg.w i)
    have h_eq_fun :
        (fun ω => ψ (Y ω, X ω))
          = (fun ω => (fderiv ℝ F (g ω)) (hg.w i)) := by
      funext ω
      simp [ψ]
      exact h_deriv_pointwise ω
    rw [h_eq_fun]
    exact hInt_fderiv
  have hX_law : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 (hg.τ i) := hX_gauss
  have hprod' :
      ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ))
        =
      (hg.τ i : ℝ) *
      ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    haveI : SFinite (Measure.map Y ℙ) := Measure.instSFiniteMap ℙ Y
    have h :=
      stein_coord_on_product (w := hg.w) (i := i) (F := F)
        (hF_diff := hF_diff) (hF_growth := hF_growth)
        (μY := Measure.map Y ℙ) (vτ := hg.τ i)
        (hμY_sfinite := inferInstance)
        (hInt_left := by
          exact integrable_phi_on_mapY_prod_gauss (Y := Y) (X := X)
            (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
            (v := hg.τ i) (hXlaw := hX_law) (hφ_meas := hφ_meas)
            (hInt := hInt_φΩ))
        (hInt_right₀ := by
          exact integrable_psi_on_mapY_prod_gauss (Y := Y) (X := X)
            (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
            (v := hg.τ i) (hXlaw := hX_law) (hψ_meas := hψ_meas)
            (hInt := hInt_ψΩ))
    simpa [φ, ψ, hX_law] using h
  calc
    ∫ ω, X ω * F (g ω) ∂ℙ
        = ∫ ω, φ (Y ω, X ω) ∂ℙ := by
          simp [φ, h_decomp]
    _ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hchg_φ
    _ = (hg.τ i : ℝ) * ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hprod'
    _ = (hg.τ i : ℝ) * ∫ ω, ψ (Y ω, X ω) ∂ℙ := by
          have := congrArg (fun z => (hg.τ i : ℝ) * z) (hchg_ψ.symm)
          simpa using this
    _ = (hg.τ i : ℝ) * ∫ ω, (fderiv ℝ F (g ω)) (hg.w i) ∂ℙ := by
          have h_deriv_pointwise : ∀ ω,
              deriv (fun t =>
                F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                      (w := hg.w) (i := i) (Y ω) t)) (X ω)
              = (fderiv ℝ F (g ω)) (hg.w i) := by
            intro ω
            have := PhysLean.Probability.GaussianIBP.CoordLine.deriv_F_along
              (w := hg.w) (i := i) (F := F) (hF := hF_diff)
              (z := ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
                        (Y ω j) • hg.w j.1)
              (x := X ω)
            simpa [PhysLean.Probability.GaussianIBP.CoordLine.line_def,
                   PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
                   h_decomp ω, add_comm, add_left_comm, add_assoc] using this
          refine congrArg (fun r => (hg.τ i : ℝ) * r) ?_
          refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
          exact h_deriv_pointwise ω

/-- Wrapper that reuses the split proof. -/
lemma stein_coord_with_param
  {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
  {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
  {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (i : hg.ι) :
  𝔼[(fun ω => (coord hg.w g i ω) * F (g ω))]
    = (hg.τ i : ℝ) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] :=
  stein_coord_with_param' (g := g) hg hF_diff hF_growth i

/-- The key 1D conditional IBP step for a fixed basis direction `w i`.
This is an immediate wrapper around `stein_coord_with_param`. -/
lemma coord_IBP
    {g : Ω → H} (hg : IsGaussianHilbert g)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (i : hg.ι) :
  𝔼[(fun ω => (coord hg.w g i ω) * F (g ω))]
    = (hg.τ i : ℝ) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] := by
  classical
  simpa using
    stein_coord_with_param (g := g) (hg := hg) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth) (i := i)

/-- **Gaussian IBP on a finite-dimensional Hilbert space (covariant form).**
If `g` is a centered Gaussian on `H` modeled by independent coordinates along an
orthonormal basis with variances `τ i`, then for every `h ∈ H` and every `C¹`
 test function `F : H → ℝ` of moderate growth,

```
  E[⟪g, h⟫ F(g)] = E[(fderiv ℝ F (g)) (Σ h)],
  where  Σ h = ∑ i, (τ i : ℝ) * ⟪h, w i⟫ • w i.
```
-/
@[simp]
theorem gaussian_integration_by_parts_hilbert_cov
    {g : Ω → H} (hg : IsGaussianHilbert g)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
      = 𝔼[(fun ω => (fderiv ℝ F (g ω))
          (∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪h, hg.w i⟫_ℝ) • hg.w i))] := by
  classical
  let ι := hg.ι
  let w := hg.w
  have inner_expansion :
      (fun ω => ⟪g ω, h⟫_ℝ)
        = (fun ω => ∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ)) := by
    funext ω; simpa using Aux.inner_decomp (w := w) (x := g ω) (y := h)
  have step1 :
      𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
        = ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))] := by
    classical
    have h_int : ∀ i : ι, Integrable (fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω)) :=
      fun i => integrable_coord_mul_F hg hF_diff hF_growth i
    have distr :
        (fun ω =>
          (∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ)) * F (g ω))
      = (fun ω =>
          ∑ i : ι, (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω))) := by
      funext ω
      simp [mul_comm, mul_left_comm]
      exact Finset.mul_sum Finset.univ (fun i => ⟪h, w i⟫_ℝ * ⟪g ω, w i⟫_ℝ) (F (g ω))
    calc
      𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
          = 𝔼[(fun ω =>
                (∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ)) * F (g ω))] := by
              refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
              have hpt :
                  ⟪g ω, h⟫_ℝ
                    = ∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ) := by
                have := congrArg (fun f : Ω → ℝ => f ω) inner_expansion
                simpa using this
              simpa using congrArg (fun t => t * F (g ω)) hpt
      _ = 𝔼[(fun ω =>
                ∑ i : ι, (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω)))] := by
              simp [distr]
      _ = ∑ i : ι, 𝔼[(fun ω =>
                (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω)))] := by
              simpa using
                expectation_finset_sum
                  (hg := hg)
                  (f := fun i ω => (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω)))
                  (hint := fun i => (h_int i).const_mul (⟪h, w i⟫_ℝ))
      _ = ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))] := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simpa [mul_comm, mul_left_comm, mul_assoc]
                using expectation_const_mul
                  (c := (⟪h, w i⟫_ℝ))
                  (f := fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))
                  ((h_int i))
  have step2 :
      ∀ i : ι,
        𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))]
          = (hg.τ i : ℝ) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))] := by
    intro i
    simpa [coord] using
      coord_IBP (g := g) (hg := hg) (F := F)
        (hF_diff := hF_diff) (hF_growth := hF_growth) (i := i)
  have step3 :
      ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))]
        = ∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)
            * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))] := by
    classical
    refine Finset.sum_congr rfl ?_
    intro i _
    have h_comm :
        𝔼[(fun ω => F (g ω) * ⟪g ω, w i⟫_ℝ)]
          = 𝔼[(fun ω => ⟪g ω, w i⟫_ℝ * F (g ω))] := by
      change ∫ ω, F (g ω) * ⟪g ω, w i⟫_ℝ ∂ℙ
          = ∫ ω, ⟪g ω, w i⟫_ℝ * F (g ω) ∂ℙ
      refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
      simp [mul_comm]
    calc
      (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))]
          = (⟪h, w i⟫_ℝ) * ((hg.τ i : ℝ) * 𝔼[(fun ω =>
                (fderiv ℝ F (g ω)) (w i))]) := by
                simp [step2 i]
      _ = ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ) * 𝔼[(fun ω =>
                (fderiv ℝ F (g ω)) (w i))] := by
                simp [mul_left_comm, mul_assoc]
  have step4 :
      (∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)
            * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))])
        = 𝔼[(fun ω => (fderiv ℝ F (g ω))
              (∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ) • w i))] := by
    classical
    simpa using
      (fderiv_expectation_weighted_sum
        (hg := hg) (hF_diff := hF_diff) (hF_growth := hF_growth)
        (a := fun i : ι => (hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)).symm
  calc
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
        = ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))] := step1
    _ = ∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)
            * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))] := step3
    _ = 𝔼[(fun ω => (fderiv ℝ F (g ω))
              (∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ) • w i))] := step4

/-- **Operator form (coordinate‑free).** Using the covariance operator `Σ`,
the covariant IBP reads

```
  𝔼[⟪g, h⟫ F(g)] = 𝔼[(fderiv ℝ F (g)) (Σ h)].
```
-/
@[simp]
 theorem gaussian_integration_by_parts_hilbert_cov_op
    {g : Ω → H} (hg : IsGaussianHilbert g)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
      = 𝔼[(fun ω => (fderiv ℝ F (g ω)) ((covOp (g := g) hg) h))] := by
  classical
  simpa [covOp_apply (g := g) (hg := hg) h]
    using gaussian_integration_by_parts_hilbert_cov
      (g := g) (hg := hg) (h := h) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth)

section LinearTestFunctions

/-- Zero mean of Gaussian inner coordinates (take `F ≡ 1`). -/
@[simp]
lemma gaussian_zero_mean_inner
    {g : Ω → H} (hg : IsGaussianHilbert g) (h : H) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ)] = 0 := by
  classical
  have hMG : HasModerateGrowth (fun _ : H => (1 : ℝ)) :=
    hasModerateGrowth_const (H := H) (c := (1 : ℝ))
  have hDiff : ContDiff ℝ 1 (fun _ : H => (1 : ℝ)) := by
    simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : H => (1 : ℝ)))
  simpa using
    (gaussian_integration_by_parts_hilbert_cov_op (g := g) (hg := hg) (h := h)
      (F := fun _ : H => (1 : ℝ)) (hF_diff := hDiff) (hF_growth := hMG))

/-- Covariance identity: `E[⟪g,h⟫ ⟪g,u⟫] = ⟪(Σ h), u⟫`. -/
@[simp]
lemma gaussian_covariance_pairing
    {g : Ω → H} (hg : IsGaussianHilbert g) (h u : H) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * ⟪g ω, u⟫_ℝ)]
      = ⟪(covOp (g := g) hg) h, u⟫_ℝ := by
  classical
  let L : H →L[ℝ] ℝ := ContinuousLinearMap.innerSL ℝ u
  have hDiff : ContDiff ℝ 1 (fun z : H => L z) := L.contDiff
  have hMG : HasModerateGrowth (fun z : H => L z) := hasModerateGrowth_of_clm (L := L)
  have hIBP :=
    gaussian_integration_by_parts_hilbert_cov_op (g := g) (hg := hg) (h := h)
      (F := fun z : H => L z) (hF_diff := hDiff) (hF_growth := hMG)
  have hderiv : ∀ z, fderiv ℝ (fun x : H => L x) z = L := by
    intro z
    exact ContinuousLinearMap.fderiv L
  have hR :
      𝔼[(fun ω : Ω =>
        (fderiv ℝ (fun z : H => L z) (g ω)) ((covOp (g := g) hg) h))]
      =
      𝔼[(fun _ω : Ω => L ((covOp (g := g) hg) h))] := by
    simp [hderiv]
  have hExpConst :
      𝔼[(fun _ω : Ω => L ((covOp (g := g) hg) h))] = L ((covOp (g := g) hg) h) := by
    simp
  have hMain :
      𝔼[(fun ω : Ω => ⟪g ω, h⟫_ℝ * L (g ω))]
        = L ((covOp (g := g) hg) h) := by
    have h' :
        𝔼[(fun ω : Ω => ⟪g ω, h⟫_ℝ * L (g ω))]
          = 𝔼[(fun _ω : Ω => L ((covOp (g := g) hg) h))] := by
      simpa [hR] using hIBP
    simpa [hExpConst] using h'
  have hRhs :
      𝔼[(fun ω : Ω => ⟪g ω, h⟫_ℝ * ⟪u, g ω⟫_ℝ)]
        = ⟪u, (covOp (g := g) hg) h⟫_ℝ := by
    simpa only [L, ContinuousLinearMap.innerSL_apply] using hMain
  simpa [real_inner_comm] using hRhs


end LinearTestFunctions

/-- **Standard-covariance corollary.** If all coordinate variances are `1`, the
covariant formula reduces to the usual identity with `h` on the RHS. -/
@[simp]
 theorem gaussian_integration_by_parts_hilbert_std
    {g : Ω → H} (hg : IsGaussianHilbert g)
    (hτ : ∀ i : hg.ι, hg.τ i = 1)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
      = 𝔼[(fun ω => (fderiv ℝ F (g ω)) h)] := by
  classical
  have := gaussian_integration_by_parts_hilbert_cov
    (g := g) (hg := hg) (h := h) (F := F)
    (hF_diff := hF_diff) (hF_growth := hF_growth)
  have h_as_sum :
      (∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪h, hg.w i⟫_ℝ) • hg.w i) = h := by
    classical
    have : (∑ i : hg.ι, (⟪h, hg.w i⟫_ℝ) • hg.w i) = h := by
      simpa [hg.w.repr_apply_apply, real_inner_comm] using (hg.w.sum_repr h)
    simpa [hτ, mul_one] using this
  simpa [h_as_sum] using this

/-! ### Roadmap for subsequent iterations
* Prove the integrability lemmas using Gaussian moment finiteness results in mathlib.
* Prove `stein_coord_with_param` by unfolding the conditional expectation step
  and invoking the parameterized 1D Stein identity from the imported file.
* Remove the finite-dimensional index restriction by replacing finite sums with
  `∑'` and applying dominated convergence; the present structure already points
  to the covariance operator `Σ` built from the spectral data `(w, τ)`.
-/


/-! ## Further corollaries and operator‑centric consequences
These statements are immediate algebraic fallouts of the operator‑form IBP
and require no extra analysis beyond what is already used above.
-/
section MoreCorollaries

variable {g : Ω → H}

/-- **CLM test functions.** A clean operator‑form covariance identity for any
continuous linear functional `L : H →L[ℝ] ℝ`.

This is just `gaussian_integration_by_parts_hilbert_cov_op` with `F = L`, whose
Fréchet derivative is constantly `L`. -/
@[simp]
lemma gaussian_covariance_clm
    (hg : IsGaussianHilbert (Ω := Ω) (H := H) g)
    (L : H →L[ℝ] ℝ) (h : H) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * L (g ω))]
      = L ((covOp (g := g) hg) h) := by
  classical
  have hDiff : ContDiff ℝ 1 (fun z : H => L z) := L.contDiff
  have hMG   : HasModerateGrowth (fun z : H => L z) :=
    hasModerateGrowth_of_clm (L := L)
  simpa using
    (gaussian_integration_by_parts_hilbert_cov_op (g := g) (hg := hg)
      (h := h) (F := fun z : H => L z) (hF_diff := hDiff) (hF_growth := hMG))

/-- **Quadratic moment along a direction.** Specializing the covariance pairing
with `u = h` gives the second moment of the scalar coordinate. -/
@[simp]
lemma gaussian_quadratic_moment
    (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (h : H) :
    𝔼[(fun ω => (⟪g ω, h⟫_ℝ)^2)]
      = ⟪(covOp (g := g) hg) h, h⟫_ℝ := by
  classical
  simpa [pow_two] using
    (gaussian_covariance_pairing (g := g) (hg := hg) (h := h) (u := h))

lemma gaussian_second_moment
    (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) :
    𝔼[(fun ω => ‖g ω‖^2)] = ∑ i : hg.ι, (hg.τ i : ℝ) := by
  classical
  have h_decomp :
      (fun ω => ‖g ω‖^2) = (fun ω => ∑ i : hg.ι, (⟪g ω, hg.w i⟫_ℝ)^2) := by
    funext ω
    simpa [real_inner_self_eq_norm_sq, pow_two] using
      (Aux.inner_decomp (w := hg.w) (x := g ω) (y := g ω))
  have h_each : ∀ i : hg.ι,
      𝔼[(fun ω => (⟪g ω, hg.w i⟫_ℝ)^2)] = (hg.τ i : ℝ) := by
    intro i
    simpa [pow_two,
           covOp_apply (g := g) (hg := hg),
           OrthonormalBasis.inner_eq_ite,
           inner_smul_left] using
      (gaussian_quadratic_moment (g := g) (hg := hg) (h := hg.w i))
  have h_int : ∀ i : hg.ι, Integrable (fun ω => (⟪g ω, hg.w i⟫_ℝ)^2) := by
    intro i
    have hX_gauss :
        ProbabilityTheory.IsCenteredGaussianRV (coord hg.w g i) (hg.τ i) :=
      (coord_isGaussian_and_indep (g := g) hg).1 i
    have hX_meas : Measurable (coord hg.w g i) :=
      (coord_measurable (g := g) hg) i
    simpa [coord, pow_two] using
      (ProbabilityTheory.IsCenteredGaussianRV.integrable_sq
        (Ω := Ω) (X := coord hg.w g i) (v := hg.τ i) hX_gauss hX_meas)
  calc
    𝔼[(fun ω => ‖g ω‖^2)]
        = 𝔼[(fun ω => ∑ i : hg.ι, (⟪g ω, hg.w i⟫_ℝ)^2)] := by
            simp [h_decomp]
    _ = ∑ i : hg.ι, 𝔼[(fun ω => (⟪g ω, hg.w i⟫_ℝ)^2)] := by
            simpa using
              expectation_finset_sum (g := g) (hg := hg)
                (f := fun i ω => (⟪g ω, hg.w i⟫_ℝ)^2) (hint := h_int)
    _ = ∑ i : hg.ι, (hg.τ i : ℝ) := by
            simp [h_each]

end MoreCorollaries
end ProbabilityTheory
end SteinAlongOneCoordinate
end GaussianIBP
end Probability
end PhysLean

/-!
# Iterated Gaussian integration by parts

The theorem `hermiteMulti_ibp_of_expGrowth` proves the general identity in
`lem:Gaussian-Hermite-IBP` of `CLT/refs/sections/gaussian-chaos.tex`, with
exactly its `C^{|α|}` regularity and exponential Euclidean-growth assumptions
for the partial derivatives `η ≤ α`. The creation-operator polynomials agree
with the product of probabilists' Hermite polynomials. Derivative order
independence, the intermediate product bounds, and integrability are proved
here; `ExpIBPChain` is only an internal sufficient condition for iteration.
The lemma's application to `Z_N` awaits the separate F04 derivative estimates.
-/

open MeasureTheory
open ProbabilityTheory
open scoped Topology

namespace SYK.CLT.GaussianIBP

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

/-- The first-order instance with the same positive constant in front of and
inside the exponential, exactly as in the manuscript's growth condition. -/
theorem coord_stein_of_manuscript_growth
    (h : (ι → ℝ) → ℝ) (i : ι) (hh : ContDiff ℝ 1 h)
    (C : ℝ) (hC : 0 < C)
    (hhb : ∀ g, |h g| ≤
      C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (hdb : ∀ g, |coordDeriv i h g| ≤
      C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, g i * h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, coordDeriv i h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
  coord_stein_of_euclidean_expGrowth h i hh C C hC.le hC.le hhb hdb

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

omit [Fintype ι] in
/-- The creation operator agrees with the probabilists' Hermite recurrence
on functions of one coordinate. -/
theorem creation_hermite (i : ι) (n : ℕ) (g : ι → ℝ) :
    creation i (fun h => Polynomial.aeval (h i) (Polynomial.hermite n)) g =
      Polynomial.aeval (g i) (Polynomial.hermite (n + 1)) := by
  rw [creation, coordDeriv_aeval, Polynomial.hermite_succ]
  simp [Polynomial.aeval_X]

omit [Fintype ι] in
/-- A block of repeated creation operators is the one-variable Hermite polynomial. -/
theorem hermiteList_replicate (i : ι) (n : ℕ) (g : ι → ℝ) :
    hermiteList (List.replicate n i) g =
      Polynomial.aeval (g i) (Polynomial.hermite n) := by
  induction n generalizing g with
  | zero => simp [hermiteList]
  | succ n ih =>
      change creation i (hermiteList (List.replicate n i)) g = _
      have hfun : hermiteList (List.replicate n i) =
          fun h => Polynomial.aeval (h i) (Polynomial.hermite n) := by
        funext h
        exact ih h
      rw [hfun, creation_hermite]

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

/-- Analytic input for iterating one-coordinate integration by parts.
The `Good` predicate must be established for the intended function class and
measure before the resulting identity can be applied. -/
structure IBPFamily (γ : Measure (ι → ℝ)) where
  Good : ((ι → ℝ) → ℝ) → Prop
  one_good : Good (fun _ => 1)
  coordDeriv_good : ∀ {f}, Good f → ∀ i, Good (coordDeriv i f)
  creation_good : ∀ {f}, Good f → ∀ i, Good (creation i f)
  ibp : ∀ {φ ψ}, Good φ → Good ψ → ∀ i,
    (∫ g, creation i φ g * ψ g ∂γ) =
      ∫ g, φ g * coordDeriv i ψ g ∂γ

omit [Fintype ι] in
private theorem hermiteList_good {γ : Measure (ι → ℝ)}
    (A : IBPFamily γ) (l : List ι) : A.Good (hermiteList l) := by
  induction l with
  | nil => exact A.one_good
  | cons i l ih => exact A.creation_good ih i

omit [Fintype ι] in
/-- Repeated coordinate integration by parts for a list of coordinates. -/
theorem hermiteList_ibp {γ : Measure (ι → ℝ)}
    (A : IBPFamily γ) (l : List ι)
    {f : (ι → ℝ) → ℝ} (hf : A.Good f) :
    (∫ g, hermiteList l g * f g ∂γ) =
      ∫ g, partialList l f g ∂γ := by
  induction l generalizing f with
  | nil =>
      simp [hermiteList, partialList]
  | cons i l ih =>
      calc
        (∫ g, hermiteList (i :: l) g * f g ∂γ) =
            ∫ g, hermiteList l g * coordDeriv i f g ∂γ := by
              simpa [hermiteList] using
                A.ibp (hermiteList_good A l) hf i
        _ = ∫ g, partialList l (coordDeriv i f) g ∂γ :=
          ih (A.coordDeriv_good hf i)
        _ = ∫ g, partialList (i :: l) f g ∂γ := by
          rfl

/-- Multi-index form of the abstract iterated integration by parts identity. -/
theorem hermiteMulti_ibp {γ : Measure (ι → ℝ)}
    (A : IBPFamily γ) (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ} (hf : A.Good f) :
    (∫ g, hermiteMulti α g * f g ∂γ) =
      ∫ g, partialMulti α f g ∂γ := by
  simpa [hermiteMulti, partialMulti] using
    hermiteList_ibp A (multiIndexList α) hf

/-- The abstract identity with the standard product normalization of Hermite
polynomials. Its analytic input is still the explicit `IBPFamily` argument. -/
theorem hermiteMulti_ibp_prod {γ : Measure (ι → ℝ)}
    (A : IBPFamily γ) (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ} (hf : A.Good f) :
    (∫ g, (∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i))) * f g ∂γ) =
      ∫ g, partialMulti α f g ∂γ := by
  simpa only [← hermiteMulti_eq_prod] using hermiteMulti_ibp A α hf

end SYK.CLT.GaussianIBP
