import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

noncomputable section

open MeasureTheory
open scoped ENNReal

/-!
# On the requested "Gaussian Lipschitz concentration" statement

The task was to complete a `sorry` in the theorem `gaussianLipschitzConcentration`
below.  Two problems had to be addressed.

1. **The definition did not type-check.**  `LipschitzWith` expects a Lipschitz
   constant in `ℝ≥0` (`NNReal`), but the original code coerced `L.toNNReal` into
   `ℝ≥0∞` (`ENNReal`).  This is fixed below by using `L.toNNReal : ℝ≥0`.

2. **The statement is mathematically false.**  As written, the predicate
   `GaussianLipschitzConcentration` is required to hold for *every* measure `γ`
   on *every* pseudometric space, with **no assumption that `γ` is a Gaussian
   measure**.  The Gaussian concentration inequality is a genuine and deep fact
   *about Gaussian measures*; it fails badly for arbitrary measures.  Hence the
   theorem `gaussianLipschitzConcentration`, which claims the property for an
   arbitrary `γ`, cannot be proved — it is false.

We therefore:
* keep the (type-corrected) definition `GaussianLipschitzConcentration`;
* comment out the original, unprovable theorem;
* prove a concrete counterexample (`not_gaussianLipschitzConcentration`)
  witnessing the falsity;
* document the correct (Gaussian-restricted) statement.
-/

/-- A concentration-type predicate for a measure `γ` on a pseudometric space:
every `L`-Lipschitz function `F` concentrates around its mean with a Gaussian
tail.  (Type-corrected version of the requested definition: the Lipschitz
constant lives in `ℝ≥0`.)

This property is **true for genuine Gaussian measures** but **false for general
measures**; see `not_gaussianLipschitzConcentration` below. -/
def GaussianLipschitzConcentration {E : Type*}
    [MeasurableSpace E] [PseudoMetricSpace E]
    (γ : Measure E) : Prop :=
  ∀ (F : E → ℝ) (L t : ℝ),
    0 < L → 0 < t → LipschitzWith (L.toNNReal) F →
      γ {x | |F x - ∫ y, F y ∂γ| > t} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2)))

/-
-- ORIGINAL REQUESTED THEOREM (commented out: it is FALSE, see below).
-- It asserts the concentration bound for an *arbitrary* measure `γ`, without
-- any Gaussian hypothesis, which is refuted by `not_gaussianLipschitzConcentration`.
theorem gaussianLipschitzConcentration
    {E : Type*}
    [MeasurableSpace E] [PseudoMetricSpace E]
    (γ : Measure E) :
    GaussianLipschitzConcentration γ := by
  intro F L t hL ht hLip
  sorry
-/

/-- A concrete non-Gaussian counterexample measure on `ℝ`: two equal point
masses at `0` and `10`. -/
def cexMeasure : Measure ℝ := Measure.dirac 0 + Measure.dirac 10

/-- **The requested statement is false.**  For the two-point measure
`cexMeasure = δ₀ + δ₁₀`, the `1`-Lipschitz identity function does *not* satisfy
the concentration bound: with `t = 4`, the mean is `10`, the "far from the mean"
set `{x | |x - 10| > 4}` contains the atom `0` and hence has measure `1`, while
the claimed Gaussian bound `2·exp(-8) < 1`.  Thus
`GaussianLipschitzConcentration` fails for a general (non-Gaussian) measure, so
the original theorem (which claimed it for an arbitrary `γ`) cannot hold. -/
theorem not_gaussianLipschitzConcentration :
    ¬ GaussianLipschitzConcentration cexMeasure := by
  intro h
  have hLip : LipschitzWith ((1 : ℝ).toNNReal) (fun x : ℝ => x) := by
    simpa [Real.toNNReal_one] using (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))
  have key := h (fun x => x) 1 4 (by norm_num) (by norm_num) hLip
  have hi0 : Integrable (fun x : ℝ => x) (Measure.dirac 0) := integrable_dirac (by simp)
  have hi10 : Integrable (fun x : ℝ => x) (Measure.dirac 10) := integrable_dirac (by simp)
  have hint : ∫ y, y ∂cexMeasure = 10 := by
    rw [cexMeasure, integral_add_measure hi0 hi10, integral_dirac, integral_dirac]; norm_num
  rw [hint] at key
  have hm : MeasurableSet {x : ℝ | |x - 10| > 4} :=
    measurableSet_lt measurable_const ((measurable_id.sub measurable_const).abs)
  have hset : cexMeasure {x : ℝ | |x - 10| > 4} = 1 := by
    rw [cexMeasure, Measure.add_apply, Measure.dirac_apply' _ hm, Measure.dirac_apply' _ hm]
    have h0 : (0 : ℝ) ∈ {x : ℝ | |x - 10| > 4} := by norm_num
    have h10 : (10 : ℝ) ∉ {x : ℝ | |x - 10| > 4} := by norm_num
    rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h10]; simp
  rw [hset] at key
  have hlt : (2 : ℝ) * Real.exp (-4 ^ 2 / (2 * 1 ^ 2)) < 1 := by
    rw [show (-4 ^ 2 / (2 * 1 ^ 2) : ℝ) = -8 by norm_num, Real.exp_neg,
        show 2 * (Real.exp 8)⁻¹ = 2 / Real.exp 8 from by rw [div_eq_mul_inv],
        div_lt_one (Real.exp_pos 8)]
    nlinarith [Real.add_one_le_exp (8 : ℝ)]
  exact absurd key (not_le.mpr (ENNReal.ofReal_lt_one.mpr hlt))

/-!
## The correct statement

The genuine Gaussian Lipschitz concentration inequality requires `γ` to be a
Gaussian measure.  In Mathlib this hypothesis is available as the class
`ProbabilityTheory.IsGaussian γ`.  A faithful, correct statement would read (for
example, on a finite-dimensional inner-product space `E`):

```
theorem gaussianLipschitzConcentration_correct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (γ : Measure E) [ProbabilityTheory.IsGaussian γ] :
    GaussianLipschitzConcentration γ
```

(possibly with an explicit variance/covariance normalisation).  This is a deep
theorem — equivalent in strength to Gaussian isoperimetry / the Borell–TIS
inequality — and is not currently available in Mathlib.  It is left unstated as
a theorem here (rather than as an unproved `sorry`) so that this file compiles
cleanly; the counterexample above establishes that the *unrestricted* form
originally requested is false.
-/
