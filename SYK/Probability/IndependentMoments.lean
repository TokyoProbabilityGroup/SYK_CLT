module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

public section

/-!
# Moments of sums of independent centered variables

The second and fourth moment addition formulas apply to independent real random variables
with zero means and finite fourth moments, on an arbitrary probability space.
-/

open MeasureTheory ProbabilityTheory

namespace SYK.Probability

private theorem integrable_pow_le_four {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 4 μ) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun ω => X ω ^ k) μ := by
  have hn := integrable_norm_pow_of_le hX.aestronglyMeasurable hk
    (hX.integrable_norm_pow (by decide : 4 ≠ 0))
  apply hn.mono' (hX.aestronglyMeasurable.pow k)
  filter_upwards [] with ω
  simp only [Pi.pow_apply, norm_pow, le_refl]

/-- The fourth-moment addition formula for independent centered variables. -/
theorem fourth_moment_add_of_indep {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hXY : IndepFun X Y μ)
    (hXmean : (∫ ω, X ω ∂μ) = 0)
    (hYmean : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
      (∫ ω, X ω ^ 4 ∂μ) +
        6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
        (∫ ω, Y ω ^ 4 ∂μ) := by
  have hX1 : Integrable X μ := by
    simpa using integrable_pow_le_four hX 1 (by decide)
  have hX2 := integrable_pow_le_four hX 2 (by decide)
  have hX3 := integrable_pow_le_four hX 3 (by decide)
  have hX4 := integrable_pow_le_four hX 4 (by decide)
  have hY1 : Integrable Y μ := by
    simpa using integrable_pow_le_four hY 1 (by decide)
  have hY2 := integrable_pow_le_four hY 2 (by decide)
  have hY3 := integrable_pow_le_four hY 3 (by decide)
  have hY4 := integrable_pow_le_four hY 4 (by decide)
  have hi31 : IndepFun (fun ω => X ω ^ 3) Y μ := by
    simpa only [Function.comp_def, id_eq] using
      hXY.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 3)) measurable_id
  have hi22 : IndepFun (fun ω => X ω ^ 2) (fun ω => Y ω ^ 2) μ := by
    simpa only [Function.comp_def] using
      hXY.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
        (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  have hi13 : IndepFun X (fun ω => Y ω ^ 3) μ := by
    simpa only [Function.comp_def, id_eq] using
      hXY.comp measurable_id (by fun_prop : Measurable (fun x : ℝ => x ^ 3))
  have h31 : Integrable (fun ω => X ω ^ 3 * Y ω) μ := by
    change Integrable ((fun ω => X ω ^ 3) * Y) μ
    exact hi31.integrable_mul hX3 hY1
  have h22 : Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) μ := by
    change Integrable ((fun ω => X ω ^ 2) * fun ω => Y ω ^ 2) μ
    exact hi22.integrable_mul hX2 hY2
  have h13 : Integrable (fun ω => X ω * Y ω ^ 3) μ := by
    change Integrable (X * fun ω => Y ω ^ 3) μ
    exact hi13.integrable_mul hX1 hY3
  have e31 : (∫ ω, X ω ^ 3 * Y ω ∂μ) = 0 := by
    have h := hi31.integral_mul_eq_mul_integral
      hX3.aestronglyMeasurable hY1.aestronglyMeasurable
    simpa only [Pi.mul_apply, hYmean, mul_zero] using h
  have e22 : (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) =
      (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) := by
    simpa only [Pi.mul_apply] using hi22.integral_mul_eq_mul_integral
      hX2.aestronglyMeasurable hY2.aestronglyMeasurable
  have e13 : (∫ ω, X ω * Y ω ^ 3 ∂μ) = 0 := by
    have h := hi13.integral_mul_eq_mul_integral
      hX1.aestronglyMeasurable hY3.aestronglyMeasurable
    simpa only [Pi.mul_apply, hXmean, zero_mul] using h
  have hB : Integrable (fun ω => 4 * (X ω ^ 3 * Y ω)) μ := h31.const_mul 4
  have hC : Integrable (fun ω => 6 * (X ω ^ 2 * Y ω ^ 2)) μ := h22.const_mul 6
  have hD : Integrable (fun ω => 4 * (X ω * Y ω ^ 3)) μ := h13.const_mul 4
  have hAB := hX4.add hB
  have hABC := hAB.add hC
  have hABCD := hABC.add hD
  have hp (ω : Ω) : (X ω + Y ω) ^ 4 =
      X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
        6 * (X ω ^ 2 * Y ω ^ 2) +
        4 * (X ω * Y ω ^ 3) + Y ω ^ 4 := by ring
  calc
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
        ∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
          6 * (X ω ^ 2 * Y ω ^ 2) +
          4 * (X ω * Y ω ^ 3) + Y ω ^ 4 ∂μ := by
            congr 1
            funext ω
            exact hp ω
    _ = _ := by
      have eABCD :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) +
            4 * (X ω * Y ω ^ 3) + Y ω ^ 4 ∂μ) =
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) +
            4 * (X ω * Y ω ^ 3) ∂μ) +
          (∫ ω, Y ω ^ 4 ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hABCD hY4
      have eABC :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) +
            4 * (X ω * Y ω ^ 3) ∂μ) =
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) ∂μ) +
          (∫ ω, 4 * (X ω * Y ω ^ 3) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hABC hD
      have eAB :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) ∂μ) =
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂μ) +
          (∫ ω, 6 * (X ω ^ 2 * Y ω ^ 2) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hAB hC
      have eA :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂μ) =
          (∫ ω, X ω ^ 4 ∂μ) +
          (∫ ω, 4 * (X ω ^ 3 * Y ω) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hX4 hB
      rw [eABCD, eABC, eAB, eA]
      simp only [integral_const_mul, e31, e22, e13, mul_zero]
      ring

/-- The second moment of a sum of independent centered variables is additive. -/
theorem second_moment_add_of_indep {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hXY : IndepFun X Y μ)
    (hXmean : (∫ ω, X ω ∂μ) = 0)
    (_hYmean : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 2 ∂μ) =
      (∫ ω, X ω ^ 2 ∂μ) + (∫ ω, Y ω ^ 2 ∂μ) := by
  have hX1 : Integrable X μ := by
    simpa using integrable_pow_le_four hX 1 (by decide)
  have hY1 : Integrable Y μ := by
    simpa using integrable_pow_le_four hY 1 (by decide)
  have hX2 := integrable_pow_le_four hX 2 (by decide)
  have hY2 := integrable_pow_le_four hY 2 (by decide)
  have hXYint : Integrable (fun ω => X ω * Y ω) μ := by
    change Integrable (X * Y) μ
    exact hXY.integrable_mul hX1 hY1
  have eXY : (∫ ω, X ω * Y ω ∂μ) = 0 := by
    have h := hXY.integral_mul_eq_mul_integral
      hX1.aestronglyMeasurable hY1.aestronglyMeasurable
    simpa only [Pi.mul_apply, hXmean, zero_mul] using h
  have hp (ω : Ω) : (X ω + Y ω) ^ 2 =
      X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 := by ring
  have hB := hXYint.const_mul 2
  have hAB := hX2.add hB
  calc
    (∫ ω, (X ω + Y ω) ^ 2 ∂μ) =
        ∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 ∂μ := by
          congr 1
          funext ω
          exact hp ω
    _ = _ := by
      have eAB :
          (∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 ∂μ) =
          (∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) ∂μ) +
          (∫ ω, Y ω ^ 2 ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hAB hY2
      have eA :
          (∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) ∂μ) =
          (∫ ω, X ω ^ 2 ∂μ) +
          (∫ ω, 2 * (X ω * Y ω) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hX2 hB
      rw [eAB, eA]
      simp only [integral_const_mul, eXY, mul_zero, add_zero]

end SYK.Probability
