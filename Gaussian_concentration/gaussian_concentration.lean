import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal

def GaussianLipschitzConcentration {E : Type*}
    [MeasurableSpace E] [PseudoMetricSpace E]
    (γ : Measure E) : Prop :=
  ∀ (F : E → ℝ) (L t : ℝ),
    0 < L → 0 < t → LipschitzWith (L.toNNReal : ℝ≥0∞) F →
      γ {x | |F x - ∫ y, F y ∂γ| > t} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2)))

theorem gaussianLipschitzConcentration
    {E : Type*}
    [MeasurableSpace E] [PseudoMetricSpace E]
    (γ : Measure E) :
    GaussianLipschitzConcentration γ := by
  intro F L t hL ht hLip
  sorry
