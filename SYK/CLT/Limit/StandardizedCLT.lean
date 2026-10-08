import SYK.CLT.Limit.FiniteVariancePositivity

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

/-!`AnnealedInput` gives the standardized partition-function CLT at nonzero small temperatures. -/

open SYK.Probability

namespace SYK.CLT

local instance (N q : ℕ) : IsProbabilityMeasure (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
  infer_instance

theorem Setting.standardizedFluctuation_eq_multiplier {q : ℕ} (S : Setting q)
    (β : ℝ) (hβ : β ≠ 0) (n : ℕ)
    (g : CouplingSpace (S.N n) q) :
    S.standardizedFluctuation β n g =
      (Real.sqrt (S.fluctuationScale n ^ 2 * S.varianceZ β n /
        S.meanZ β n ^ 2))⁻¹ * S.relativeFluctuation β n g := by
  have hs : 0 < S.fluctuationScale n := by
    have hN : (0 : ℝ) < S.N n := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4)
        (S.q_ge_four.trans (S.q_le_N n))
    unfold Setting.fluctuationScale
    positivity
  have hv : 0 < S.varianceZ β n := S.varianceZ_pos_of_ne_zero β hβ n
  have hm : 0 < S.meanZ β n := (S.partition_moments β n).2.2
  have hsqrt : Real.sqrt (S.fluctuationScale n ^ 2 * S.varianceZ β n /
        S.meanZ β n ^ 2) =
      S.fluctuationScale n * Real.sqrt (S.varianceZ β n) / S.meanZ β n := by
    have harg : S.fluctuationScale n ^ 2 * S.varianceZ β n /
        S.meanZ β n ^ 2 =
        (S.fluctuationScale n * Real.sqrt (S.varianceZ β n) /
          S.meanZ β n) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hv.le]
    rw [harg, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  unfold Setting.standardizedFluctuation Setting.relativeFluctuation Setting.Y
  field_simp [ne_of_gt hs, ne_of_gt hm, ne_of_gt (Real.sqrt_pos.mpr hv)]

theorem gaussian_normalized_limit_law (v : ℝ≥0) (hv : 0 < v) :
    (gaussianReal 0 v).map
      (fun x : ℝ => (Real.sqrt (v : ℝ))⁻¹ * x) = gaussianReal 0 1 := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.coe_injective
    change (Real.sqrt (v : ℝ))⁻¹ ^ 2 * (v : ℝ) = 1
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by exact_mod_cast hv.ne')

theorem Setting.standardizedFluctuation_clt {q : ℕ} (S : Setting q)
    (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq → β ≠ 0 →
      TendstoInDistribution (S.standardizedFluctuation β) atTop
        (fun x : ℝ => x) (fun n => standardGaussianMeasure (S.N n) q)
        (gaussianReal 0 1) := by
  obtain ⟨rrel, hrrel, hrel⟩ := S.relativeFluctuation_clt hFE
  obtain ⟨rvar, hrvar, hvar⟩ := S.scaled_varianceZ_over_mean_sq_tendsto hFE
  obtain ⟨rpos, hrpos, hpos⟩ := exists_small_temperature_variance_pos hFE
  refine ⟨min rrel (min rvar rpos), lt_min hrrel (lt_min hrvar hrpos), ?_⟩
  intro β hβ hβ0
  have hβrel : |β| < rrel := lt_of_lt_of_le hβ (min_le_left _ _)
  have hβvar : |β| < rvar :=
    lt_of_lt_of_le hβ ((min_le_right _ _).trans (min_le_left _ _))
  have hβpos : |β| < rpos :=
    lt_of_lt_of_le hβ ((min_le_right _ _).trans (min_le_right _ _))
  let v := limitVariance q hFE.ℓ β
  have hv : 0 < v := hpos β hβpos hβ0
  let a (n : ℕ) := (Real.sqrt (S.fluctuationScale n ^ 2 *
      S.varianceZ β n / S.meanZ β n ^ 2))⁻¹
  have ha : Tendsto a atTop (𝓝 (Real.sqrt (v : ℝ))⁻¹) :=
    ((hvar β hβvar).sqrt).inv₀
      (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hv)))
  have hm := tendstoInDistribution_mul_coeff
    (fun n => standardGaussianMeasure (S.N n) q)
    (gaussianReal 0 v)
    (S.relativeFluctuation β) (fun x : ℝ => x) (hrel β hβrel hβ0)
    a (Real.sqrt (v : ℝ))⁻¹ ha
  have hLaw (n : ℕ) :
      (standardGaussianMeasure (S.N n) q).map
        (S.standardizedFluctuation β n) =
      (standardGaussianMeasure (S.N n) q).map
        (fun g => a n * S.relativeFluctuation β n g) := by
    congr 1
    funext g
    exact S.standardizedFluctuation_eq_multiplier β hβ0 n g
  refine ⟨?_, by fun_prop, ?_⟩
  · intro n
    have heq : S.standardizedFluctuation β n =
        fun g => a n * S.relativeFluctuation β n g := by
      funext g
      exact S.standardizedFluctuation_eq_multiplier β hβ0 n g
    rw [heq]
    exact aemeasurable_const.mul (S.relativeFluctuation_memLp β n).aestronglyMeasurable.aemeasurable
  · simpa only [hLaw, id_eq, gaussian_normalized_limit_law v hv,
      Measure.map_id'] using hm.tendsto

end SYK.CLT
