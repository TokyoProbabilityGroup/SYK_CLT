import SYK.CLT.Basic

/-!
# Positive finite-size disorder variance

At nonzero inverse temperature, a single interaction makes the partition
function strictly larger than its value at zero coupling. Full support of the
Gaussian disorder then rules out zero variance at every finite size.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace SYK.CLT


private instance : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
  (gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure

private instance (N q : ℕ) : Measure.IsOpenPosMeasure
    (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
    GaussianConcentration.standardGaussianMeasureOnEuclidean
  apply (PiLp.continuous_toLp 2 _).isOpenPosMeasure_map
  exact WithLp.toLp_surjective 2

theorem Setting.varianceZ_pos_of_ne_zero {q : ℕ} (S : Setting q)
    (β : ℝ) (hβ : β ≠ 0) (n : ℕ) : 0 < S.varianceZ β n := by
  have hzero : S.Z β n 0 = 1 :=
    realPartitionFunction_zero_coupling (S.params n) (S.majorana n) β
  have hs : Nonempty (InteractionIndex (S.N n) q) := by
    have hcard : 0 < Fintype.card (InteractionIndex (S.N n) q) := by
      simpa [InteractionIndex] using Nat.choose_pos (S.q_le_N n)
    exact Fintype.card_pos_iff.mp hcard
  obtain ⟨s⟩ := hs
  have hsingle : 1 < S.Z β n (WithLp.toLp 2 (Pi.single s (1 : ℝ))) :=
    realPartitionFunction_single_gt_one (S.params n) (S.majorana n) β hβ s
  by_contra hpos
  have hvar : S.varianceZ β n = 0 :=
    le_antisymm (not_lt.mp hpos) (variance_nonneg _ _)
  have hae := ae_eq_integral_of_variance_eq_zero
    (S.partition_moments β n).1 hvar
  have hconst : S.Z β n = fun _ => S.meanZ β n := by
    exact Measure.eq_of_ae_eq (μ := standardGaussianMeasure (S.N n) q) hae
      (realPartitionFunction_continuous (S.params n) (S.majorana n) β)
      continuous_const
  have h0 := congrFun hconst 0
  have h1 := congrFun hconst (WithLp.toLp 2 (Pi.single s (1 : ℝ)))
  rw [hzero] at h0
  rw [h1] at hsingle
  linarith

end SYK.CLT
