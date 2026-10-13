module

public import SYK.CLT.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.Matrix.Normed -- shake: keep (Matrix.Norms.Operator scope)
import SYK.CLT.Limit.EuclideanRelativeCLT
import SYK.CLT.Limit.FiniteVariancePositivity
import SYK.CLT.Limit.StandardizedCLT
import SYK.CLT.Log.Asymptotics

public section

/-!
# Conditional central limit theorem for the SYK model

The finite-model setting and annealed input live in `Basic.lean`. The main
proof combines the exact second chaos, high-temperature higher-chaos bound,
and transfer to the centered logarithm.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
open scoped Matrix.Norms.Operator

namespace SYK.CLT

/-- The partition-function part of `thm:partition-clt` at nonzero inverse temperature.
The joint theorem below additionally supplies the logarithmic CLT. -/
theorem partition_clt {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
        TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1) := by
  obtain ⟨rrel, hrrel, hrel⟩ := S.relativeFluctuation_clt hFE
  obtain ⟨rstd, hrstd, hstd⟩ := S.standardizedFluctuation_clt hFE
  refine ⟨min rrel rstd, lt_min hrrel hrstd, ?_⟩
  intro β hβ hβ0
  have hβrel : |β| < rrel := lt_of_lt_of_le hβ (min_le_left _ _)
  have hβstd : |β| < rstd :=
    lt_of_lt_of_le hβ (min_le_right _ _)
  refine ⟨annealedFreeEnergy_tendsto hFE β, hrel β hβrel hβ0, ?_⟩
  exact ⟨limitVariance_pos_of_ne_zero hFE β hβ0, S.varianceZ_pos_of_ne_zero β hβ0,
    hstd β hβstd hβ0⟩

/-- `thm:partition-clt` and `thm:free-energy-clt` for one matrix Majorana family.

For nonzero inverse temperature the limit is the identity random variable
on `ℝ` with law `gaussianReal 0 (limitVariance q ℓ β)`. Thus the conclusion
expresses weak convergence of probability laws. The limiting function is
the one supplied by the annealed proposition. The limiting and finite-size
variances are positive throughout the stated range.

The assertions of `prop:annealed-free-energy` for `S` are assumed through
`hFE`; the proposition itself and construction of this input are not proved here.
The interaction-order assumptions are supplied only by `S`. -/
theorem partition_and_log_partition_clt {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
        TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1) := by
  obtain ⟨rpart, hrpart, hpart⟩ := partition_clt S hFE
  obtain ⟨rlog, hrlog, hlog⟩ := S.logFluctuation_clt hFE
  refine ⟨min rpart rlog, lt_min hrpart hrlog, ?_⟩
  intro β hβ hβ0
  have hβpart : |β| < rpart := lt_of_lt_of_le hβ (min_le_left _ _)
  have hβlog : |β| < rlog := lt_of_lt_of_le hβ (min_le_right _ _)
  have hp := hpart β hβpart hβ0
  exact ⟨hp.1, hp.2.1, hlog β hβlog hβ0, hp.2.2⟩

end SYK.CLT
