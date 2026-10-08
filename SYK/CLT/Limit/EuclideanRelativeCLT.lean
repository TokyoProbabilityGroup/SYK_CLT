import SYK.CLT.Limit.RelativeCLT

/-!
# Relative fluctuation CLT on the model coupling space

The product-Gaussian relative CLT is transported to the manuscript's
Euclidean coupling measure, with the exact limitVariance normalization.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

open SYK.GaussianChaos

namespace SYK.CLT

local instance (N q : ℕ) : IsProbabilityMeasure (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
  infer_instance

local instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (gaussianCouplings ι) := by
  unfold gaussianCouplings
  infer_instance

theorem Setting.relativeFluctuation_memLp {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    MemLp (S.relativeFluctuation β n) 2
      (standardGaussianMeasure (S.N n) q) := by
  unfold Setting.relativeFluctuation
  exact ((S.Y_memLp β n).sub (memLp_const (1 : ℝ))).const_mul _

theorem Setting.relativeFluctuation_law {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    (standardGaussianMeasure (S.N n) q).map (S.relativeFluctuation β n) =
      (gaussianCouplings (InteractionIndex (S.N n) q)).map
        (fun g => S.relativeFluctuation β n (WithLp.toLp 2 g)) := by
  let ι := InteractionIndex (S.N n) q
  have hrel := (S.relativeFluctuation_memLp β n).aestronglyMeasurable.aemeasurable
  change AEMeasurable (S.relativeFluctuation β n)
    ((gaussianCouplings ι).map (MeasurableEquiv.toLp 2 (ι → ℝ))) at hrel
  change ((gaussianCouplings ι).map
    (MeasurableEquiv.toLp 2 (ι → ℝ))).map (S.relativeFluctuation β n) = _
  rw [AEMeasurable.map_map_of_aemeasurable hrel
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable]
  rfl

theorem limitVariance_eq_scaledCoefficient_sq
    (q : ℕ) (ℓ : ℝ → ℝ) (β : ℝ) :
    (limitVariance q ℓ β : ℝ) =
      (β * deriv ℓ β * Real.sqrt ((q.factorial : ℝ) / 2)) ^ 2 := by
  change (q.factorial : ℝ) / 2 * β ^ 2 * (deriv ℓ β) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem gaussian_scaled_limit_law
    (q : ℕ) (ℓ : ℝ → ℝ) (β : ℝ) :
    (gaussianReal 0 1).map
      (fun x : ℝ => (β * deriv ℓ β * Real.sqrt ((q.factorial : ℝ) / 2)) * x) =
      gaussianReal 0 (limitVariance q ℓ β) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.coe_injective
    simp only [mul_one, NNReal.coe_mk]
    exact (limitVariance_eq_scaledCoefficient_sq q ℓ β).symm

theorem Setting.relativeFluctuation_clt {q : ℕ} (S : Setting q)
    (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq → β ≠ 0 →
      TendstoInDistribution (S.relativeFluctuation β) atTop
        (fun x : ℝ => x)
        (fun n => standardGaussianMeasure (S.N n) q)
        (gaussianReal 0 (limitVariance q hFE.ℓ β)) := by
  obtain ⟨βq, hβq, hpi⟩ := S.relativeFluctuation_pi_clt hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ hβ0
  have h := (hpi β hβ hβ0).tendsto
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (S.relativeFluctuation_memLp β n).aestronglyMeasurable.aemeasurable
  · fun_prop
  · have hLaw (n : ℕ) := S.relativeFluctuation_law β n
    have hLim := gaussian_scaled_limit_law q hFE.ℓ β
    simpa only [← hLaw, hLim, Measure.map_id'] using h

end SYK.CLT
