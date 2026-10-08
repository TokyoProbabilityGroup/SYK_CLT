import SYK.CLT.Chaos.SecondChaosAsymptotic
import SYK.CLT.Quadratic.GaussianQuadraticObservable
import Mathlib.Probability.CentralLimitTheorem

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

open SYK.GaussianChaos

namespace SYK.CLT

private theorem charFun_centeredGaussianSquares {ι : Type*} [Fintype ι]
    (t : ℝ) :
    charFun ((gaussianCouplings ι).map (fun g =>
      (Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
        ∑ i : ι, centeredGaussianSquare (g i))) t =
      (charFun ((gaussianReal 0 1).map centeredGaussianSquare)
        ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * t)) ^ Fintype.card ι := by
  let μ : ι → Measure ℝ := fun _ => gaussianReal 0 1
  have hindep : iIndepFun (fun i (g : ι → ℝ) => centeredGaussianSquare (g i))
      (Measure.pi μ) :=
    iIndepFun_pi (fun _ => centeredGaussianSquare_measurable.aemeasurable)
  have hmeas (i : ι) : Measurable (fun g : ι → ℝ => centeredGaussianSquare (g i)) :=
    centeredGaussianSquare_measurable.comp (by fun_prop)
  have hsum : Measurable (fun g : ι → ℝ => ∑ i, centeredGaussianSquare (g i)) :=
    Finset.measurable_fun_sum _ (fun i _ => hmeas i)
  have hchar := hindep.charFun_map_fun_sum_eq_prod (fun i => (hmeas i).aemeasurable)
  change charFun ((Measure.pi μ).map (fun g =>
      (Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
        ∑ i : ι, centeredGaussianSquare (g i))) t = _
  rw [charFun_map_mul_comp, hchar]
  case hf => exact hsum.aemeasurable
  have hmap (i : ι) :
      (Measure.pi μ).map (fun g => centeredGaussianSquare (g i)) =
        (gaussianReal 0 1).map centeredGaussianSquare := by
    change (Measure.pi μ).map (centeredGaussianSquare ∘ fun g => g i) = _
    rw [← Measure.map_map centeredGaussianSquare_measurable (by fun_prop)]
    rw [(measurePreserving_eval μ i).map_eq]
  simp_rw [hmap]
  simp

variable {q : ℕ} (S : Setting q)

/-- The normalized sum of independent Gaussian squares has the standard
Gaussian characteristic-function limit. -/
theorem Setting.centeredGaussianSquares_charFun_tendsto (t : ℝ) :
    Tendsto (fun n => charFun
      ((gaussianCouplings (InteractionIndex (S.N n) q)).map (fun g =>
        (Real.sqrt (Fintype.card (InteractionIndex (S.N n) q) : ℝ))⁻¹ *
          ∑ i : InteractionIndex (S.N n) q, centeredGaussianSquare (g i))) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  have ht := (tendsto_charFun_inv_sqrt_mul_pow
    centeredGaussianSquare_measurable.aemeasurable
    centeredGaussianSquare_mean centeredGaussianSquare_second_moment t).comp
      S.interactionCard_tendsto
  simp_rw [charFun_centeredGaussianSquares]
  simpa [charFun_gaussianReal, Function.comp_def, neg_div] using ht

local instance (N q : ℕ) : IsProbabilityMeasure (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
  infer_instance

/-- The quadratic Gaussian sum converges to a standard normal law. -/
theorem Setting.normalizedQuadraticSum_clt {q : ℕ} (S : Setting q) :
    TendstoInDistribution
      (fun n => normalizedQuadraticSum (S.N n) q) atTop (fun x : ℝ => x)
      (fun n => standardGaussianMeasure (S.N n) q) (gaussianReal 0 1) where
  forall_aemeasurable n := by
    exact (normalizedQuadraticSum_measurable (S.N n) q).aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    have h := S.centeredGaussianSquares_charFun_tendsto t
    simp only [ProbabilityMeasure.coe_mk]
    simp_rw [normalizedQuadraticSum_law]
    simpa using h

end SYK.CLT
