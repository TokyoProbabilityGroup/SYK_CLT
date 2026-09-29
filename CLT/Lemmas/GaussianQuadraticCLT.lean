import SYK.CLT.Lemmas.SecondChaosAsymptotic
import Mathlib.Probability.CentralLimitTheorem

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SYK.CLT

/-- One centered, variance-one quadratic Gaussian observable. -/
noncomputable def centeredGaussianSquare (x : ℝ) : ℝ :=
  (x ^ 2 - 1) / Real.sqrt 2

@[fun_prop] private theorem centeredGaussianSquare_measurable :
    Measurable centeredGaussianSquare := by
  unfold centeredGaussianSquare
  fun_prop

private theorem hermite_two_eval (x : ℝ) :
    Polynomial.aeval x (Polynomial.hermite 2) = x ^ 2 - 1 := by
  rw [show 2 = 1 + 1 by decide, Polynomial.hermite_succ, Polynomial.hermite_one]
  simp
  ring

theorem centeredGaussianSquare_mean :
    (∫ x, centeredGaussianSquare x ∂gaussianReal 0 1) = 0 := by
  have h := hermite_pair_integral_real 2 0
  simp only [if_neg (by decide : 2 ≠ 0)] at h
  simp only [Polynomial.hermite_zero, map_one, mul_one,
    hermite_two_eval] at h
  unfold centeredGaussianSquare
  rw [integral_div, h, zero_div]

theorem centeredGaussianSquare_second_moment :
    (∫ x, centeredGaussianSquare x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := hermite_pair_integral_real 2 2
  norm_num at h
  have heq : (fun x : ℝ => centeredGaussianSquare x ^ 2) =
      fun x => ((x ^ 2 - 1) * (x ^ 2 - 1)) / 2 := by
    funext x
    unfold centeredGaussianSquare
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  have h' : (∫ x : ℝ, (x ^ 2 - 1) * (x ^ 2 - 1) ∂gaussianReal 0 1) = 2 := by
    simpa only [pow_two] using h
  rw [heq, integral_div, h']
  norm_num

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

/-- The normalized quadratic fluctuation of the Gaussian interaction coordinates. -/
noncomputable def normalizedQuadraticSum (N q : ℕ) (g : CouplingSpace N q) : ℝ :=
  (Real.sqrt (Fintype.card (InteractionIndex N q) : ℝ))⁻¹ *
    ∑ i : InteractionIndex N q, centeredGaussianSquare (g i)

private theorem normalizedQuadraticSum_measurable (N q : ℕ) :
    Measurable (normalizedQuadraticSum N q) := by
  unfold normalizedQuadraticSum centeredGaussianSquare
  fun_prop

private theorem normalizedQuadraticSum_raw_measurable (N q : ℕ) :
    Measurable (fun g : InteractionIndex N q → ℝ =>
      (Real.sqrt (Fintype.card (InteractionIndex N q) : ℝ))⁻¹ *
        ∑ i : InteractionIndex N q, centeredGaussianSquare (g i)) := by
  unfold centeredGaussianSquare
  fun_prop

theorem normalizedQuadraticSum_law (N q : ℕ) :
    (standardGaussianMeasure N q).map (normalizedQuadraticSum N q) =
    (gaussianCouplings (InteractionIndex N q)).map (fun g =>
      (Real.sqrt (Fintype.card (InteractionIndex N q) : ℝ))⁻¹ *
        ∑ i : InteractionIndex N q, centeredGaussianSquare (g i)) := by
  unfold standardGaussianMeasure GaussianConcentration.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map (normalizedQuadraticSum_measurable N q)
    (WithLp.measurable_toLp 2 (InteractionIndex N q → ℝ))]
  change (gaussianCouplings (InteractionIndex N q)).map
    (normalizedQuadraticSum N q ∘ WithLp.toLp 2) = _
  congr 1

local instance (N q : ℕ) : IsProbabilityMeasure (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
  infer_instance

/-- The quadratic Gaussian sum converges to a standard normal law. -/
theorem Setting.normalizedQuadraticSum_clt {q : ℕ} (S : Setting q) :
    TendstoInDistribution
      (fun n => normalizedQuadraticSum (S.N n) q) atTop (fun x : ℝ => x)
      (fun n => standardGaussianMeasure (S.N n) q) (gaussianReal 0 1) where
  forall_aemeasurable n := (normalizedQuadraticSum_measurable (S.N n) q).aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    have h := S.centeredGaussianSquares_charFun_tendsto t
    simp only [ProbabilityMeasure.coe_mk]
    simp_rw [normalizedQuadraticSum_law]
    simpa using h

end SYK.CLT
