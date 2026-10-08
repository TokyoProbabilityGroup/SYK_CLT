import SYK.Probability.GaussianChaos.Orthogonality
import SYK.Model.GaussianDisorder

/-!
# Finite Gaussian quadratic observables

The centered variance-one square, its first two moments, and the normalized
finite sum with its coupling-space law are independent of asymptotic CLTs.
Entry points: `centeredGaussianSquare`, `centeredGaussianSquare_second_moment`,
`normalizedQuadraticSum_law`. Fourth moments and the CLT are separate consumers.
-/

open MeasureTheory ProbabilityTheory

open SYK.GaussianChaos

namespace SYK.CLT

/-- One centered, variance-one quadratic Gaussian observable. -/
noncomputable def centeredGaussianSquare (x : ℝ) : ℝ :=
  (x ^ 2 - 1) / Real.sqrt 2

/-- Measurability of the centered variance-one Gaussian square. -/
@[fun_prop] theorem centeredGaussianSquare_measurable :
    Measurable centeredGaussianSquare := by
  unfold centeredGaussianSquare
  fun_prop

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

/-- The normalized quadratic fluctuation of the Gaussian interaction coordinates. -/
noncomputable def normalizedQuadraticSum (N q : ℕ) (g : CouplingSpace N q) : ℝ :=
  (Real.sqrt (Fintype.card (InteractionIndex N q) : ℝ))⁻¹ *
    ∑ i : InteractionIndex N q, centeredGaussianSquare (g i)

/-- Measurability of the finite quadratic fluctuation on the coupling space. -/
@[fun_prop] theorem normalizedQuadraticSum_measurable (N q : ℕ) :
    Measurable (normalizedQuadraticSum N q) := by
  unfold normalizedQuadraticSum
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

end SYK.CLT
