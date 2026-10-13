module

public import SYK.Probability.GaussianChaos.HermiteDensity
import SYK.Probability.GaussianConcentration.StandardGaussian
import SYK.Probability.GaussianMomentDetermination

public section

/-!
# Polynomial density for Gaussian `L²`

Polynomial density in finite-product Gaussian `L²` completes the Hermite
density argument of `SYK.Probability.GaussianChaos.HermiteDensity`. Entry points:
`mvPolynomialLp_dense`, `hermiteOrthonormal_dense`,
`hasSum_hermiteCoefficients_unconditional`,
`hasSum_hermiteDegreeProjection_unconditional`.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

open SYK.Probability

namespace SYK.GaussianChaos

/-- The exponential of any continuous linear Gaussian observable belongs to `L²`. -/
theorem gaussianExpDual_memLp_two {ι : Type*} [Fintype ι]
    (L : StrongDual ℝ (ι → ℝ)) (t : ℝ) :
    MemLp (fun g : ι → ℝ => Real.exp (t * L g)) 2 (gaussianCouplings ι) := by
  letI : IsGaussian (gaussianCouplings ι) := by
    change IsGaussian (Measure.pi fun _ : ι => gaussianReal 0 1)
    infer_instance
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have hmap : Integrable (fun x : ℝ => Real.exp ((2 * t) * x))
      ((gaussianCouplings ι).map L) := by
    rw [IsGaussian.map_eq_gaussianReal L]
    exact integrable_exp_mul_gaussianReal (2 * t)
  have h := (integrable_map_measure (by fun_prop) (by fun_prop)).mp hmap
  convert h using 1
  funext g
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The positive part of a Gaussian `L²` class, viewed as a weighted measure. -/
private noncomputable def gaussianPositiveMeasurePi {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι)) : Measure (ι → ℝ) :=
  (gaussianCouplings ι).withDensity fun g => ENNReal.ofReal (f g)

private theorem gaussianPositiveMeasurePi_finite {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι)) :
    IsFiniteMeasure (gaussianPositiveMeasurePi f) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact ((Lp.memLp f).integrable (by norm_num)).2

private theorem gaussianPositiveMeasurePi_integrable_exp_dual {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι))
    (L : StrongDual ℝ (ι → ℝ)) (t : ℝ) :
    Integrable (fun g => Real.exp (t * L g)) (gaussianPositiveMeasurePi f) := by
  have hmeas : AEMeasurable (fun g : ι → ℝ => ENNReal.ofReal (f g))
      (gaussianCouplings ι) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [gaussianPositiveMeasurePi,
    integrable_withDensity_iff_integrable_smul₀' hmeas (by simp)]
  have hpos := ((Lp.memLp f).integrable_mul (gaussianExpDual_memLp_two L t)).pos_part
  convert hpos using 1
  funext g
  rw [smul_eq_mul, ENNReal.toReal_ofReal',
    max_mul_of_nonneg (f g) 0 (le_of_lt (Real.exp_pos _))]
  simp

private theorem integral_gaussianPositiveMeasurePi {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι)) (h : (ι → ℝ) → ℝ) :
    (∫ g, h g ∂gaussianPositiveMeasurePi f) =
      ∫ g, max (f g) 0 * h g ∂gaussianCouplings ι := by
  have hmeas : AEMeasurable (fun g : ι → ℝ => ENNReal.ofReal (f g))
      (gaussianCouplings ι) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [gaussianPositiveMeasurePi,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas (by simp)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal']

private theorem gaussianPositiveMeasurePi_integrable_pow_dual {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι))
    (L : StrongDual ℝ (ι → ℝ)) (n : ℕ) :
    Integrable (fun g => (L g) ^ n) (gaussianPositiveMeasurePi f) := by
  have hset : integrableExpSet L (gaussianPositiveMeasurePi f) = Set.univ := by
    ext t
    simp [integrableExpSet, gaussianPositiveMeasurePi_integrable_exp_dual f L t]
  simpa using (integrable_pow_of_mem_interior_integrableExpSet
    (X := L) (μ := gaussianPositiveMeasurePi f) (by simp [hset]) n)

private theorem gaussianPositivePartPi_mul_pow_integrable {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι))
    (L : StrongDual ℝ (ι → ℝ)) (n : ℕ) :
    Integrable (fun g => max (f g) 0 * (L g) ^ n) (gaussianCouplings ι) := by
  have hmeas : AEMeasurable (fun g : ι → ℝ => ENNReal.ofReal (f g))
      (gaussianCouplings ι) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have h := (integrable_withDensity_iff_integrable_smul₀'
    hmeas (by simp)).mp (gaussianPositiveMeasurePi_integrable_pow_dual f L n)
  simpa only [gaussianPositiveMeasurePi, smul_eq_mul, ENNReal.toReal_ofReal'] using h

private theorem gaussianPositiveMeasurePi_moments_eq_of_orthogonal {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι))
    (L : StrongDual ℝ (ι → ℝ))
    (horth : ∀ n : ℕ, ∫ g, f g * (L g) ^ n ∂gaussianCouplings ι = 0)
    (n : ℕ) :
    (∫ g, (L g) ^ n ∂gaussianPositiveMeasurePi f) =
      ∫ g, (L g) ^ n ∂gaussianPositiveMeasurePi (-f) := by
  rw [integral_gaussianPositiveMeasurePi, integral_gaussianPositiveMeasurePi]
  have hpoint : (fun g : ι → ℝ => max ((-f) g) 0 * (L g) ^ n) =ᵐ[gaussianCouplings ι]
      (fun g => max (-(f g)) 0 * (L g) ^ n) := by
    filter_upwards [Lp.coeFn_neg f] with g hg
    simp only [Pi.neg_apply] at hg
    rw [hg]
  have hneg : (∫ g, max ((-f) g) 0 * (L g) ^ n ∂gaussianCouplings ι) =
      ∫ g, max (-(f g)) 0 * (L g) ^ n ∂gaussianCouplings ι := by
    exact integral_congr_ae hpoint
  rw [hneg]
  have hdecomp : (fun g : ι → ℝ => max (f g) 0 * (L g) ^ n -
      max (-(f g)) 0 * (L g) ^ n) = (fun g => f g * (L g) ^ n) := by
    funext g
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  have hnegInt : Integrable (fun g : ι → ℝ => max (-(f g)) 0 * (L g) ^ n)
      (gaussianCouplings ι) :=
    (gaussianPositivePartPi_mul_pow_integrable (-f) L n).congr hpoint
  have h := integral_sub (gaussianPositivePartPi_mul_pow_integrable f L n) hnegInt
  rw [hdecomp, horth n] at h
  linarith

private theorem gaussianPositiveMeasurePi_map_eq_neg_of_orthogonal {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι))
    (L : StrongDual ℝ (ι → ℝ))
    (horth : ∀ n : ℕ, ∫ g, f g * (L g) ^ n ∂gaussianCouplings ι = 0) :
    (gaussianPositiveMeasurePi f).map L = (gaussianPositiveMeasurePi (-f)).map L := by
  letI := gaussianPositiveMeasurePi_finite f
  letI := gaussianPositiveMeasurePi_finite (-f)
  apply measure_eq_of_moments
  · intro t
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact gaussianPositiveMeasurePi_integrable_exp_dual f L t
  · intro t
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact gaussianPositiveMeasurePi_integrable_exp_dual (-f) L t
  · intro n
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
    exact gaussianPositiveMeasurePi_moments_eq_of_orthogonal f L horth n

private theorem gaussianPositiveMeasurePi_eq_neg_of_dual_moments {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι))
    (horth : ∀ (L : StrongDual ℝ (ι → ℝ)) (n : ℕ),
      ∫ g, f g * (L g) ^ n ∂gaussianCouplings ι = 0) :
    gaussianPositiveMeasurePi f = gaussianPositiveMeasurePi (-f) := by
  letI := gaussianPositiveMeasurePi_finite f
  letI := gaussianPositiveMeasurePi_finite (-f)
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  rw [gaussianPositiveMeasurePi_map_eq_neg_of_orthogonal f L (horth L)]

/-- Vanishing moments along every linear observable force a finite product
Gaussian `L²` class to vanish. -/
theorem gaussianLpPi_eq_zero_of_dual_moments_zero {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι))
    (horth : ∀ (L : StrongDual ℝ (ι → ℝ)) (n : ℕ),
      ∫ g, f g * (L g) ^ n ∂gaussianCouplings ι = 0) :
    f = 0 := by
  have hmeasure := gaussianPositiveMeasurePi_eq_neg_of_dual_moments f horth
  have hmeas : AEMeasurable (fun g : ι → ℝ => ENNReal.ofReal (f g))
      (gaussianCouplings ι) := (Lp.memLp f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmeasNeg : AEMeasurable (fun g : ι → ℝ => ENNReal.ofReal ((-f) g))
      (gaussianCouplings ι) := (Lp.memLp (-f)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpos := Measure.rnDeriv_withDensity₀ (gaussianCouplings ι) hmeas
  have hneg := Measure.rnDeriv_withDensity₀ (gaussianCouplings ι) hmeasNeg
  change (gaussianPositiveMeasurePi f).rnDeriv (gaussianCouplings ι) =ᵐ[
    gaussianCouplings ι]
    (fun g => ENNReal.ofReal (f g)) at hpos
  change (gaussianPositiveMeasurePi (-f)).rnDeriv (gaussianCouplings ι) =ᵐ[
    gaussianCouplings ι]
    (fun g => ENNReal.ofReal ((-f) g)) at hneg
  rw [hmeasure] at hpos
  have heq := hpos.symm.trans hneg
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [heq, Lp.coeFn_neg f] with g hg hgneg
  simp only [Pi.neg_apply] at hgneg
  rw [hgneg] at hg
  have hgreal := congrArg ENNReal.toReal hg
  simp only [ENNReal.toReal_ofReal'] at hgreal
  have h := max_zero_sub_max_neg_zero_eq_self (f g)
  rw [hgreal, sub_self] at h
  exact h.symm

private noncomputable def dualMvPolynomial {ι : Type*} [Fintype ι]
    (L : StrongDual ℝ (ι → ℝ)) : MvPolynomial ι ℝ := by
  classical
  exact ∑ i, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i

private theorem dualMvPolynomial_aeval {ι : Type*} [Fintype ι]
    (L : StrongDual ℝ (ι → ℝ)) (g : ι → ℝ) :
    MvPolynomial.aeval g (dualMvPolynomial L) = L g := by
  classical
  have hsum : (∑ i, Pi.single i (g i)) = g := Finset.univ_sum_single g
  have hcoeff : ∀ i, L (Pi.single i (g i)) = L (Pi.single i 1) * g i := by
    intro i
    have h : Pi.single i (g i) = (g i) • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hij : i = j <;> simp [hij]
    rw [h, map_smul]
    simp [smul_eq_mul, mul_comm]
  calc
    MvPolynomial.aeval g (dualMvPolynomial L) =
        ∑ i, L (Pi.single i (1 : ℝ)) * g i := by
      simp [dualMvPolynomial]
    _ = ∑ i, L (Pi.single i (g i)) := by
      simp only [hcoeff]
    _ = L g := by
      rw [← map_sum, hsum]

/-- Real multivariate polynomial classes are dense in finite product Gaussian `L²`. -/
theorem mvPolynomialLp_dense {ι : Type*} [Fintype ι] :
    (Submodule.span ℝ (Set.range (mvPolynomialLp (ι := ι)))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  apply gaussianLpPi_eq_zero_of_dual_moments_zero f
  intro L n
  let p : MvPolynomial ι ℝ := dualMvPolynomial L ^ n
  have hp : mvPolynomialLp p ∈ Submodule.span ℝ (Set.range (mvPolynomialLp (ι := ι))) :=
    Submodule.subset_span ⟨p, rfl⟩
  have hinner := (Submodule.mem_orthogonal' _ f).mp hf _ hp
  rw [L2.inner_def] at hinner
  have hcoe := (mvPolynomial_eval_memLp_and_hermiteSpan p).choose.coeFn_toLp
  refine (integral_congr_ae ?_).trans hinner
  filter_upwards [hcoe] with g hg
  change f g * (L g) ^ n = (mvPolynomialLp p) g * f g
  have hpoly : MvPolynomial.aeval g p = (L g) ^ n := by
    change MvPolynomial.aeval g (dualMvPolynomial L ^ n) = (L g) ^ n
    rw [map_pow, dualMvPolynomial_aeval]
  rw [mvPolynomialLp, hg, hpoly]
  ring

/-- Normalized Hermite products form a complete family in Gaussian `L²`. -/
theorem hermiteOrthonormal_dense {ι : Type*} [Fintype ι] :
    (Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι)))).topologicalClosure
      = ⊤ :=
  hermiteOrthonormal_dense_of_mvPolynomialLp_dense mvPolynomialLp_dense

/-- The factorial-coefficient Hermite expansion converges in Gaussian `L²`. -/
theorem hasSum_hermiteCoefficients_unconditional {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι)) :
    HasSum (fun α : ι → ℕ =>
      (⟪hermiteLp α, f⟫_ℝ /
        ∏ i : ι, ((α i).factorial : ℝ)) • hermiteLp α) f :=
  hasSum_hermiteCoefficients hermiteOrthonormal_dense f

/-- The sum of homogeneous chaos projections converges in Gaussian `L²`. -/
theorem hasSum_hermiteDegreeProjection_unconditional {ι : Type*} [Fintype ι]
    (f : Lp ℝ 2 (gaussianCouplings ι)) :
    HasSum (fun r : ℕ => hermiteDegreeProjection r f) f :=
  hasSum_hermiteDegreeProjection hermiteOrthonormal_dense f

end SYK.GaussianChaos
