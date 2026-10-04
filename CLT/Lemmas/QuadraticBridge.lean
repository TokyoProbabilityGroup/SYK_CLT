import SYK.CLT.Lemmas.ZeroChaos
import SYK.CLT.Lemmas.SecondChaosAsymptotic
import SYK.CLT.Lemmas.GaussianQuadraticCLT
import SYK.CLT.Lemmas.DistributionTransfer

/-!
# Quadratic Hermite sum and Gaussian-square sum

The second chaos is the exact normalized sum of independent centered
Gaussian squares, with the finite-size coefficient from the manuscript.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace

namespace SYK.CLT

local instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (SYK.gaussianCouplings ι) := by
  unfold SYK.gaussianCouplings
  infer_instance

local instance (N q : ℕ) : IsProbabilityMeasure (standardGaussianMeasure N q) := by
  unfold standardGaussianMeasure
  infer_instance

theorem hermite_sum_ae {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (fun g => (∑ i : ι, hermiteLp (Pi.single i 2) :
      Lp ℝ 2 (SYK.gaussianCouplings ι)) g) =ᵐ[SYK.gaussianCouplings ι]
      fun g => ∑ i : ι, (g i ^ 2 - 1) := by
  classical
  have h (i : ι) := (hermiteMulti_memLp_two (Pi.single i 2)).coeFn_toLp
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : ι => hermiteLp (Pi.single i 2)), Filter.eventually_all.mpr h]
    with g hsum hg
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (hermiteLp (Pi.single i 2)) g = SYK.hermiteMulti (Pi.single i 2) g
    from hg i]
  exact hermiteMulti_single_two i g

noncomputable def quadraticGaussianLp (ι : Type*) [Fintype ι]
    [DecidableEq ι] :
    Lp ℝ 2 (SYK.gaussianCouplings ι) :=
  (Real.sqrt (2 * (Fintype.card ι : ℝ)))⁻¹ •
    ∑ i : ι, hermiteLp (Pi.single i 2)

theorem quadraticGaussianLp_ae {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    (quadraticGaussianLp ι : (ι → ℝ) → ℝ) =ᵐ[SYK.gaussianCouplings ι]
      fun g => (Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
        ∑ i : ι, centeredGaussianSquare (g i) := by
  classical
  have hsum := hermite_sum_ae (ι := ι)
  have hsmul := Lp.coeFn_smul
    (Real.sqrt (2 * (Fintype.card ι : ℝ)))⁻¹
    (∑ i : ι, hermiteLp (Pi.single i 2) : Lp ℝ 2 (SYK.gaussianCouplings ι))
  filter_upwards [hsum, hsmul] with g hg hs
  change (quadraticGaussianLp ι) g = _ at hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs]
  rw [hg]
  simp only [centeredGaussianSquare]
  rw [← Finset.sum_div]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem Setting.Y_secondChaos_eq_quadraticGaussianLp {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 2 (S.YGaussianLp β n) =
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) •
        quadraticGaussianLp (InteractionIndex (S.N n) q) := by
  classical
  have hcard : (Fintype.card (InteractionIndex (S.N n) q) : ℝ) =
      (Nat.choose (S.N n) q : ℝ) := by simp [InteractionIndex]
  have hM : 0 < (Nat.choose (S.N n) q : ℝ) := by
    exact_mod_cast Nat.choose_pos (S.q_le_N n)
  have hsqrt : 0 < Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)) := by
    positivity
  rw [S.Y_secondChaos_eq]
  unfold quadraticGaussianLp
  rw [hcard, smul_smul]
  congr 1
  rw [← div_eq_mul_inv]
  field_simp [ne_of_gt hsqrt, ne_of_gt hM]
  rw [Real.sq_sqrt (show 0 ≤ 2 * (Nat.choose (S.N n) q : ℝ) by positivity)]
  ring

/-- Exact finite-size fluctuation decomposition in Gaussian `L²`. -/
theorem Setting.scaled_Y_decomposition {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    S.fluctuationScale n •
      (S.YGaussianLp β n -
        Lp.const 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ)) =
      (S.fluctuationScale n *
        (β * deriv (fun b => Real.log (S.meanZ b n)) β /
          Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))) •
        quadraticGaussianLp (InteractionIndex (S.N n) q) +
      S.fluctuationScale n • S.higherChaosRemainderLp β n := by
  rw [S.Y_decomposition, S.Y_secondChaos_eq_quadraticGaussianLp]
  simp only [smul_sub, smul_add, smul_smul]
  abel

/-- The `L²` fluctuation represents the model's relative fluctuation. -/
theorem Setting.scaled_YGaussianLp_ae {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    (S.fluctuationScale n •
      (S.YGaussianLp β n -
        Lp.const 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ)) :
      (InteractionIndex (S.N n) q → ℝ) → ℝ) =ᵐ[
        SYK.gaussianCouplings (InteractionIndex (S.N n) q)]
      fun g => S.relativeFluctuation β n (WithLp.toLp 2 g) := by
  have hY := S.YGaussianLp_ae β n
  have hconst := Lp.coeFn_const
    (α := InteractionIndex (S.N n) q → ℝ)
    (μ := SYK.gaussianCouplings (InteractionIndex (S.N n) q))
    (p := 2) (c := (1 : ℝ))
  have hsub := Lp.coeFn_sub (S.YGaussianLp β n)
    (Lp.const 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ))
  have hsmul := Lp.coeFn_smul (S.fluctuationScale n)
    (S.YGaussianLp β n -
      Lp.const 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ))
  filter_upwards [hY, hconst, hsub, hsmul] with g hgY hgconst hgsub hgsmul
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  rw [hgY, hgconst]
  rfl

/-- The same standard Gaussian limit on the product coupling space. -/
theorem Setting.quadraticGaussianLp_clt {q : ℕ} (S : Setting q) :
    TendstoInDistribution
      (fun n => (quadraticGaussianLp (InteractionIndex (S.N n) q) :
        (InteractionIndex (S.N n) q → ℝ) → ℝ))
      atTop (fun x : ℝ => x)
      (fun n => SYK.gaussianCouplings (InteractionIndex (S.N n) q))
      (gaussianReal 0 1) where
  forall_aemeasurable n := (Lp.aestronglyMeasurable _).aemeasurable
  tendsto := by
    have h := S.normalizedQuadraticSum_clt.tendsto
    have heq (n : ℕ) :
        (SYK.gaussianCouplings (InteractionIndex (S.N n) q)).map
          (quadraticGaussianLp (InteractionIndex (S.N n) q) :
            (InteractionIndex (S.N n) q → ℝ) → ℝ) =
        (standardGaussianMeasure (S.N n) q).map
          (normalizedQuadraticSum (S.N n) q) := by
      rw [Measure.map_congr (quadraticGaussianLp_ae (ι := InteractionIndex (S.N n) q))]
      exact (normalizedQuadraticSum_law (S.N n) q).symm
    simpa only [heq] using h

/-- The leading scaled chaos has the conditional Gaussian limit on the
product coupling space at nonzero inverse temperature. The coefficient
calculation itself remains valid at zero inverse temperature. -/
theorem Setting.scaledQuadraticGaussianLp_clt {q : ℕ} (S : Setting q)
    (hFE : AnnealedInput q S) (β : ℝ) (_hβ : β ≠ 0) :
    TendstoInDistribution
      (fun n (g : InteractionIndex (S.N n) q → ℝ) =>
        (S.fluctuationScale n *
          (β * deriv (fun b => Real.log (S.meanZ b n)) β /
            Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))) *
          (quadraticGaussianLp (InteractionIndex (S.N n) q) g))
      atTop
      (fun x : ℝ =>
        (β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2)) * x)
      (fun n => SYK.gaussianCouplings (InteractionIndex (S.N n) q))
      (gaussianReal 0 1) := by
  exact tendstoInDistribution_mul_coeff
    (fun n => SYK.gaussianCouplings (InteractionIndex (S.N n) q))
    (gaussianReal 0 1)
    (fun n => (quadraticGaussianLp (InteractionIndex (S.N n) q) :
      (InteractionIndex (S.N n) q → ℝ) → ℝ))
    (fun x : ℝ => x) S.quadraticGaussianLp_clt
    (fun n => S.fluctuationScale n *
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))))
    (β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2))
    (S.secondChaosScaledCoefficient_tendsto hFE β)

end SYK.CLT
