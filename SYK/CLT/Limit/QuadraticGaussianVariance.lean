import SYK.CLT.Limit.EuclideanRelativeCLT

/-!
# Variance of the normalized quadratic Gaussian chaos

The quadratic term in the partition-function fluctuation has unit L² norm.
This is the exact finite-size normalization needed for the variance limit.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology InnerProductSpace

open SYK.GaussianChaos

namespace SYK.CLT

theorem inner_hermiteLp_single_two {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j : ι) :
    ⟪hermiteLp (Pi.single i 2), hermiteLp (Pi.single j 2)⟫_ℝ =
      if i = j then 2 else 0 := by
  rw [inner_hermiteLp]
  by_cases hij : i = j
  · subst j
    simp [hermiteFactorial_single_two]
  · have hne : (Pi.single i 2 : ι → ℕ) ≠ Pi.single j 2 := by
      intro h
      have hi := congrFun h i
      simp [hij] at hi
    simp [hij, hne]

theorem quadraticGaussianLp_norm_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] : ‖quadraticGaussianLp ι‖ ^ 2 = 1 := by
  classical
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hinner :
      ⟪(∑ i : ι, hermiteLp (Pi.single i 2) : Lp ℝ 2 (gaussianCouplings ι)),
        (∑ i : ι, hermiteLp (Pi.single i 2) : Lp ℝ 2 (gaussianCouplings ι))⟫_ℝ =
        2 * (Fintype.card ι : ℝ) := by
    rw [inner_sum]
    simp_rw [sum_inner, inner_hermiteLp_single_two]
    simp
    ring
  rw [← real_inner_self_eq_norm_sq, quadraticGaussianLp,
    real_inner_smul_left, inner_smul_right, hinner]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hcard.le]

/-- The quadratic chaos is orthogonal to the full higher-degree remainder. -/
theorem Setting.inner_secondChaos_higherChaosRemainder_eq_zero {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    ⟪hermiteDegreeProjection 2 (S.YGaussianLp β n),
      S.higherChaosRemainderLp β n⟫_ℝ = 0 := by
  let f := S.YGaussianLp β n
  let v : ℕ → Lp ℝ 2 (gaussianCouplings (InteractionIndex (S.N n) q)) :=
    fun k => hermiteDegreeProjection (k + 3) f
  have hsum : HasSum v (S.higherChaosRemainderLp β n) := by
    exact (hasSum_nat_add_iff' 3).mpr (hasSum_hermiteDegreeProjection_unconditional f)
  have hinner (k : ℕ) :
      ⟪hermiteDegreeProjection 2 f, v k⟫_ℝ = 0 := by
    exact inner_hermiteDegreeProjection_eq_zero 2 (k + 3) (by omega) f f
  have hh := hsum.mapL ((innerSL ℝ) (hermiteDegreeProjection 2 f))
  change HasSum (fun k => ⟪hermiteDegreeProjection 2 f, v k⟫_ℝ)
    ⟪hermiteDegreeProjection 2 f, S.higherChaosRemainderLp β n⟫_ℝ at hh
  simpa only [hinner, tsum_zero] using hh.tsum_eq.symm

/-- The disorder variance of the relative partition function is its centered
Gaussian `L²` norm squared on the product coupling space. -/
theorem Setting.varianceY_pi_eq_norm_sq {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    variance (fun g : InteractionIndex (S.N n) q → ℝ =>
      S.Y β n (WithLp.toLp 2 g))
      (gaussianCouplings (InteractionIndex (S.N n) q)) =
      ‖S.YGaussianLp β n -
        Lp.const 2 (gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ)‖ ^ 2 := by
  let ι := InteractionIndex (S.N n) q
  let μ := gaussianCouplings ι
  have hY : MemLp (fun g : ι → ℝ => S.Y β n (WithLp.toLp 2 g)) 2 μ := by
    exact (Lp.memLp (S.YGaussianLp β n)).ae_eq (S.YGaussianLp_ae β n)
  rw [variance_eq_integral hY.aemeasurable, integral_Y_pi S β n]
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (S.YGaussianLp β n) (Lp.const 2 μ (1 : ℝ)),
    S.YGaussianLp_ae β n,
    Lp.coeFn_const (α := ι → ℝ) (μ := μ) (p := 2) (c := (1 : ℝ))]
    with g hsub hgauss hconst
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hgauss, hconst]
  simp [Real.norm_eq_abs, sq_abs]

/-- Exact finite-size variance split into the quadratic chaos and the
higher-degree remainder. -/
theorem Setting.varianceY_pi_decomposition {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    variance (fun g : InteractionIndex (S.N n) q → ℝ =>
      S.Y β n (WithLp.toLp 2 g))
      (gaussianCouplings (InteractionIndex (S.N n) q)) =
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) ^ 2 +
      ‖S.higherChaosRemainderLp β n‖ ^ 2 := by
  have hcard : 0 < Fintype.card (InteractionIndex (S.N n) q) := by
    simpa [InteractionIndex] using Nat.choose_pos (S.q_le_N n)
  letI : Nonempty (InteractionIndex (S.N n) q) := Fintype.card_pos_iff.mp hcard
  have heq : S.YGaussianLp β n -
      Lp.const 2 (gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ) =
      hermiteDegreeProjection 2 (S.YGaussianLp β n) +
        S.higherChaosRemainderLp β n := by
    calc
      _ = (Lp.const 2 (gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ) +
          hermiteDegreeProjection 2 (S.YGaussianLp β n) +
          S.higherChaosRemainderLp β n) -
          Lp.const 2 (gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ) := by
            exact congrArg (fun x => x -
              Lp.const 2 (gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ))
              (S.Y_decomposition β n)
      _ = _ := by abel
  rw [S.varianceY_pi_eq_norm_sq, heq]
  rw [norm_add_sq_real, S.inner_secondChaos_higherChaosRemainder_eq_zero]
  rw [S.Y_secondChaos_eq_quadraticGaussianLp]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    quadraticGaussianLp_norm_sq, mul_one]
  ring

/-- The variance of the scaled relative partition function has the stated
limiting value on the product coupling space. -/
theorem Setting.scaled_varianceY_pi_tendsto {q : ℕ} (S : Setting q)
    (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => S.fluctuationScale n ^ 2 *
        variance (fun g : InteractionIndex (S.N n) q → ℝ =>
          S.Y β n (WithLp.toLp 2 g))
          (gaussianCouplings (InteractionIndex (S.N n) q)))
        atTop (𝓝 (limitVariance q hFE.ℓ β : ℝ)) := by
  obtain ⟨βq, hβq, hrem⟩ := S.scaled_higherChaosRemainderLp_norm_tendsto_zero
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  have hcoeff := (S.secondChaosScaledCoefficient_tendsto hFE β).pow 2
  have htail := (hrem β hβ).pow 2
  have hsum := hcoeff.add htail
  have heq (n : ℕ) : S.fluctuationScale n ^ 2 *
      variance (fun g : InteractionIndex (S.N n) q → ℝ =>
        S.Y β n (WithLp.toLp 2 g))
        (gaussianCouplings (InteractionIndex (S.N n) q)) =
      (S.fluctuationScale n *
        (β * deriv (fun b => Real.log (S.meanZ b n)) β /
          Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))) ^ 2 +
        ‖S.fluctuationScale n • S.higherChaosRemainderLp β n‖ ^ 2 := by
    rw [S.varianceY_pi_decomposition, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ S.fluctuationScale n by
        unfold Setting.fluctuationScale
        positivity)]
    ring
  simpa [heq, limitVariance_eq_scaledCoefficient_sq] using hsum

/-- The Euclidean disorder variance is the product-space relative variance,
multiplied by the square of the partition-function mean. -/
theorem Setting.varianceZ_eq_mean_sq_varianceY_pi {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    S.varianceZ β n = (S.meanZ β n) ^ 2 *
      variance (fun g : InteractionIndex (S.N n) q → ℝ =>
        S.Y β n (WithLp.toLp 2 g))
        (gaussianCouplings (InteractionIndex (S.N n) q)) := by
  have hZ : S.Z β n = fun g => S.meanZ β n * S.Y β n g := by
    funext g
    simp only [Setting.Y]
    field_simp [(ne_of_gt (S.partition_moments β n).2.2)]
  rw [Setting.varianceZ, hZ, variance_const_mul]
  change (S.meanZ β n) ^ 2 *
      variance (S.Y β n)
        ((gaussianCouplings (InteractionIndex (S.N n) q)).map
          (MeasurableEquiv.toLp 2 (InteractionIndex (S.N n) q → ℝ))) = _
  rw [variance_map_equiv]
  rfl

/-- Exact normalization of the partition-function variance has the predicted
nonzero-inverse-temperature limit. -/
theorem Setting.scaled_varianceZ_over_mean_sq_tendsto {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => S.fluctuationScale n ^ 2 * S.varianceZ β n /
        S.meanZ β n ^ 2) atTop
        (𝓝 (limitVariance q hFE.ℓ β : ℝ)) := by
  obtain ⟨βq, hβq, hvar⟩ := S.scaled_varianceY_pi_tendsto hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  have heq (n : ℕ) : S.fluctuationScale n ^ 2 * S.varianceZ β n /
      S.meanZ β n ^ 2 =
      S.fluctuationScale n ^ 2 *
        variance (fun g : InteractionIndex (S.N n) q → ℝ =>
          S.Y β n (WithLp.toLp 2 g))
          (gaussianCouplings (InteractionIndex (S.N n) q)) := by
    rw [S.varianceZ_eq_mean_sq_varianceY_pi]
    field_simp [(ne_of_gt (S.partition_moments β n).2.2)]
  simpa only [heq] using hvar β hβ

end SYK.CLT
