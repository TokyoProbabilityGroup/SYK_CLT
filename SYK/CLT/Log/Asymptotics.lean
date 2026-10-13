import SYK.CLT.Log.EventBound
import SYK.Probability.LpDistributionTransfer
import SYK.CLT.Limit.EuclideanRelativeCLT
import SYK.CLT.Limit.QuadraticGaussianVariance
import SYK.CLT.Log.Taylor

/-! # Vanishing logarithmic linearization error -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

open SYK.GaussianChaos SYK.Probability

namespace SYK.CLT

private theorem Setting.fluctuationScale_tendsto_atTop {q : ℕ} (S : Setting q) :
    Tendsto S.fluctuationScale atTop atTop := by
  have hN : Tendsto (fun n => (S.N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp S.N_tendsto
  have he : q / 2 - 1 ≠ 0 := by
    have hq := S.q_ge_four
    omega
  change Tendsto (fun n => (S.N n : ℝ) ^ (q / 2 - 1)) atTop atTop
  simpa only [Function.comp_def] using (tendsto_pow_atTop he).comp hN

private theorem Setting.unscaledQuadraticCoefficient_tendsto_zero {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) (β : ℝ) :
    Tendsto (fun n =>
      β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))
      atTop (𝓝 0) := by
  have hscaled := S.secondChaosScaledCoefficient_tendsto hFE β
  have hinv := tendsto_inv_atTop_zero.comp S.fluctuationScale_tendsto_atTop
  have h := hscaled.mul hinv
  have hzero : Tendsto (fun n => S.fluctuationScale n *
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) *
        (S.fluctuationScale n)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using h
  apply hzero.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hs : S.fluctuationScale n ≠ 0 := by
    have hN : (0 : ℝ) < S.N n := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4)
        (S.q_ge_four.trans (S.q_le_N n))
    unfold Setting.fluctuationScale
    exact pow_ne_zero _ hN.ne'
  simp only [Function.comp_apply] at *
  calc
    S.fluctuationScale n *
        (β * deriv (fun b => Real.log (S.meanZ b n)) β /
          Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) *
        (S.fluctuationScale n)⁻¹ =
        (β * deriv (fun b => Real.log (S.meanZ b n)) β /
          Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) *
          (S.fluctuationScale n * (S.fluctuationScale n)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hs, mul_one]

/-- The small-`Y` probability vanishes even after multiplication by the
square of the CLT fluctuation scale. -/
theorem Setting.scaled_sq_Y_lt_half_tendsto_zero {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => S.fluctuationScale n ^ 2 *
        (standardGaussianMeasure (S.N n) q).real
          {g | S.Y β n g < (1 / 2 : ℝ)}) atTop (𝓝 0) := by
  obtain ⟨βq, hβq, hrem⟩ := S.scaled_higherChaosRemainderLp_norm_tendsto_zero
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  let c : ℕ → ℝ := fun n =>
    β * deriv (fun b => Real.log (S.meanZ b n)) β /
      Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))
  have hcScaled : Tendsto (fun n => S.fluctuationScale n * c n) atTop
      (𝓝 (β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2))) := by
    simpa only [c] using S.secondChaosScaledCoefficient_tendsto hFE β
  have hcZero : Tendsto c atTop (𝓝 0) := by
    simpa only [c] using S.unscaledQuadraticCoefficient_tendsto_zero hFE β
  have hlead : Tendsto (fun n => S.fluctuationScale n ^ 2 * c n ^ 4)
      atTop (𝓝 0) := by
    have h := (hcScaled.pow 2).mul (hcZero.pow 2)
    have hzero : Tendsto (fun n => (S.fluctuationScale n * c n) ^ 2 *
        c n ^ 2) atTop (𝓝 0) := by simpa using h
    apply hzero.congr'
    filter_upwards [] with n
    ring
  have hrem2 : Tendsto (fun n => S.fluctuationScale n ^ 2 *
      ‖S.higherChaosRemainderLp β n‖ ^ 2) atTop (𝓝 0) := by
    have h := (hrem β hβ).pow 2
    have hzero : Tendsto (fun n =>
        ‖S.fluctuationScale n • S.higherChaosRemainderLp β n‖ ^ 2)
        atTop (𝓝 0) := by simpa using h
    apply hzero.congr'
    filter_upwards [] with n
    have hs : 0 ≤ S.fluctuationScale n := by
      unfold Setting.fluctuationScale
      positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    ring
  have hUpper : Tendsto (fun n =>
      3840 * (S.fluctuationScale n ^ 2 * c n ^ 4) +
        16 * (S.fluctuationScale n ^ 2 *
          ‖S.higherChaosRemainderLp β n‖ ^ 2)) atTop (𝓝 0) := by
    simpa using (hlead.const_mul 3840).add (hrem2.const_mul 16)
  refine squeeze_zero ?_ ?_ hUpper
  · intro n
    exact mul_nonneg (sq_nonneg _) measureReal_nonneg
  · intro n
    have htail := S.Y_lt_half_le_moments β n
    have hs : 0 ≤ S.fluctuationScale n ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left htail hs
    calc
      S.fluctuationScale n ^ 2 *
          (standardGaussianMeasure (S.N n) q).real
            {g | S.Y β n g < (1 / 2 : ℝ)} ≤
          S.fluctuationScale n ^ 2 *
            (3840 * c n ^ 4 +
              16 * ‖S.higherChaosRemainderLp β n‖ ^ 2) := by
                simpa only [c] using hmul
      _ = 3840 * (S.fluctuationScale n ^ 2 * c n ^ 4) +
          16 * (S.fluctuationScale n ^ 2 *
            ‖S.higherChaosRemainderLp β n‖ ^ 2) := by ring

private theorem Setting.N_le_fluctuationScale {q : ℕ} (S : Setting q) (n : ℕ) :
    (S.N n : ℝ) ≤ S.fluctuationScale n := by
  have hN : (1 : ℝ) ≤ S.N n := by
    exact_mod_cast (show 1 ≤ S.N n from
      le_trans (by decide : 1 ≤ 4) (S.q_ge_four.trans (S.q_le_N n)))
  have he : q / 2 - 1 ≠ 0 := by
    have hq := S.q_ge_four
    omega
  exact le_self_pow₀ hN he

/-- The lower-tail contribution to the logarithmic error is negligible at
the CLT scale, including the linear growth of the annealed pressure. -/
private theorem Setting.scaled_log_meanZ_Y_lt_half_tendsto_zero {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => S.fluctuationScale n * Real.log (S.meanZ β n) *
        (standardGaussianMeasure (S.N n) q).real
          {g | S.Y β n g < (1 / 2 : ℝ)}) atTop (𝓝 0) := by
  obtain ⟨βq, hβq, htail⟩ := S.scaled_sq_Y_lt_half_tendsto_zero hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  obtain ⟨C, hC, hlinear⟩ := S.log_meanZ_le_linear_eventually hFE β
  have hupper := (htail β hβ).const_mul C
  refine squeeze_zero' ?_ ?_ (by simpa using hupper)
  · apply Filter.Eventually.of_forall
    intro n
    exact mul_nonneg (mul_nonneg (by unfold Setting.fluctuationScale; positivity)
      (S.log_meanZ_nonneg β n)) measureReal_nonneg
  · filter_upwards [hlinear] with n hn
    have hs : 0 ≤ S.fluctuationScale n := by
      unfold Setting.fluctuationScale
      positivity
    have hp : 0 ≤ (standardGaussianMeasure (S.N n) q).real
        {g | S.Y β n g < (1 / 2 : ℝ)} := measureReal_nonneg
    have hlog : Real.log (S.meanZ β n) ≤ C * S.fluctuationScale n :=
      hn.trans (mul_le_mul_of_nonneg_left (S.N_le_fluctuationScale n) hC)
    have h := mul_le_mul_of_nonneg_left hlog hs
    have h' := mul_le_mul_of_nonneg_right h hp
    simp only [one_div] at h'
    simp only [one_div]
    change S.fluctuationScale n * Real.log (S.meanZ β n) *
      (standardGaussianMeasure (S.N n) q).real
        {g | S.Y β n g < (2 : ℝ)⁻¹} ≤
      C * (S.fluctuationScale n ^ 2 *
        (standardGaussianMeasure (S.N n) q).real
          {g | S.Y β n g < (2 : ℝ)⁻¹})
    calc
      _ ≤ S.fluctuationScale n * (C * S.fluctuationScale n) *
        (standardGaussianMeasure (S.N n) q).real
          {g | S.Y β n g < (2 : ℝ)⁻¹} := h'
      _ = _ := by ring

/-- The expected logarithmic Taylor error is bounded by the relative variance
and the small-partition-function tail. -/
theorem Setting.integral_logLinearError_le_variance_tail {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    (∫ g, S.logLinearError β n g ∂standardGaussianMeasure (S.N n) q) ≤
      2 * variance (S.Y β n) (standardGaussianMeasure (S.N n) q) +
      Real.log (S.meanZ β n) *
        (standardGaussianMeasure (S.N n) q).real
          {g | S.Y β n g < (1 / 2 : ℝ)} := by
  let μ := standardGaussianMeasure (S.N n) q
  let bad : Set (CouplingSpace (S.N n) q) :=
    {g | S.Y β n g < (1 / 2 : ℝ)}
  have hcont : Continuous (S.Y β n) := by
    unfold Setting.Y Setting.Z
    exact (realPartitionFunction_continuous (S.params n) (S.majorana n) β).div_const _
  have hbad : MeasurableSet bad := hcont.measurable measurableSet_Iio
  have hsq : Integrable (fun g => (S.Y β n g - 1) ^ 2) μ :=
    ((S.Y_memLp β n).sub (memLp_const (1 : ℝ))).integrable_sq
  have hbound : Integrable (fun g =>
      2 * (S.Y β n g - 1) ^ 2 +
        bad.indicator (fun _ => Real.log (S.meanZ β n)) g) μ :=
    hsq.const_mul 2 |>.add ((integrable_const _).indicator hbad)
  have hpoint (g : CouplingSpace (S.N n) q) :
      S.logLinearError β n g ≤
        2 * (S.Y β n g - 1) ^ 2 +
          bad.indicator (fun _ => Real.log (S.meanZ β n)) g := by
    by_cases hg : g ∈ bad
    · have hlog := S.logLinearError_le_log_meanZ_of_lt_half β n g hg
      simp only [Set.indicator_of_mem hg]
      nlinarith [sq_nonneg (S.Y β n g - 1)]
    · have hhalf : (1 / 2 : ℝ) ≤ S.Y β n g := by
        simp only [bad, Set.mem_setOf_eq, not_lt] at hg
        exact hg
      simpa only [Set.indicator_of_notMem hg, add_zero] using
        S.logLinearError_le_sq_of_half_le β n g hhalf
  have hmono := integral_mono (S.logLinearError_integrable β n) hbound hpoint
  have hvar : variance (S.Y β n) μ =
      ∫ g, (S.Y β n g - 1) ^ 2 ∂μ := by
    rw [variance_eq_integral (S.Y_memLp β n).aestronglyMeasurable.aemeasurable,
      S.integral_Y]
  dsimp only [μ] at hvar
  rw [integral_add (hsq.const_mul 2) ((integrable_const _).indicator hbad),
    integral_const_mul, integral_indicator_const _ hbad] at hmono
  simpa only [hvar, smul_eq_mul, mul_comm] using hmono

private theorem Setting.varianceY_eq_varianceY_pi {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    variance (S.Y β n) (standardGaussianMeasure (S.N n) q) =
      variance (fun g : InteractionIndex (S.N n) q → ℝ =>
        S.Y β n (WithLp.toLp 2 g))
        (gaussianCouplings (InteractionIndex (S.N n) q)) := by
  change variance (S.Y β n)
    ((gaussianCouplings (InteractionIndex (S.N n) q)).map
      (MeasurableEquiv.toLp 2 (InteractionIndex (S.N n) q → ℝ))) = _
  rw [variance_map_equiv]
  rfl

private theorem Setting.scaled_varianceY_tendsto {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => S.fluctuationScale n ^ 2 *
        variance (S.Y β n) (standardGaussianMeasure (S.N n) q))
        atTop (𝓝 (limitVariance q hFE.ℓ β : ℝ)) := by
  obtain ⟨βq, hβq, hvar⟩ := S.scaled_varianceY_pi_tendsto hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  simpa only [S.varianceY_eq_varianceY_pi] using hvar β hβ

private theorem Setting.scaled_varianceY_tendsto_zero {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => S.fluctuationScale n *
        variance (S.Y β n) (standardGaussianMeasure (S.N n) q))
        atTop (𝓝 0) := by
  obtain ⟨βq, hβq, hvar⟩ := S.scaled_varianceY_tendsto hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  have hinv := tendsto_inv_atTop_zero.comp S.fluctuationScale_tendsto_atTop
  have h := (hvar β hβ).mul hinv
  have hs : ∀ n, S.fluctuationScale n ≠ 0 := by
    intro n
    have hN : (0 : ℝ) < S.N n := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4)
        (S.q_ge_four.trans (S.q_le_N n))
    exact pow_ne_zero _ hN.ne'
  convert h using 1
  · funext n
    have hn := hs n
    simp only [Function.comp_apply]
    calc
      _ = S.fluctuationScale n *
          (S.fluctuationScale n * (S.fluctuationScale n)⁻¹) *
          variance (S.Y β n) (standardGaussianMeasure (S.N n) q) := by
            rw [mul_inv_cancel₀ hn, mul_one]
      _ = _ := by ring
  · simp

/-- The bad event in the proof of `thm:free-energy-clt` has probability
`O(N^(-3a))`, where `a = q/2 - 1`. The bound uses fourth moments of the
second chaos and the quantitative higher-chaos remainder bound. -/
theorem Setting.cubed_scale_Y_lt_half_bounded {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        S.fluctuationScale n ^ 3 *
          (standardGaussianMeasure (S.N n) q).real
            {g | S.Y β n g < (1 / 2 : ℝ)} ≤ C := by
  obtain ⟨r, hr, R, hR⟩ := S.higherChaosRemainderLp_le_power
  refine ⟨r, hr, ?_⟩
  intro β hβ
  let c : ℕ → ℝ := fun n =>
    β * deriv (fun b => Real.log (S.meanZ b n)) β /
      Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))
  let L := β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2)
  have hc : Tendsto (fun n => S.fluctuationScale n * c n) atTop (𝓝 L) :=
    S.secondChaosScaledCoefficient_tendsto hFE β
  have hc4 := (hc.pow 4).eventually_lt_const (lt_add_one (L ^ 4))
  have ha : ((q / 2 - 1 : ℕ) : ℝ) = (q : ℝ) / 2 - 1 := by
    have hq := S.q_ge_four
    have he : q / 2 * 2 = q := Nat.div_mul_cancel (even_iff_two_dvd.mp S.q_even)
    have he' : (q / 2 : ℕ) * (2 : ℝ) = (q : ℝ) := by exact_mod_cast he
    rw [Nat.cast_sub (by omega : 1 ≤ q / 2), Nat.cast_one]
    linarith
  refine ⟨3840 * (L ^ 4 + 1) + 16 * |R|, by positivity, ?_⟩
  filter_upwards [hc4] with n hn
  have hN : (0 : ℝ) < S.N n := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4)
      (S.q_ge_four.trans (S.q_le_N n))
  have hs : 1 ≤ S.fluctuationScale n :=
    (show (1 : ℝ) ≤ S.N n by exact_mod_cast
      (show 1 ≤ S.N n by have := S.q_le_N n; have := S.q_ge_four; omega)).trans
        (S.N_le_fluctuationScale n)
  have hpower : S.fluctuationScale n ^ 3 *
      (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1)) = 1 := by
    have hscale : S.fluctuationScale n =
        (S.N n : ℝ) ^ ((q : ℝ) / 2 - 1) := by
      rw [Setting.fluctuationScale, ← Real.rpow_natCast, ha]
    rw [hscale]
    calc
      _ = (S.N n : ℝ) ^ (((q : ℝ) / 2 - 1) * 3) *
          (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1)) := by
        rw [Real.rpow_mul hN.le ((q : ℝ) / 2 - 1) (3 : ℝ), Real.rpow_ofNat]
      _ = (S.N n : ℝ) ^
          (((q : ℝ) / 2 - 1) * 3 + -3 * ((q : ℝ) / 2 - 1)) :=
        (Real.rpow_add hN _ _).symm
      _ = 1 := by ring_nf; simp
  have hrem : S.fluctuationScale n ^ 3 *
      ‖S.higherChaosRemainderLp β n‖ ^ 2 ≤ |R| := by
    calc
      _ ≤ S.fluctuationScale n ^ 3 *
          (R * (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1))) :=
        mul_le_mul_of_nonneg_left (hR β hβ n) (by positivity)
      _ = R := by rw [mul_left_comm, hpower, mul_one]
      _ ≤ |R| := le_abs_self _
  have hlead : S.fluctuationScale n ^ 3 * c n ^ 4 ≤ L ^ 4 + 1 := by
    calc
      _ ≤ (S.fluctuationScale n * c n) ^ 4 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs)
          (show 0 ≤ S.fluctuationScale n ^ 3 * c n ^ 4 by positivity)]
      _ ≤ L ^ 4 + 1 := hn.le
  have htail := mul_le_mul_of_nonneg_left (S.Y_lt_half_le_moments β n)
    (show 0 ≤ S.fluctuationScale n ^ 3 by positivity)
  change S.fluctuationScale n ^ 3 * _ ≤
    S.fluctuationScale n ^ 3 *
      (3840 * c n ^ 4 + 16 * ‖S.higherChaosRemainderLp β n‖ ^ 2) at htail
  nlinarith

/-- The explicit expected-logarithm error in `thm:free-energy-clt`.
For each fixed nonzero high-temperature real `β`,
`E[log Y_N] = O(N^(-2a))`, with `a = q/2 - 1`.
The annealed proposition is an explicit input; the constant need not be
uniform in `β`. -/
theorem Setting.integral_log_Y_isBigO {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq → β ≠ 0 →
      (fun n => ∫ g, Real.log (S.Y β n g)
        ∂standardGaussianMeasure (S.N n) q) =O[atTop]
        (fun n => ((S.N n : ℝ) ^ (2 * (q / 2 - 1)))⁻¹) := by
  obtain ⟨rv, hrv, hv⟩ := S.scaled_varianceY_tendsto hFE
  obtain ⟨rt, hrt, ht⟩ := S.cubed_scale_Y_lt_half_bounded hFE
  refine ⟨min rv rt, lt_min hrv hrt, ?_⟩
  intro β hβ _hβ0
  have hβv := lt_of_lt_of_le hβ (min_le_left rv rt)
  have hβt := lt_of_lt_of_le hβ (min_le_right rv rt)
  obtain ⟨T, hT, htail⟩ := ht β hβt
  obtain ⟨A, hA, hlog⟩ := S.log_meanZ_le_linear_eventually hFE β
  let V : ℝ := (limitVariance q hFE.ℓ β : ℝ) + 1
  have hvar := (hv β hβv).eventually_lt_const
    (lt_add_one (limitVariance q hFE.ℓ β : ℝ))
  apply Asymptotics.IsBigO.of_bound (2 * V + A * T)
  filter_upwards [htail, hlog, hvar] with n hnT hnA hnV
  have hs : 0 < S.fluctuationScale n := by
    have hN : (0 : ℝ) < S.N n := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4)
        (S.q_ge_four.trans (S.q_le_N n))
    exact pow_pos hN _
  have hAn : Real.log (S.meanZ β n) ≤ A * S.fluctuationScale n :=
    hnA.trans (mul_le_mul_of_nonneg_left (S.N_le_fluctuationScale n) hA)
  have htailbound : S.fluctuationScale n ^ 2 * Real.log (S.meanZ β n) *
      (standardGaussianMeasure (S.N n) q).real
        {g | S.Y β n g < (1 / 2 : ℝ)} ≤ A * T := by
    calc
      _ ≤ S.fluctuationScale n ^ 2 * (A * S.fluctuationScale n) *
          (standardGaussianMeasure (S.N n) q).real
            {g | S.Y β n g < (1 / 2 : ℝ)} :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAn (sq_nonneg _)) measureReal_nonneg
      _ = A * (S.fluctuationScale n ^ 3 *
          (standardGaussianMeasure (S.N n) q).real
            {g | S.Y β n g < (1 / 2 : ℝ)}) := by ring
      _ ≤ A * T := mul_le_mul_of_nonneg_left hnT hA
  have hbound := mul_le_mul_of_nonneg_left
    (S.integral_logLinearError_le_variance_tail β n)
    (sq_nonneg (S.fluctuationScale n))
  have herr : S.fluctuationScale n ^ 2 *
      (∫ g, S.logLinearError β n g ∂standardGaussianMeasure (S.N n) q) ≤
      2 * V + A * T := by
    calc
      _ ≤ S.fluctuationScale n ^ 2 *
          (2 * variance (S.Y β n) (standardGaussianMeasure (S.N n) q) +
            Real.log (S.meanZ β n) *
              (standardGaussianMeasure (S.N n) q).real
                {g | S.Y β n g < (1 / 2 : ℝ)}) := hbound
      _ = 2 * (S.fluctuationScale n ^ 2 *
          variance (S.Y β n) (standardGaussianMeasure (S.N n) q)) +
            S.fluctuationScale n ^ 2 * Real.log (S.meanZ β n) *
              (standardGaussianMeasure (S.N n) q).real
                {g | S.Y β n g < (1 / 2 : ℝ)} := by ring
      _ ≤ 2 * V + A * T :=
        add_le_add (mul_le_mul_of_nonneg_left hnV.le (by norm_num)) htailbound
  have hnorm : ‖∫ g, Real.log (S.Y β n g)
      ∂standardGaussianMeasure (S.N n) q‖ =
      ∫ g, S.logLinearError β n g ∂standardGaussianMeasure (S.N n) q := by
    rw [← norm_neg, ← S.integral_logLinearError, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (S.logLinearError_nonneg β n))]
  have hpow : (S.N n : ℝ) ^ (2 * (q / 2 - 1)) =
      S.fluctuationScale n ^ 2 := by
    rw [Nat.mul_comm 2, pow_mul]
    rfl
  rw [hnorm, hpow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hs))]
  rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos hs)]
  simpa only [mul_comm] using herr

/-- At high temperature the mean logarithmic Taylor error vanishes on the
scale of the central limit theorem. -/
theorem Setting.scaled_integral_logLinearError_tendsto_zero {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => S.fluctuationScale n *
        (∫ g, S.logLinearError β n g ∂standardGaussianMeasure (S.N n) q))
        atTop (𝓝 0) := by
  obtain ⟨rvar, hrvar, hvar⟩ := S.scaled_varianceY_tendsto_zero hFE
  obtain ⟨rtail, hrtail, htail⟩ := S.scaled_log_meanZ_Y_lt_half_tendsto_zero hFE
  refine ⟨min rvar rtail, lt_min hrvar hrtail, ?_⟩
  intro β hβ
  have hβvar : |β| < rvar := lt_of_lt_of_le hβ (min_le_left _ _)
  have hβtail : |β| < rtail := lt_of_lt_of_le hβ (min_le_right _ _)
  have hupper : Tendsto (fun n =>
      2 * (S.fluctuationScale n *
        variance (S.Y β n) (standardGaussianMeasure (S.N n) q)) +
      S.fluctuationScale n * Real.log (S.meanZ β n) *
        (standardGaussianMeasure (S.N n) q).real
          {g | S.Y β n g < (1 / 2 : ℝ)}) atTop (𝓝 0) := by
    simpa using ((hvar β hβvar).const_mul 2).add (htail β hβtail)
  refine squeeze_zero ?_ ?_ hupper
  · intro n
    exact mul_nonneg (by unfold Setting.fluctuationScale; positivity)
      (integral_nonneg fun g => S.logLinearError_nonneg β n g)
  · intro n
    have hs : 0 ≤ S.fluctuationScale n := by
      unfold Setting.fluctuationScale
      positivity
    have h := mul_le_mul_of_nonneg_left
      (S.integral_logLinearError_le_variance_tail β n) hs
    simp only [one_div] at h ⊢
    calc
      _ ≤ S.fluctuationScale n *
        (2 * variance (S.Y β n) (standardGaussianMeasure (S.N n) q) +
          Real.log (S.meanZ β n) *
            (standardGaussianMeasure (S.N n) q).real
              {g | S.Y β n g < (2 : ℝ)⁻¹}) := h
      _ = _ := by ring

private theorem integral_norm_centered_le_two_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Ω → ℝ) (hE : Integrable E μ)
    (hEnonneg : ∀ ω, 0 ≤ E ω) :
    (∫ ω, ‖E ω - ∫ x, E x ∂μ‖ ∂μ) ≤ 2 * ∫ x, E x ∂μ := by
  have hmean : 0 ≤ ∫ x, E x ∂μ := integral_nonneg hEnonneg
  have hcent : Integrable (fun ω => E ω - ∫ x, E x ∂μ) μ :=
    hE.sub (integrable_const _)
  have hbound : ∀ ω, ‖E ω - ∫ x, E x ∂μ‖ ≤ E ω + ∫ x, E x ∂μ := by
    intro ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hEnonneg ω),
      abs_of_nonneg hmean] using norm_sub_le (E ω) (∫ x, E x ∂μ)
  have h := integral_mono hcent.norm (hE.add (integrable_const _)) hbound
  simp only [Pi.add_apply] at h
  rw [integral_add hE (integrable_const _)] at h
  simpa [two_mul] using h

theorem Setting.scaled_centered_logLinearError_l1_tendsto_zero {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => ∫ g,
        ‖S.fluctuationScale n *
          (S.logLinearError β n g -
            ∫ x, S.logLinearError β n x ∂standardGaussianMeasure (S.N n) q)‖
          ∂standardGaussianMeasure (S.N n) q) atTop (𝓝 0) := by
  obtain ⟨βq, hβq, hmean⟩ := S.scaled_integral_logLinearError_tendsto_zero hFE
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  have hupper := (hmean β hβ).const_mul 2
  refine squeeze_zero ?_ ?_ (by simpa using hupper)
  · intro n
    exact integral_nonneg fun g => norm_nonneg _
  · intro n
    let μ := standardGaussianMeasure (S.N n) q
    let E := S.logLinearError β n
    have hs : 0 ≤ S.fluctuationScale n := by
      unfold Setting.fluctuationScale
      positivity
    have hbound := integral_norm_centered_le_two_integral μ E
      (S.logLinearError_integrable β n) (S.logLinearError_nonneg β n)
    have hmul := mul_le_mul_of_nonneg_left hbound hs
    have heq : (∫ g, ‖S.fluctuationScale n *
        (E g - ∫ x, E x ∂μ)‖ ∂μ) =
        S.fluctuationScale n * (∫ g, ‖E g - ∫ x, E x ∂μ‖ ∂μ) := by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hs, integral_const_mul]
    rw [heq]
    simpa [μ, E, standardGaussianMeasure] using (show
      S.fluctuationScale n * (∫ g, ‖E g - ∫ x, E x ∂μ‖ ∂μ) ≤
        2 * (S.fluctuationScale n * ∫ x, E x ∂μ) from by
          calc
            _ ≤ S.fluctuationScale n * (2 * ∫ x, E x ∂μ) := hmul
            _ = _ := by ring)

/-- The centered log partition function has the same Gaussian limit as the
relative partition function. -/
theorem Setting.logFluctuation_clt {q : ℕ}
    (S : Setting q) (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq → β ≠ 0 →
      TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ => x)
        (fun n => standardGaussianMeasure (S.N n) q)
        (gaussianReal 0 (limitVariance q hFE.ℓ β)) := by
  obtain ⟨rrel, hrrel, hrel⟩ := S.relativeFluctuation_clt hFE
  obtain ⟨rerr, hrerr, herr⟩ := S.scaled_centered_logLinearError_l1_tendsto_zero hFE
  refine ⟨min rrel rerr, lt_min hrrel hrerr, ?_⟩
  intro β hβ hβ0
  have hβrel : |β| < rrel := lt_of_lt_of_le hβ (min_le_left _ _)
  have hβerr : |β| < rerr := lt_of_lt_of_le hβ (min_le_right _ _)
  have heq (n : ℕ) (g : CouplingSpace (S.N n) q) :
      S.logFluctuation β n g - S.relativeFluctuation β n g =
        -(S.fluctuationScale n *
          (S.logLinearError β n g -
            ∫ x, S.logLinearError β n x ∂standardGaussianMeasure (S.N n) q)) := by
    rw [S.logFluctuation_eq_relative_sub_centeredError]
    ring
  have hY (n : ℕ) :
      AEMeasurable (S.logFluctuation β n)
        (standardGaussianMeasure (S.N n) q) := by
    have hlog := ((S.partition_moments β n).2.1).aestronglyMeasurable.aemeasurable
    unfold Setting.logFluctuation
    exact (hlog.sub_const _).const_mul _
  have hErrInt (n : ℕ) :
      Integrable (fun g => S.logFluctuation β n g - S.relativeFluctuation β n g)
        (standardGaussianMeasure (S.N n) q) := by
    have hE := ((S.logLinearError_integrable β n).sub
      (integrable_const (∫ x, S.logLinearError β n x
        ∂standardGaussianMeasure (S.N n) q))).const_mul
      (S.fluctuationScale n)
    have hNeg := hE.neg
    exact hNeg.congr (ae_of_all _ fun g => (heq n g).symm)
  have hErr : Tendsto (fun n => ∫ g,
      ‖S.logFluctuation β n g - S.relativeFluctuation β n g‖
        ∂standardGaussianMeasure (S.N n) q) atTop (𝓝 0) := by
    simpa only [heq, norm_neg] using herr β hβerr
  exact varying_l1_perturb_clt
    (fun n => standardGaussianMeasure (S.N n) q)
    (gaussianReal 0 (limitVariance q hFE.ℓ β))
    (S.relativeFluctuation β) (S.logFluctuation β) (fun x : ℝ => x)
    (hrel β hβrel hβ0) hY hErrInt hErr

end SYK.CLT
