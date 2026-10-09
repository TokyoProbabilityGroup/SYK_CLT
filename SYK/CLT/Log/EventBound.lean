import SYK.CLT.Quadratic.IndependentFourthMoment
import SYK.CLT.Limit.QuadraticBridge

/-! # Small-event estimates for the logarithmic CLT -/

open MeasureTheory ProbabilityTheory

open SYK.GaussianChaos

namespace SYK.CLT

local instance (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (gaussianCouplings ι) := by
  unfold gaussianCouplings
  infer_instance

private theorem integral_Lp_sq_eq_norm_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (R : Lp ℝ 2 μ) :
    (∫ ω, R ω ^ 2 ∂μ) = ‖R‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  congr 1
  funext ω
  simp [Real.norm_eq_abs, sq_abs]

theorem measureReal_abs_ge_le_fourth {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable (fun ω => X ω ^ 4) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ (∫ ω, X ω ^ 4 ∂μ) / t ^ 4 := by
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ^ 4 ≤ X ω ^ 4} := by
    intro ω hω
    have hpow := pow_le_pow_left₀ ht.le hω 4
    have habs : |X ω| ^ 4 = X ω ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    simpa only [Set.mem_setOf_eq, habs] using hpow
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (f := fun ω => X ω ^ 4) (ae_of_all _ fun ω => by positivity) hX (t ^ 4)
  have hle := measureReal_mono (μ := μ) hsub
  have ht4 : 0 < t ^ 4 := pow_pos ht _
  have hbound : t ^ 4 * μ.real {ω | t ≤ |X ω|} ≤
      ∫ ω, X ω ^ 4 ∂μ :=
    (mul_le_mul_of_nonneg_left hle ht4.le).trans hmarkov
  exact (le_div_iff₀ ht4).2 (by simpa only [mul_comm] using hbound)

theorem measureReal_abs_ge_le_second {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable (fun ω => X ω ^ 2) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ (∫ ω, X ω ^ 2 ∂μ) / t ^ 2 := by
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ^ 2 ≤ X ω ^ 2} := by
    intro ω hω
    have hpow := pow_le_pow_left₀ ht.le hω 2
    have habs : |X ω| ^ 2 = X ω ^ 2 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    simpa only [Set.mem_setOf_eq, habs] using hpow
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (f := fun ω => X ω ^ 2) (ae_of_all _ fun ω => by positivity) hX (t ^ 2)
  have hle := measureReal_mono (μ := μ) hsub
  have ht2 : 0 < t ^ 2 := pow_pos ht _
  have hbound : t ^ 2 * μ.real {ω | t ≤ |X ω|} ≤
      ∫ ω, X ω ^ 2 ∂μ :=
    (mul_le_mul_of_nonneg_left hle ht2.le).trans hmarkov
  exact (le_div_iff₀ ht2).2 (by simpa only [mul_comm] using hbound)

/-- Split a half-sized fluctuation into a fourth-moment principal part and
a second-moment remainder. -/
theorem measureReal_abs_add_ge_half_le_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : Ω → ℝ}
    (hA : Integrable (fun ω => A ω ^ 4) μ)
    (hB : Integrable (fun ω => B ω ^ 2) μ) :
    μ.real {ω | (1 / 2 : ℝ) ≤ |A ω + B ω|} ≤
      256 * (∫ ω, A ω ^ 4 ∂μ) +
        16 * (∫ ω, B ω ^ 2 ∂μ) := by
  have hsub : {ω | (1 / 2 : ℝ) ≤ |A ω + B ω|} ⊆
      {ω | (1 / 4 : ℝ) ≤ |A ω|} ∪
        {ω | (1 / 4 : ℝ) ≤ |B ω|} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
    change (1 / 2 : ℝ) ≤ |A ω + B ω| at hω
    have htri := abs_add_le (A ω) (B ω)
    rcases hnot with ⟨ha, hb⟩
    linarith
  have hAmarkov := measureReal_abs_ge_le_fourth hA
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hBmarkov := measureReal_abs_ge_le_second hB
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h := (measureReal_mono (μ := μ) hsub).trans
    (measureReal_union_le _ _)
  have h' := h.trans (add_le_add hAmarkov hBmarkov)
  calc
    μ.real {ω | (1 / 2 : ℝ) ≤ |A ω + B ω|} ≤
        (∫ ω, A ω ^ 4 ∂μ) / (1 / 4 : ℝ) ^ 4 +
          (∫ ω, B ω ^ 2 ∂μ) / (1 / 4 : ℝ) ^ 2 := h'
    _ = 256 * (∫ ω, A ω ^ 4 ∂μ) +
          16 * (∫ ω, B ω ^ 2 ∂μ) := by ring

theorem measureReal_lt_half_le_moments_of_ae_decomposition
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y A B : Ω → ℝ}
    (hdecomp : (fun ω => Y ω - 1) =ᵐ[μ] (fun ω => A ω + B ω))
    (hA : Integrable (fun ω => A ω ^ 4) μ)
    (hB : Integrable (fun ω => B ω ^ 2) μ) :
    μ.real {ω | Y ω < (1 / 2 : ℝ)} ≤
      256 * (∫ ω, A ω ^ 4 ∂μ) +
        16 * (∫ ω, B ω ^ 2 ∂μ) := by
  have hsub : {ω | Y ω < (1 / 2 : ℝ)} ⊆
      {ω | (1 / 2 : ℝ) ≤ |Y ω - 1|} := by
    intro ω hω
    change Y ω < (1 / 2 : ℝ) at hω
    change (1 / 2 : ℝ) ≤ |Y ω - 1|
    rw [abs_of_neg (by linarith : Y ω - 1 < 0)]
    linarith
  have hsets : {ω | (1 / 2 : ℝ) ≤ |Y ω - 1|} =ᵐ[μ]
      {ω | (1 / 2 : ℝ) ≤ |A ω + B ω|} :=
    hdecomp.mono (by
      intro ω hω
      change ((1 / 2 : ℝ) ≤ |Y ω - 1|) =
        ((1 / 2 : ℝ) ≤ |A ω + B ω|)
      rw [show Y ω - 1 = A ω + B ω by simpa using hω])
  calc
    μ.real {ω | Y ω < (1 / 2 : ℝ)} ≤
        μ.real {ω | (1 / 2 : ℝ) ≤ |Y ω - 1|} := measureReal_mono hsub
    _ = μ.real {ω | (1 / 2 : ℝ) ≤ |A ω + B ω|} := measureReal_congr hsets
    _ ≤ _ := measureReal_abs_add_ge_half_le_moments hA hB

/-- The model's exact chaos decomposition, expressed almost everywhere as
a quadratic Gaussian sum plus the higher-chaos remainder. -/
theorem Setting.Y_minus_one_ae_quadratic_remainder {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    (fun g : InteractionIndex (S.N n) q → ℝ =>
      S.Y β n (WithLp.toLp 2 g) - 1) =ᵐ[
        gaussianCouplings (InteractionIndex (S.N n) q)]
      fun g =>
        (β * deriv (fun b => Real.log (S.meanZ b n)) β /
          Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) *
          ((Real.sqrt (Fintype.card (InteractionIndex (S.N n) q) : ℝ))⁻¹ *
            ∑ i : InteractionIndex (S.N n) q, centeredGaussianSquare (g i)) +
          (S.higherChaosRemainderLp β n) g := by
  classical
  let ι := InteractionIndex (S.N n) q
  let c := β * deriv (fun b => Real.log (S.meanZ b n)) β /
    Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))
  let C : Lp ℝ 2 (gaussianCouplings ι) :=
    Lp.const 2 (gaussianCouplings ι) (1 : ℝ)
  let Q := quadraticGaussianLp ι
  let R := S.higherChaosRemainderLp β n
  have hLp : S.YGaussianLp β n = C + c • Q + R := by
    dsimp [C, c, Q, R]
    rw [S.Y_decomposition, S.Y_secondChaos_eq_quadraticGaussianLp]
  have hY := S.YGaussianLp_ae β n
  have hC := Lp.coeFn_const (α := ι → ℝ) (μ := gaussianCouplings ι)
    (p := 2) (c := (1 : ℝ))
  have hQ := quadraticGaussianLp_ae (ι := ι)
  have hSmul := Lp.coeFn_smul c Q
  have hAdd₁ := Lp.coeFn_add C (c • Q)
  have hAdd₂ := Lp.coeFn_add (C + c • Q) R
  filter_upwards [hY, hC, hQ, hSmul, hAdd₁, hAdd₂]
    with g hgY hgC hgQ hgSmul hgAdd₁ hgAdd₂
  change C g = 1 at hgC
  change Q g = (Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
    ∑ i : ι, centeredGaussianSquare (g i) at hgQ
  change (c • Q) g = c * Q g at hgSmul
  change (C + c • Q) g = C g + (c • Q) g at hgAdd₁
  change (C + c • Q + R) g = (C + c • Q) g + R g at hgAdd₂
  change S.Y β n (WithLp.toLp 2 g) - 1 = _
  calc
    S.Y β n (WithLp.toLp 2 g) - 1 = (S.YGaussianLp β n) g - 1 := by rw [hgY]
    _ = (C + c • Q + R) g - 1 := by rw [hLp]
    _ = c * ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
          ∑ i : ι, centeredGaussianSquare (g i)) + R g := by
            rw [hgAdd₂, hgAdd₁, hgC, hgSmul, hgQ]
            ring
    _ = _ := rfl

/-- Finite-size lower-tail estimate from the fourth moment of the quadratic
Gaussian term and the `L²` higher-chaos remainder. -/
theorem Setting.Y_pi_lt_half_le_moments {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    (gaussianCouplings (InteractionIndex (S.N n) q)).real
      {g | S.Y β n (WithLp.toLp 2 g) < (1 / 2 : ℝ)} ≤
      3840 *
        (β * deriv (fun b => Real.log (S.meanZ b n)) β /
          Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) ^ 4 +
        16 * ‖S.higherChaosRemainderLp β n‖ ^ 2 := by
  classical
  let ι := InteractionIndex (S.N n) q
  let μ := gaussianCouplings ι
  let c := β * deriv (fun b => Real.log (S.meanZ b n)) β /
    Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))
  let Q : (ι → ℝ) → ℝ := fun g =>
    (Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
      ∑ i : ι, centeredGaussianSquare (g i)
  let A : (ι → ℝ) → ℝ := fun g => c * Q g
  let R := S.higherChaosRemainderLp β n
  let B : (ι → ℝ) → ℝ := fun g => R g
  have hcard : 0 < Fintype.card ι := by
    simpa [ι, InteractionIndex] using Nat.choose_pos (S.q_le_N n)
  have hQ4 : (∫ g, Q g ^ 4 ∂μ) ≤ 15 := by
    simpa [Q, μ] using
      normalizedGaussianSquares_fourth_moment_le (ι := ι) hcard
  have hQmem : MemLp Q 4 μ := by
    have h := centeredGaussianSquares_sum_memLp_four (ι := ι)
    simpa [Q, μ] using h.const_mul
      (Real.sqrt (Fintype.card ι : ℝ))⁻¹
  have hAmem : MemLp A 4 μ := by
    simpa [A] using hQmem.const_mul c
  have hA4 : Integrable (fun g => A g ^ 4) μ := by
    have h := hAmem.integrable_norm_pow (by decide : 4 ≠ 0)
    convert h using 1
    funext g
    rw [Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by nlinarith [sq_nonneg (A g ^ 2)])]
  have hB2 : Integrable (fun g => B g ^ 2) μ := by
    have h := Lp.memLp R
    simpa [B, μ] using (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
  have hAeq : (∫ g, A g ^ 4 ∂μ) = c ^ 4 * (∫ g, Q g ^ 4 ∂μ) := by
    simp only [A, mul_pow, integral_const_mul]
  have hAle : (∫ g, A g ^ 4 ∂μ) ≤ 15 * c ^ 4 := by
    rw [hAeq]
    calc
      c ^ 4 * (∫ g, Q g ^ 4 ∂μ) ≤ c ^ 4 * 15 :=
        mul_le_mul_of_nonneg_left hQ4 (by positivity)
      _ = 15 * c ^ 4 := by ring
  have hBeq : (∫ g, B g ^ 2 ∂μ) = ‖R‖ ^ 2 := by
    simpa [B, μ] using integral_Lp_sq_eq_norm_sq R
  have hdecomp :
      (fun g : ι → ℝ => S.Y β n (WithLp.toLp 2 g) - 1) =ᵐ[μ]
        (fun g => A g + B g) := by
    simpa [A, B, Q, c, R, μ, ι] using
      S.Y_minus_one_ae_quadratic_remainder β n
  have htail := measureReal_lt_half_le_moments_of_ae_decomposition
    hdecomp hA4 hB2
  calc
    μ.real {g | S.Y β n (WithLp.toLp 2 g) < (1 / 2 : ℝ)} ≤
        256 * (∫ g, A g ^ 4 ∂μ) +
          16 * (∫ g, B g ^ 2 ∂μ) := htail
    _ ≤ 3840 * c ^ 4 + 16 * ‖R‖ ^ 2 := by
      rw [hBeq]
      nlinarith [mul_le_mul_of_nonneg_left hAle (by norm_num : (0 : ℝ) ≤ 256)]
    _ = _ := rfl

/-- The finite-size small-`Y` estimate on the measure used by the CLT theorem. -/
theorem Setting.Y_lt_half_le_moments {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    (standardGaussianMeasure (S.N n) q).real
      {g | S.Y β n g < (1 / 2 : ℝ)} ≤
      3840 *
        (β * deriv (fun b => Real.log (S.meanZ b n)) β /
          Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) ^ 4 +
        16 * ‖S.higherChaosRemainderLp β n‖ ^ 2 := by
  let ι := InteractionIndex (S.N n) q
  have hYcont : Continuous (S.Y β n) := by
    unfold Setting.Y Setting.Z
    exact (realPartitionFunction_continuous (S.params n) (S.majorana n) β).div_const _
  have hset : MeasurableSet {g : CouplingSpace (S.N n) q |
      S.Y β n g < (1 / 2 : ℝ)} :=
    hYcont.measurable measurableSet_Iio
  change ((gaussianCouplings ι).map
    (MeasurableEquiv.toLp 2 (ι → ℝ))).real
      {g | S.Y β n g < (1 / 2 : ℝ)} ≤ _
  rw [map_measureReal_apply (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable hset]
  simpa [ι, Set.preimage] using S.Y_pi_lt_half_le_moments β n

end SYK.CLT
