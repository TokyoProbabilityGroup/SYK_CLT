import SYK.CLT.Chaos.HigherChaosProjection
import SYK.Probability.GaussianChaos.PolynomialDensity

/-!
# The higher-chaos remainder in Gaussian L²

The degree projections are pairwise orthogonal. Their convergent tail gives
an exact L² remainder whose norm squared is the sum bounded in `HigherChaosProjection`.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology InnerProductSpace

open SYK.GaussianChaos

namespace SYK.CLT
/-- Distinct homogeneous Hermite chaoses are orthogonal in Gaussian L². -/
theorem inner_hermiteDegreeProjection_eq_zero {ι : Type*} [Fintype ι]
    (r s : ℕ) (hrs : r ≠ s)
    (f g : Lp ℝ 2 (gaussianCouplings ι)) :
    ⟪hermiteDegreeProjection r f, hermiteDegreeProjection s g⟫_ℝ = 0 := by
  classical
  simp only [hermiteDegreeProjection, hermiteFiniteProjection,
    inner_sum, sum_inner, real_inner_smul_left, inner_smul_right]
  apply Finset.sum_eq_zero
  intro α hα
  suffices hinner :
      (∑ γ ∈ multiIndices_degree r,
        (⟪hermiteLp γ, f⟫_ℝ / ∏ i, ((γ i).factorial : ℝ)) *
          ⟪hermiteLp γ, hermiteLp α⟫_ℝ) = 0 by
    rw [hinner, mul_zero]
  apply Finset.sum_eq_zero
  intro γ hγ
  have hne : γ ≠ α := by
    intro heq
    have hγr := (mem_multiIndices_degree r γ).mp hγ
    have hαs := (mem_multiIndices_degree s α).mp hα
    exact hrs (hγr.symm.trans (heq ▸ hαs))
  rw [inner_hermiteLp, if_neg hne]
  ring

private theorem norm_sum_range_sq_of_pairwise_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (m : ℕ) :
    ‖∑ k ∈ Finset.range m, v k‖ ^ 2 =
      ∑ k ∈ Finset.range m, ‖v k‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Finset.sum_range_succ]
      have hinner : ⟪∑ k ∈ Finset.range m, v k, v m⟫_ℝ = 0 := by
        rw [sum_inner]
        apply Finset.sum_eq_zero
        intro k hk
        exact horth k m (by exact ne_of_lt (Finset.mem_range.mp hk))
      rw [norm_add_sq_real, hinner, mul_zero, add_zero, ih]

private theorem norm_sq_eq_tsum_of_pairwise_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (z : E) (hz : HasSum v z) :
    ‖z‖ ^ 2 = ∑' k : ℕ, ‖v k‖ ^ 2 := by
  have hpartial : Tendsto (fun m => ‖∑ k ∈ Finset.range m, v k‖ ^ 2)
      atTop (𝓝 (‖z‖ ^ 2)) := (hz.tendsto_sum_nat.norm).pow 2
  have hreal : Tendsto (fun m => ∑ k ∈ Finset.range m, ‖v k‖ ^ 2)
      atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa only [norm_sum_range_sq_of_pairwise_orthogonal v horth] using hpartial
  have hsum : HasSum (fun k : ℕ => ‖v k‖ ^ 2) (‖z‖ ^ 2) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun k => sq_nonneg _) _).2 hreal
  exact hsum.tsum_eq.symm

/-- The Gaussian L² sum of Hermite chaoses of degree at least three. -/
noncomputable def Setting.higherChaosRemainderLp {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    Lp ℝ 2 (gaussianCouplings (InteractionIndex (S.N n) q)) :=
  S.YGaussianLp β n -
    ∑ r ∈ Finset.range 3, hermiteDegreeProjection r (S.YGaussianLp β n)

/-- Parseval identity for the higher-chaos remainder. -/
theorem Setting.higherChaosRemainderLp_norm_sq {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) :
    ‖S.higherChaosRemainderLp β n‖ ^ 2 =
      ∑' k : ℕ,
        ‖hermiteDegreeProjection (k + 3) (S.YGaussianLp β n)‖ ^ 2 := by
  let f := S.YGaussianLp β n
  let v : ℕ → Lp ℝ 2 (gaussianCouplings (InteractionIndex (S.N n) q)) :=
    fun k => hermiteDegreeProjection (k + 3) f
  have horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0 := by
    intro i j hij
    exact inner_hermiteDegreeProjection_eq_zero (i + 3) (j + 3)
      (by omega) f f
  have hsum : HasSum v (S.higherChaosRemainderLp β n) := by
    exact (hasSum_nat_add_iff' 3).mpr (hasSum_hermiteDegreeProjection_unconditional f)
  exact norm_sq_eq_tsum_of_pairwise_orthogonal v horth _ hsum

/-- Uniform high-temperature `L²` bound for the actual remainder. -/
theorem Setting.higherChaosRemainderLp_le_power {q : ℕ} (S : Setting q) :
    ∃ βq : ℝ, 0 < βq ∧ ∃ C : ℝ,
      ∀ β : ℝ, |β| < βq → ∀ n : ℕ,
        ‖S.higherChaosRemainderLp β n‖ ^ 2 ≤
          C * (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1)) := by
  obtain ⟨βq, hβq, C, hbound⟩ := S.tsum_higherChaosProjection_le_power
  refine ⟨βq, hβq, C, ?_⟩
  intro β hβ n
  rw [S.higherChaosRemainderLp_norm_sq]
  exact hbound β hβ n

/-- The remainder norm squared is little-o of the second-chaos variance scale. -/
theorem Setting.higherChaosRemainderLp_isLittleO {q : ℕ} (S : Setting q) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      (fun n => ‖S.higherChaosRemainderLp β n‖ ^ 2) =o[atTop]
        (fun n => (S.N n : ℝ) ^ (2 - (q : ℝ))) := by
  obtain ⟨βq, hβq, hbound⟩ := S.higherChaosProjection_isLittleO
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  simpa only [S.higherChaosRemainderLp_norm_sq] using hbound β hβ

private theorem fluctuationScale_sq_eq_inverse_rpow {q : ℕ}
    (S : Setting q) (n : ℕ) :
    S.fluctuationScale n ^ 2 =
      ((S.N n : ℝ) ^ (2 - (q : ℝ)))⁻¹ := by
  have hN : (0 : ℝ) < (S.N n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
  have he : (q / 2 - 1) * 2 = q - 2 := by
    obtain ⟨k, hk⟩ := S.q_even
    omega
  have hcast : ((q - 2 : ℕ) : ℝ) = (q : ℝ) - 2 := by
    rw [Nat.cast_sub (le_trans (by decide : 2 ≤ 4) S.q_ge_four)]
    norm_num
  calc
    S.fluctuationScale n ^ 2 =
        (S.N n : ℝ) ^ ((q / 2 - 1) * 2) := by
      rw [Setting.fluctuationScale, pow_mul]
    _ = (S.N n : ℝ) ^ (q - 2) := by rw [he]
    _ = ((S.N n : ℝ) ^ (2 - (q : ℝ)))⁻¹ := by
      rw [← Real.rpow_natCast, hcast,
        show 2 - (q : ℝ) = -((q : ℝ) - 2) by ring,
        Real.rpow_neg hN.le]
      simp

/-- At high temperature, the scaled higher-chaos remainder vanishes in `L²`. -/
theorem Setting.scaled_higherChaosRemainderLp_norm_tendsto_zero {q : ℕ}
    (S : Setting q) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      Tendsto (fun n => ‖S.fluctuationScale n • S.higherChaosRemainderLp β n‖)
        atTop (𝓝 0) := by
  obtain ⟨βq, hβq, htail⟩ := S.higherChaosRemainderLp_isLittleO
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  have hratio := (htail β hβ).tendsto_div_nhds_zero
  have heq (n : ℕ) :
      ‖S.fluctuationScale n • S.higherChaosRemainderLp β n‖ ^ 2 =
        ‖S.higherChaosRemainderLp β n‖ ^ 2 /
          (S.N n : ℝ) ^ (2 - (q : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
    · rw [mul_pow, fluctuationScale_sq_eq_inverse_rpow S n]
      ring
    · unfold Setting.fluctuationScale
      positivity
  have hsq : Tendsto (fun n =>
      ‖S.fluctuationScale n • S.higherChaosRemainderLp β n‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [heq] using hratio
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

end SYK.CLT
