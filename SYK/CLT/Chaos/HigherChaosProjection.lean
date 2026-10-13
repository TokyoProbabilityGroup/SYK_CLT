module

public import SYK.CLT.Chaos.Rademacher
public import SYK.CLT.Chaos.PartitionSymmetry
import SYK.CLT.Chaos.PartitionHigherDerivatives

public section

/-!
# Higher-chaos projection bounds

Hermite orthogonality, the all-order partition derivative estimate, and the
Rademacher counting identity bound each homogeneous projection and its
infinite tail. Entry points: `Setting.norm_sq_hermiteDegreeProjection_le_rademacher_moment`
and `Setting.tsum_higherChaosProjection_le_exp_moment`. Inside the high-temperature radius,
`Setting.tsum_higherChaosProjection_le_power` and `Setting.higherChaosProjection_isLittleO`
give the power bound and the little-o statement of `prop:higher-chaos-closure`.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology InnerProductSpace

open SYK.GaussianChaos

namespace SYK.CLT

/-- A finite exponential-series tail bound used when summing the higher
homogeneous chaoses. -/
private theorem exp_tail_range_le (u : ℝ) (hu : 0 ≤ u) (m : ℕ) :
    (∑ k ∈ Finset.range m, u ^ (k + 3) / ((k + 3).factorial : ℝ)) ≤
      u ^ 3 / 6 * Real.exp u := by
  calc
    _ ≤ ∑ k ∈ Finset.range m, (u ^ 3 / 6) *
        (u ^ k / (k.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _
      have hfacNat : k.factorial * (3).factorial ≤ (k + 3).factorial :=
        Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add k 3)
      norm_num at hfacNat
      have hfac : (6 : ℝ) * (k.factorial : ℝ) ≤ ((k + 3).factorial : ℝ) := by
        exact_mod_cast (by simpa [mul_comm] using hfacNat)
      calc
        u ^ (k + 3) / ((k + 3).factorial : ℝ) ≤
            u ^ (k + 3) / (6 * (k.factorial : ℝ)) := by gcongr
        _ = (u ^ 3 / 6) * (u ^ k / (k.factorial : ℝ)) := by
          rw [show k + 3 = 3 + k by omega, pow_add]
          ring
    _ = u ^ 3 / 6 * ∑ k ∈ Finset.range m, u ^ k / (k.factorial : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hu m) (by positivity)

private theorem Setting.inner_hermiteLp_YGaussianLp_eq_zero_of_odd
    {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (α : InteractionIndex (S.N n) q → ℕ) (hα : IsOddMultiIndex α) :
    ⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ = 0 := by
  rw [Setting.YGaussianLp, inner_smul_right,
    S.inner_hermiteLp_ZGaussianLp_eq_zero β n α hα, mul_zero]

open scoped Classical in
theorem Setting.norm_sq_hermiteDegreeProjection_le_even_sum
    {q : ℕ} (S : Setting q) (β : ℝ) (n r : ℕ) :
    ‖hermiteDegreeProjection r (S.YGaussianLp β n)‖ ^ 2 ≤
      (β ^ 2 * couplingScale (S.params n) ^ 2) ^ r *
        ∑ α ∈ (multiIndicesOfDegree
          (ι := InteractionIndex (S.N n) q) r).filter IsEvenMultiIndex,
          (∏ I : InteractionIndex (S.N n) q, ((α I).factorial : ℝ))⁻¹ := by
  classical
  rw [norm_sq_hermiteDegreeProjection]
  let s := multiIndicesOfDegree (ι := InteractionIndex (S.N n) q) r
  have hrestrict :
      (∑ α ∈ s, |⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ| ^ 2 /
          ∏ I, ((α I).factorial : ℝ)) =
        ∑ α ∈ s.filter IsEvenMultiIndex,
          |⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ| ^ 2 /
            ∏ I, ((α I).factorial : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro α hαs hαfilter
    have hodd : IsOddMultiIndex α := by
      change ¬ IsEvenMultiIndex α
      simpa only [Finset.mem_filter, hαs, true_and] using hαfilter
    rw [S.inner_hermiteLp_YGaussianLp_eq_zero_of_odd β n α hodd]
    simp
  rw [hrestrict, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α hα
  have hdegree : ∑ I, α I = r := by
    have hs : α ∈ multiIndicesOfDegree r := (Finset.mem_filter.mp hα).1
    exact (mem_multiIndicesOfDegree r α).mp hs
  have hcoeff := S.abs_inner_hermiteLp_YGaussianLp_le β n α
  rw [hdegree] at hcoeff
  have hnum : |⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ| ^ 2 ≤
      (β ^ 2 * couplingScale (S.params n) ^ 2) ^ r := by
    calc
      _ ≤ ((|β| * couplingScale (S.params n)) ^ r) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcoeff 2
      _ = _ := by
        rw [pow_two, ← mul_pow, ← sq_abs]
        ring
  have hfac : 0 ≤ ∏ I : InteractionIndex (S.N n) q,
      ((α I).factorial : ℝ) := (hermiteFactorial_pos α).le
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hfac)

/-- The degree-`r` projection is controlled by the `r`-th Rademacher chaos moment.
This combines the Gaussian Hermite coefficient estimate with
`eq:even-sum-Rademacher-moment`. -/
theorem Setting.norm_sq_hermiteDegreeProjection_le_rademacher_moment
    {q : ℕ} (S : Setting q) (β : ℝ) (n r : ℕ) :
    ‖hermiteDegreeProjection r (S.YGaussianLp β n)‖ ^ 2 ≤
      ((β ^ 2 * couplingScale (S.params n) ^ 2) ^ r /
        (r.factorial : ℝ)) *
        Rademacher.radE (S.N n)
          (fun ε => Rademacher.chaos (S.N n) q ε ^ r) := by
  have h := S.norm_sq_hermiteDegreeProjection_le_even_sum β n r
  rw [Rademacher.even_sum_rademacher_moment] at h
  simpa only [div_eq_mul_inv, mul_assoc] using h

/-- A finite higher-chaos tail is bounded by the exponential third moment of
the Rademacher chaos, as in `eq:all-higher-chaoses-at-once`. -/
theorem Setting.sum_higherChaosProjection_le_exp_moment
    {q : ℕ} (S : Setting q) (β : ℝ) (n m : ℕ) :
    (∑ k ∈ Finset.range m,
      ‖hermiteDegreeProjection (k + 3) (S.YGaussianLp β n)‖ ^ 2) ≤
      ((β ^ 2 * couplingScale (S.params n) ^ 2) ^ 3 / 6) *
        Rademacher.radE (S.N n) (fun ε =>
          |Rademacher.chaos (S.N n) q ε| ^ 3 *
            Real.exp ((β ^ 2 * couplingScale (S.params n) ^ 2) *
              |Rademacher.chaos (S.N n) q ε|)) := by
  let t := β ^ 2 * couplingScale (S.params n) ^ 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  change (∑ k ∈ Finset.range m,
      ‖hermiteDegreeProjection (k + 3) (S.YGaussianLp β n)‖ ^ 2) ≤
    t ^ 3 / 6 * Rademacher.radE (S.N n) (fun ε =>
      |Rademacher.chaos (S.N n) q ε| ^ 3 *
        Real.exp (t * |Rademacher.chaos (S.N n) q ε|))
  calc
    _ ≤ ∑ k ∈ Finset.range m, Rademacher.radE (S.N n) (fun ε =>
        (t * |Rademacher.chaos (S.N n) q ε|) ^ (k + 3) /
          ((k + 3).factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _
      have h := S.norm_sq_hermiteDegreeProjection_le_rademacher_moment β n (k + 3)
      have hmono :
          Rademacher.radE (S.N n) (fun ε => Rademacher.chaos (S.N n) q ε ^ (k + 3)) ≤
            Rademacher.radE (S.N n) (fun ε =>
              |Rademacher.chaos (S.N n) q ε| ^ (k + 3)) := by
        apply Rademacher.radE_mono
        intro ε
        exact (le_abs_self _).trans_eq (abs_pow _ _)
      calc
        _ ≤ (t ^ (k + 3) / (k + 3).factorial) *
            Rademacher.radE (S.N n)
              (fun ε => Rademacher.chaos (S.N n) q ε ^ (k + 3)) := h
        _ ≤ (t ^ (k + 3) / (k + 3).factorial) *
            Rademacher.radE (S.N n)
              (fun ε => |Rademacher.chaos (S.N n) q ε| ^ (k + 3)) := by
            exact mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = _ := by
            rw [← Rademacher.radE_const_mul]
            congr 1
            funext ε
            rw [mul_pow]
            ring
    _ = Rademacher.radE (S.N n) (fun ε =>
          ∑ k ∈ Finset.range m,
            (t * |Rademacher.chaos (S.N n) q ε|) ^ (k + 3) /
              ((k + 3).factorial : ℝ)) := by
          rw [Rademacher.radE_sum]
    _ ≤ Rademacher.radE (S.N n) (fun ε =>
          t ^ 3 / 6 * (|Rademacher.chaos (S.N n) q ε| ^ 3 *
            Real.exp (t * |Rademacher.chaos (S.N n) q ε|))) := by
          apply Rademacher.radE_mono
          intro ε
          have hb := exp_tail_range_le
            (t * |Rademacher.chaos (S.N n) q ε|)
            (mul_nonneg ht (abs_nonneg _)) m
          convert hb using 1
          ring
    _ = _ := by rw [Rademacher.radE_const_mul]

/-- The complete higher-degree projection norm sum obeys the same bound as
every finite partial sum. -/
theorem Setting.tsum_higherChaosProjection_le_exp_moment
    {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    (∑' k : ℕ,
      ‖hermiteDegreeProjection (k + 3) (S.YGaussianLp β n)‖ ^ 2) ≤
      ((β ^ 2 * couplingScale (S.params n) ^ 2) ^ 3 / 6) *
        Rademacher.radE (S.N n) (fun ε =>
          |Rademacher.chaos (S.N n) q ε| ^ 3 *
            Real.exp ((β ^ 2 * couplingScale (S.params n) ^ 2) *
              |Rademacher.chaos (S.N n) q ε|)) := by
  apply Real.tsum_le_of_sum_range_le
  · intro k
    positivity
  · intro m
    exact S.sum_higherChaosProjection_le_exp_moment β n m

private theorem high_temp_parameter_bound {q : ℕ} (S : Setting q)
    (c : ℝ) (hc : 0 < c) (β : ℝ) (n : ℕ)
    (hβ : |β| < Real.sqrt (c / ((q - 1).factorial : ℝ))) :
    β ^ 2 * couplingScale (S.params n) ^ 2 ≤
      c * (S.N n : ℝ) ^ (-((q : ℝ) - 1)) := by
  have hA : (0 : ℝ) < ((q - 1).factorial : ℝ) := by positivity
  have hx : (0 : ℝ) < (S.N n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
  have hβsq : β ^ 2 < c / ((q - 1).factorial : ℝ) := by
    have h := (sq_lt_sq₀ (abs_nonneg β)
      (Real.sqrt_nonneg (c / ((q - 1).factorial : ℝ)))).mpr hβ
    rwa [sq_abs, Real.sq_sqrt (div_nonneg hc.le hA.le)] at h
  have hβA : β ^ 2 * ((q - 1).factorial : ℝ) ≤ c := by
    exact (lt_div_iff₀ hA).mp hβsq |>.le
  have he : ((q : ℝ) - 1) = ((q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 4) S.q_ge_four)]
    simp
  calc
    β ^ 2 * couplingScale (S.params n) ^ 2 =
        β ^ 2 * (((q - 1).factorial : ℝ) / (S.N n : ℝ) ^ (q - 1)) := by
          rw [couplingScale_sq]
          rfl
    _ ≤ c / (S.N n : ℝ) ^ (q - 1) := by
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right hβA (by positivity)
    _ = c * (S.N n : ℝ) ^ (-((q : ℝ) - 1)) := by
          rw [he, Real.rpow_neg hx.le, Real.rpow_natCast]
          ring

/-- Algebraic form of the higher-chaos decay exponent. -/
private theorem rate_power_identity (x : ℝ) (hx : 0 < x) (q : ℕ) :
    (x ^ (-((q : ℝ) - 1))) ^ 3 * x ^ ((3 * q : ℝ) / 2) =
      x ^ (-3 * ((q : ℝ) / 2 - 1)) := by
  rw [← Real.rpow_natCast (x ^ (-((q : ℝ) - 1))) 3]
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

/-- Uniform high-temperature bound for the sum of all Hermite degrees at least three. -/
theorem Setting.tsum_higherChaosProjection_le_power {q : ℕ} (S : Setting q) :
    ∃ βq : ℝ, 0 < βq ∧ ∃ C : ℝ,
      ∀ β : ℝ, |β| < βq → ∀ n : ℕ,
      (∑' k : ℕ,
        ‖hermiteDegreeProjection (k + 3) (S.YGaussianLp β n)‖ ^ 2) ≤
        C * (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1)) := by
  obtain ⟨c, hc, C₀, hmoment⟩ :=
    Rademacher.rademacher_encoding q S.q_ge_four S.q_even
  have hfac : (0 : ℝ) < ((q - 1).factorial : ℝ) := by positivity
  refine ⟨Real.sqrt (c / ((q - 1).factorial : ℝ)),
    Real.sqrt_pos.2 (div_pos hc hfac), c ^ 3 / 6 * C₀, ?_⟩
  intro β hβ n
  let x : ℝ := S.N n
  let t : ℝ := β ^ 2 * couplingScale (S.params n) ^ 2
  let M : ℝ := Rademacher.radE (S.N n) (fun ε =>
    |Rademacher.chaos (S.N n) q ε| ^ 3 *
      Real.exp (t * |Rademacher.chaos (S.N n) q ε|))
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htbound : t ≤ c * x ^ (-((q : ℝ) - 1)) :=
    high_temp_parameter_bound S c hc β n hβ
  have hM : M ≤ C₀ * x ^ ((3 * q : ℝ) / 2) :=
    hmoment (S.N n) t ht htbound
  have hM0 : 0 ≤ M := by
    dsimp [M, Rademacher.radE]
    positivity
  have hCM : 0 ≤ C₀ * x ^ ((3 * q : ℝ) / 2) := hM0.trans hM
  calc
    _ ≤ t ^ 3 / 6 * M := S.tsum_higherChaosProjection_le_exp_moment β n
    _ ≤ t ^ 3 / 6 * (C₀ * x ^ ((3 * q : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ (c * x ^ (-((q : ℝ) - 1))) ^ 3 / 6 *
        (C₀ * x ^ ((3 * q : ℝ) / 2)) := by
      gcongr
    _ = _ := by
      rw [mul_pow]
      change c ^ 3 * (x ^ (-((q : ℝ) - 1))) ^ 3 / 6 *
          (C₀ * x ^ ((3 * q : ℝ) / 2)) =
        c ^ 3 / 6 * C₀ * x ^ (-3 * ((q : ℝ) / 2 - 1))
      calc
        _ = c ^ 3 / 6 * C₀ *
            ((x ^ (-((q : ℝ) - 1))) ^ 3 * x ^ ((3 * q : ℝ) / 2)) := by ring
        _ = _ := by rw [rate_power_identity x hx q]

private theorem rate_little_o {q : ℕ} (S : Setting q) (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (C : ℝ)
    (hbound : ∀ n, F n ≤ C * (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1))) :
    F =o[atTop] (fun n => (S.N n : ℝ) ^ (2 - (q : ℝ))) := by
  have hq : 0 < (q : ℝ) / 2 - 1 := by
    have h : (4 : ℝ) ≤ q := by exact_mod_cast S.q_ge_four
    linarith
  have hN : Tendsto (fun n => (S.N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp S.N_tendsto
  have hpower : Tendsto (fun n => (S.N n : ℝ) ^ (-((q : ℝ) / 2 - 1)))
      atTop (𝓝 0) := (tendsto_rpow_neg_atTop hq).comp hN
  have hx (n : ℕ) : (0 : ℝ) < (S.N n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
  have hratio (n : ℕ) :
      (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1)) /
          (S.N n : ℝ) ^ (2 - (q : ℝ)) =
        (S.N n : ℝ) ^ (-((q : ℝ) / 2 - 1)) := by
    rw [← Real.rpow_sub (hx n)]
    congr 1
    ring
  apply (isLittleO_iff_tendsto (f := F)
    (g := fun n => (S.N n : ℝ) ^ (2 - (q : ℝ))) (by
      intro n hn
      exact False.elim ((Real.rpow_pos_of_pos (hx n) _).ne' hn))).2
  have hupper : Tendsto (fun n => C * (S.N n : ℝ) ^ (-((q : ℝ) / 2 - 1)))
      atTop (𝓝 0) := by simpa using hpower.const_mul C
  apply squeeze_zero (fun n => div_nonneg (hF n) (Real.rpow_nonneg (hx n).le _))
    (fun n => ?_) hupper
  calc
    F n / (S.N n : ℝ) ^ (2 - (q : ℝ)) ≤
        (C * (S.N n : ℝ) ^ (-3 * ((q : ℝ) / 2 - 1))) /
          (S.N n : ℝ) ^ (2 - (q : ℝ)) :=
      div_le_div_of_nonneg_right (hbound n) (Real.rpow_nonneg (hx n).le _)
    _ = C * (S.N n : ℝ) ^ (-((q : ℝ) / 2 - 1)) := by
      rw [mul_div_assoc, hratio]

/-- The higher-degree Hermite projection norm sum is negligible at the
second-chaos variance scale. -/
theorem Setting.higherChaosProjection_isLittleO {q : ℕ} (S : Setting q) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq →
      (fun n => ∑' k : ℕ,
        ‖hermiteDegreeProjection (k + 3) (S.YGaussianLp β n)‖ ^ 2) =o[atTop]
        (fun n => (S.N n : ℝ) ^ (2 - (q : ℝ))) := by
  obtain ⟨βq, hβq, C, hbound⟩ := S.tsum_higherChaosProjection_le_power
  refine ⟨βq, hβq, ?_⟩
  intro β hβ
  apply rate_little_o S _ (fun n => ?_) C (hbound β hβ)
  exact tsum_nonneg (fun k => by positivity)

end SYK.CLT
