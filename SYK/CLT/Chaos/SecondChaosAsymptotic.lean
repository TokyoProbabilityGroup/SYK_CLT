import SYK.CLT.Chaos.SecondChaos
import Mathlib.Analysis.SpecialFunctions.Choose

open Filter Asymptotics
open scoped Topology

namespace SYK.CLT

/-- Fixed-order binomial coefficients are asymptotic to N^q/q!. -/
theorem Setting.choose_ratio_tendsto {q : ℕ} (S : Setting q) :
    Tendsto (fun n => (Nat.choose (S.N n) q : ℝ) /
      ((S.N n : ℝ) ^ q / (q.factorial : ℝ))) atTop (𝓝 1) := by
  have hequiv := (isEquivalent_choose q).comp_tendsto S.N_tendsto
  have hnonzero : ∀ᶠ n : ℕ in atTop,
      (S.N n : ℝ) ^ q / (q.factorial : ℝ) ≠ 0 := by
    apply Filter.Eventually.of_forall
    intro n
    have hN : (0 : ℝ) < (S.N n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
    exact ne_of_gt (div_pos (pow_pos hN _) (by positivity))
  exact (isEquivalent_iff_tendsto_one hnonzero).1 hequiv

theorem Setting.inverse_choose_ratio_tendsto {q : ℕ} (S : Setting q) :
    Tendsto (fun n => (S.N n : ℝ) ^ q /
      (2 * (Nat.choose (S.N n) q : ℝ))) atTop
      (𝓝 ((q.factorial : ℝ) / 2)) := by
  have h := (S.choose_ratio_tendsto).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h' : Tendsto (fun n => (q.factorial : ℝ) / 2 *
      ((Nat.choose (S.N n) q : ℝ) /
        ((S.N n : ℝ) ^ q / (q.factorial : ℝ)))⁻¹) atTop
        (𝓝 ((q.factorial : ℝ) / 2)) := by
    simpa using h.const_mul ((q.factorial : ℝ) / 2)
  apply h'.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hN : (0 : ℝ) < (S.N n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
  have hchoose : (0 : ℝ) < (Nat.choose (S.N n) q : ℝ) := by
    exact_mod_cast Nat.choose_pos (S.q_le_N n)
  dsimp
  field_simp

theorem Setting.normalized_choose_factor_tendsto {q : ℕ} (S : Setting q) :
    Tendsto (fun n => (S.N n : ℝ) ^ (q / 2) /
      Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))) atTop
      (𝓝 (Real.sqrt ((q.factorial : ℝ) / 2))) := by
  have h := (S.inverse_choose_ratio_tendsto).sqrt
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hN : (0 : ℝ) < (S.N n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
  have hpow : (S.N n : ℝ) ^ q = ((S.N n : ℝ) ^ (q / 2)) ^ 2 := by
    obtain ⟨k, hk⟩ := S.q_even
    have hq : q = 2 * k := by omega
    have he : q = (q / 2) * 2 := by omega
    calc
      _ = (S.N n : ℝ) ^ ((q / 2) * 2) := congrArg _ he
      _ = _ := pow_mul _ _ _
  dsimp
  rw [hpow, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (by positivity)]

/-- The scaled exact second-chaos coefficient has the manuscript limit. -/
theorem Setting.secondChaosScaledCoefficient_tendsto {q : ℕ} (S : Setting q)
    (hFE : AnnealedInput q S) (β : ℝ) :
    Tendsto (fun n => S.fluctuationScale n *
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))) atTop
      (𝓝 (β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2))) := by
  have hcoeff := secondChaosCoefficient_tendsto hFE β
  have hcount := S.normalized_choose_factor_tendsto
  have hprod := (hcoeff.mul hcount).const_mul (2 : ℝ)
  convert hprod using 1
  · ext n
    have hN : (0 : ℝ) < (S.N n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (S.q_ge_four.trans (S.q_le_N n))
    have hq : 1 ≤ q / 2 := by
      have h : 4 ≤ q := S.q_ge_four
      omega
    have hpow : (S.N n : ℝ) ^ (q / 2) =
        (S.N n : ℝ) ^ (q / 2 - 1) * (S.N n : ℝ) := by
      conv_lhs => rw [← Nat.sub_add_cancel hq]
      rw [pow_succ]
    rw [Setting.fluctuationScale]
    rw [hpow]
    field_simp
  · ring_nf

/-- The number of q-body interactions diverges along the system-size family. -/
theorem Setting.interactionCard_tendsto {q : ℕ} (S : Setting q) :
    Tendsto (fun n => Fintype.card (InteractionIndex (S.N n) q)) atTop atTop := by
  have hN : Tendsto (fun n => (S.N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp S.N_tendsto
  have hq : (0 : ℝ) < q := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) S.q_ge_four
  have hpow : Tendsto (fun n => (S.N n : ℝ) ^ q) atTop atTop := by
    simpa only [Function.comp_def, Real.rpow_natCast] using (tendsto_rpow_atTop hq).comp hN
  have hdiv : Tendsto (fun n => (S.N n : ℝ) ^ q / (q.factorial : ℝ))
      atTop atTop := Tendsto.atTop_div_const (by positivity) hpow
  have hchoose : Tendsto (fun n => (Nat.choose (S.N n) q : ℝ)) atTop atTop :=
    ((isEquivalent_choose q).comp_tendsto S.N_tendsto).tendsto_atTop_iff.mpr hdiv
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  simpa [InteractionIndex] using hchoose

end SYK.CLT
