import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.AbsMax

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace SYK
namespace CLT

/-!
Hilbert-valued analytic suppression for high chaos orders.

Each component has a zero whose order is at least its chaos order.  A boundary
second-moment bound therefore gains a geometric factor when evaluated on a
smaller disk.
-/

/-- Abstract analytic suppression estimate used above logarithmic chaos
order. -/
theorem analytic_suppression_high_components
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℕ → ℂ → H) (R C : ℝ) (m : ℕ) (w : ℂ)
    (hR : 0 < R) (hw : ‖w‖ < R) (hC : 0 ≤ C)
    (hfactor :
      ∀ r : ℕ, ∃ V : ℂ → H,
        AnalyticOnNhd ℂ V (Metric.closedBall 0 R) ∧
          ∀ z ∈ Metric.closedBall (0 : ℂ) R, G r z = z ^ r • V z)
    (hsummable :
      ∀ z : ℂ, ‖z‖ = R → Summable (fun r => ‖G r z‖ ^ 2))
    (hboundary :
      ∀ z : ℂ, ‖z‖ = R → ∑' r : ℕ, ‖G r z‖ ^ 2 ≤ C) :
    (∑' r : ℕ, if m < r then ‖G r w‖ ^ 2 else 0) ≤
      ((‖w‖ / R) ^ (2 * (m + 1)) /
        (1 - (‖w‖ / R) ^ 2)) * C := by
  -- For each r, obtain the decomposition G r z = z^r • V z
  choose V hV_analytic hV_factor using hfactor
  have hwR : ‖w‖ / R < 1 := by rwa [div_lt_one hR]
  have hwR_nn : 0 ≤ ‖w‖ / R := div_nonneg (norm_nonneg w) (le_of_lt hR)
  -- Pick a reference point on the boundary
  set z₀ : ℂ := (R : ℂ) with hz₀_def
  have hz₀ : ‖z₀‖ = R := by simp [hz₀_def, Complex.norm_real, abs_of_pos hR]
  -- Key bound: for any z on boundary, ‖G r z‖^2 ≤ ∑_s ‖G s z‖^2 ≤ C
  have hsingle_bound : ∀ r, ‖G r z₀‖ ^ 2 ≤ C := by
    intro r
    have hsum := hsummable z₀ hz₀
    have hbound := hboundary z₀ hz₀
    have hr : ‖G r z₀‖ ^ 2 ≤ ∑' s, ‖G s z₀‖ ^ 2 := by
      set f := fun s => ‖G s z₀‖ ^ 2 with hf_def
      have h1 : f r ≤ ∑ s ∈ Finset.range (r + 1), f s := by
        apply Finset.single_le_sum
        · intro i _; exact sq_nonneg _
        · exact Finset.mem_range.mpr (Nat.lt_succ_self r)
      have h2 : ∑ s ∈ Finset.range (r + 1), f s ≤ ∑' s, f s := hsum.sum_le_tsum _ (fun _ _ => sq_nonneg _)
      linarith
    exact le_trans hr hbound
  -- sup_{‖z‖=R} ‖G r z‖^2 ≤ C because at the maximizing point, it's ≤ the sum ≤ C
  have hsphere_nonempty : (Metric.sphere (0 : ℂ) R).Nonempty := ⟨z₀, by simp [hz₀]⟩
  have hsphere_compact : IsCompact (Metric.sphere (0 : ℂ) R) := isCompact_sphere _ _
  have hG_cont : ∀ r, ContinuousOn (fun z => ‖G r z‖) (Metric.closedBall (0 : ℂ) R) := by
    intro r
    apply ContinuousOn.norm
    apply ContinuousOn.congr
    · exact ContinuousOn.smul (continuous_pow r).continuousOn (hV_analytic r).continuousOn
    · intro z hz
      exact hV_factor r z hz
  have hG_sq_cont : ∀ r, ContinuousOn (fun z => ‖G r z‖ ^ 2) (Metric.sphere (0 : ℂ) R) := by
    intro r
    apply ContinuousOn.pow
    apply (hG_cont r).mono
    exact Metric.sphere_subset_closedBall
  -- For any z on the boundary, ‖G r z‖^2 ≤ C
  have hboundary_bound : ∀ r z, ‖z‖ = R → ‖G r z‖ ^ 2 ≤ C := by
    intro r z hz
    have hsum := hsummable z hz
    have hbound := hboundary z hz
    have hr : ‖G r z‖ ^ 2 ≤ ∑' s, ‖G s z‖ ^ 2 := by
      set f := fun s => ‖G s z‖ ^ 2 with hf_def
      have h1 : f r ≤ ∑ s ∈ Finset.range (r + 1), f s := by
        apply Finset.single_le_sum
        · intro i _; exact sq_nonneg _
        · exact Finset.mem_range.mpr (Nat.lt_succ_self r)
      have h2 : ∑ s ∈ Finset.range (r + 1), f s ≤ ∑' s, f s := hsum.sum_le_tsum _ (fun _ _ => sq_nonneg _)
      linarith
    exact le_trans hr hbound
  -- Use maximum modulus: for V r analytic on closed ball, ‖V r w‖ ≤ sup_{‖z‖=R} ‖V r z‖
  have hw_in : w ∈ Metric.closedBall (0 : ℂ) R := Metric.mem_closedBall.mpr (by simpa using hw.le)
  -- Key lemma: ‖V r w‖^2 ≤ C / R^(2r) for each r
  have hV_bound : ∀ r, ‖V r w‖ ^ 2 ≤ C / R ^ (2 * r) := by
    intro r
    -- By maximum modulus principle for V r
    -- Maximum principle: ‖V r w‖ ≤ sup_{‖z‖=R} ‖V r z‖
    set hVr_an := hV_analytic r with hVr_an_def
    -- Maximum modulus: the norm of an analytic function on a closed ball is bounded by the sup on the sphere
    have hVr_cont : ContinuousOn (V r) (Metric.closedBall (0 : ℂ) R) := hVr_an.continuousOn
    have h_image_compact : IsCompact (Set.image (fun z => ‖V r z‖) (Metric.sphere (0 : ℂ) R)) := by
      apply hsphere_compact.image_of_continuousOn
      exact hVr_cont.norm.mono (Metric.sphere_subset_closedBall)
    -- Maximum modulus principle: ‖V r w‖ ≤ sup_{‖z‖=R} ‖V r z‖
    have hv_le_sup : ‖V r w‖ ≤ sSup ((fun z => ‖V r z‖) '' Metric.sphere (0 : ℂ) R) := by
      -- Maximum modulus principle: norm of analytic function on closed ball ≤ sup on sphere
      have hfrontier : frontier (Metric.closedBall (0 : ℂ) R) = Metric.sphere (0 : ℂ) R := by
        rw [frontier_closedBall]
        simp [hR.ne']
      rw [← hfrontier]
      have hclosed : IsClosed (Metric.closedBall (0 : ℂ) R) := Metric.isClosed_closedBall
      have hclosure : closure (Metric.closedBall (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := hclosed.closure_eq
      have hw_in_closure : w ∈ closure (Metric.closedBall (0 : ℂ) R) := by rw [hclosure]; exact hw_in
      have hVr_diff : DiffContOnCl ℂ (V r) (Metric.closedBall (0 : ℂ) R) := by
        have hdiff : DifferentiableOn ℂ (V r) (closure (Metric.closedBall (0 : ℂ) R)) := by
          rw [hclosure]
          exact hVr_an.differentiableOn
        exact hdiff.diffContOnCl
      rw [hfrontier]
      have hbound : ∀ z ∈ frontier (Metric.closedBall (0 : ℂ) R), ‖V r z‖ ≤ sSup ((fun z => ‖V r z‖) '' frontier (Metric.closedBall (0 : ℂ) R)) := by
        intro z hz
        rw [hfrontier] at hz ⊢
        exact le_csSup h_image_compact.bddAbove ⟨z, hz, rfl⟩
      rw [← hfrontier]
      exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_closedBall hVr_diff hbound hw_in_closure
    -- Bound the sup by √C / R^r
    -- For any z on sphere: ‖V r z‖ = ‖G r z‖ / R^r
    have hVz_eq : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖V r z‖ = ‖G r z‖ / R ^ r := by
      intro z hz
      have hz_in : z ∈ Metric.closedBall (0 : ℂ) R := Metric.sphere_subset_closedBall hz
      rw [hV_factor r z hz_in]
      have hz_norm : ‖z‖ = R := by simpa using hz
      simp [norm_smul, hz_norm]
      exact eq_div_of_mul_eq (pow_ne_zero r hR.ne') (by ring)
    -- The sup of ‖V r z‖ on sphere equals sup of ‖G r z‖ / R^r
    have h_image_eq : (fun z => ‖V r z‖) '' Metric.sphere (0 : ℂ) R =
        (fun z => ‖G r z‖ / R ^ r) '' Metric.sphere (0 : ℂ) R := by
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, (hVz_eq z hz).symm⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, hVz_eq z hz⟩
    -- Sup of ‖G r z‖ on sphere is ≤ √C since each ‖G r z‖^2 ≤ C
    have hGs_bound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖G r z‖ ≤ Real.sqrt C := by
      intro z hz
      have := hboundary_bound r z (by simpa using hz)
      exact Real.le_sqrt_of_sq_le this
    have hGsSup_le : sSup ((fun z => ‖G r z‖) '' Metric.sphere (0 : ℂ) R) ≤ Real.sqrt C := by
      apply csSup_le _
      · rintro _ ⟨z, hz, rfl⟩
        exact hGs_bound z hz
      · exact ⟨‖G r z₀‖, z₀, by simp [hz₀], rfl⟩
    -- Sup of ‖G r z‖ / R^r on sphere is ≤ √C / R^r
    have hGsR_bound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖G r z‖ / R ^ r ≤ Real.sqrt C / R ^ r := by
      intro z hz
      exact div_le_div_of_nonneg_right (hGs_bound z hz) (pow_nonneg (le_of_lt hR) r)
    have hGsRSup_le : sSup ((fun z => ‖G r z‖ / R ^ r) '' Metric.sphere (0 : ℂ) R) ≤ Real.sqrt C / R ^ r := by
      apply csSup_le _
      · rintro _ ⟨z, hz, rfl⟩
        exact hGsR_bound z hz
      · exact ⟨‖G r z₀‖ / R ^ r, z₀, by simp [hz₀], rfl⟩
    -- Now combine to get ‖V r w‖^2 ≤ C / R^(2*r)
    rw [h_image_eq] at hv_le_sup
    have hv_le : ‖V r w‖ ≤ Real.sqrt C / R ^ r := le_trans hv_le_sup hGsRSup_le
    have hv_nn : 0 ≤ ‖V r w‖ := norm_nonneg _
    have hbound_nn : 0 ≤ Real.sqrt C / R ^ r := div_nonneg (Real.sqrt_nonneg C) (pow_nonneg (le_of_lt hR) r)
    calc ‖V r w‖ ^ 2 ≤ (Real.sqrt C / R ^ r) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      _ = C / R ^ (2 * r) := by
        rw [div_pow, Real.sq_sqrt hC, pow_mul]; ring
  -- Now sum the geometric series
  -- First, bound ‖G r w‖^2 ≤ (‖w‖/R)^(2r) * C for r > m
  have hGw_bound : ∀ r, m < r → ‖G r w‖ ^ 2 ≤ (‖w‖ / R) ^ (2 * r) * C := by
    intro r hr
    rw [hV_factor r w hw_in]
    simp [norm_smul]
    have hv_bound := hV_bound r
    have hR_pow_ne_zero : R ^ (2 * r) ≠ 0 := pow_ne_zero _ hR.ne'
    have hrw_pow : ‖w‖ ^ (2 * r) * (C / R ^ (2 * r)) = (‖w‖ / R) ^ (2 * r) * C := by
      rw [div_pow, mul_comm]
      field_simp
    calc (‖w‖ ^ r * ‖V r w‖) ^ 2 = ‖w‖ ^ (2 * r) * ‖V r w‖ ^ 2 := by ring
      _ ≤ ‖w‖ ^ (2 * r) * (C / R ^ (2 * r)) := mul_le_mul_of_nonneg_left hv_bound (pow_nonneg (norm_nonneg w) _)
      _ = (‖w‖ / R) ^ (2 * r) * C := hrw_pow
  -- The geometric series ∑ (‖w‖/R)^(2r) * C is summable
  have hgeo_summable : Summable (fun r : ℕ => (‖w‖ / R) ^ (2 * r) * C) := by
    have h1 : Summable (fun r : ℕ => ((‖w‖ / R) ^ 2) ^ r) := summable_geometric_of_lt_one (sq_nonneg _) (by nlinarith)
    convert h1.mul_right C using 1
    ext r
    ring
  -- Define the upper bound function
  let f : ℕ → ℝ := fun r => if m < r then (‖w‖ / R) ^ (2 * r) * C else 0
  have hf_nonneg : ∀ r, 0 ≤ f r := fun r => by simp [f]; positivity
  -- The series with the if-condition is also summable (bounded by the full geometric series)
  have hf_summable : Summable f := by
    apply Summable.of_nonneg_of_le (fun r => hf_nonneg r) (fun r => ?_) hgeo_summable
    show (if m < r then (‖w‖ / R) ^ (2 * r) * C else 0) ≤ (‖w‖ / R) ^ (2 * r) * C
    split_ifs with hr <;> [rfl; positivity]
  -- Now show the tail sum is bounded by the geometric series
  have htail_le : ∑' r : ℕ, (if m < r then ‖G r w‖ ^ 2 else 0) ≤ ∑' r : ℕ, f r := by
    have hterm_le : ∀ r, (if m < r then ‖G r w‖ ^ 2 else 0) ≤ f r := by
      intro r
      by_cases hr : m < r
      · simp [f, hr]
        exact hGw_bound r hr
      · simp [f, hr]
    -- Need to show summability of the first series
    have hfirst_summable : Summable (fun r : ℕ => if m < r then ‖G r w‖ ^ 2 else 0) := by
      apply Summable.of_nonneg_of_le (fun r => by positivity) (fun r => hterm_le r) hf_summable
    exact Summable.tsum_le_tsum (fun r => hterm_le r) hfirst_summable hf_summable
  -- Now compute the geometric series sum
  have hf_sum_eq : ∑' r : ℕ, f r = (‖w‖ / R) ^ (2 * (m + 1)) / (1 - (‖w‖ / R) ^ 2) * C := by
    -- Rewrite f in terms of a shifted geometric series
    have hq : (‖w‖ / R) ^ 2 < 1 := by nlinarith
    have hq_nn : 0 ≤ (‖w‖ / R) ^ 2 := sq_nonneg _
    -- f r = 0 for r ≤ m, and f r = (‖w‖ / R) ^ (2 * r) * C for r > m
    -- So ∑' r, f r = ∑' r, (if m + 1 ≤ r then (‖w‖ / R) ^ (2 * r) * C else 0)
    -- = ∑' k, (‖w‖ / R) ^ (2 * (m + 1 + k)) * C  (setting r = m + 1 + k)
    have hf_eq_shifted : ∀ r, f r = if m + 1 ≤ r then (‖w‖ / R) ^ (2 * r) * C else 0 := by
      intro r
      simp [f]
    simp_rw [hf_eq_shifted]
    -- Reindex: use sum_add_tsum_nat_add
    have hsumm2 : Summable (fun r : ℕ => if m + 1 ≤ r then (‖w‖ / R) ^ (2 * r) * C else 0) := by
      apply Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) hgeo_summable
      show (if m + 1 ≤ r then (‖w‖ / R) ^ (2 * r) * C else 0) ≤ (‖w‖ / R) ^ (2 * r) * C
      split_ifs with h <;> [rfl; positivity]
    rw [← hsumm2.sum_add_tsum_nat_add (m + 1)]
    -- The first (m+1) terms are 0 since i < m+1 implies ¬(m+1 ≤ i)
    have hsum_zero : ∑ i ∈ Finset.range (m + 1), (if m + 1 ≤ i then (‖w‖ / R) ^ (2 * i) * C else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      exact Nat.not_le.mpr (Finset.mem_range.mp hi)
    rw [hsum_zero, zero_add]
    -- Simplify: for all k, k + (m+1) ≥ m+1, so the condition is always true
    simp_rw [show ∀ k : ℕ, (if m + 1 ≤ k + (m + 1) then (‖w‖ / R) ^ (2 * (k + (m + 1))) * C else 0) =
        (‖w‖ / R) ^ (2 * (k + (m + 1))) * C by intro k; rw [if_pos (Nat.le_add_left _ _)]]
    -- Now compute the geometric series
    have hq : (‖w‖ / R) ^ 2 < 1 := hq
    -- (‖w‖ / R) ^ (2 * (k + (m + 1))) = (‖w‖ / R) ^ (2 * (m + 1)) * ((‖w‖ / R) ^ 2) ^ k
    have hrewrite : ∀ k : ℕ, (‖w‖ / R) ^ (2 * (k + (m + 1))) * C =
        (‖w‖ / R) ^ (2 * (m + 1)) * C * ((‖w‖ / R) ^ 2) ^ k := by
      intro k; ring
    simp_rw [hrewrite]
    -- Pull out the constant
    rw [tsum_mul_left]
    -- Compute the geometric series
    rw [tsum_geometric_of_lt_one hq_nn hq]
    -- Rearrange
    ring
  linarith

end CLT
end SYK
