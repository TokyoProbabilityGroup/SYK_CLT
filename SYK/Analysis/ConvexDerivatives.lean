import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Derivatives of convergent convex functions

Local uniform convergence of differentiable convex functions gives uniform
convergence of their derivatives on compact sets under the stated regularity
of the limit. Entry point: `convex_convergence_deriv_tendstoUniformlyOn`.

The hypotheses are convexity and differentiability on an open set `I`, local uniform
convergence of the functions, differentiability of the limit and continuity of its derivative;
the conclusion is uniform convergence of the derivatives on every compact `K ⊆ I`. Deriving
the local uniform convergence of the functions from pointwise convergence, as stated in
`lem:convex-derivatives`, is not part of this file. The conditional CLT receives it as a
field of `AnnealedInput`.
-/

open Filter Metric
open scoped Topology

namespace SYK
namespace Analysis

/-- Triangle-inequality bound comparing the secant slopes of two functions. -/
lemma abs_slope_sub_le (g G : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    |slope g a b - slope G a b| ≤ (|g a - G a| + |g b - G b|) / (b - a) := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  rw [slope_def_field, slope_def_field, div_sub_div_same, abs_div, abs_of_pos hpos]
  gcongr
  calc |g b - g a - (G b - G a)| = |(g b - G b) - (g a - G a)| := by ring_nf
    _ ≤ |g b - G b| + |g a - G a| := abs_sub _ _
    _ = |g a - G a| + |g b - G b| := add_comm _ _

/-- If a differentiable function has a derivative with modulus of continuity controlled by
`d ↦ ε` on a set `S`, then on any small interval `[a, b] ⊆ S` its secant slope is within `ε`
of the derivative at any reference point `p ∈ [a, b]`.  This is the mean-value part of the
secant squeeze argument. -/
lemma abs_slope_sub_deriv_lt {F : ℝ → ℝ} {S : Set ℝ} {a b p d ε : ℝ}
    (hFdiff : ∀ z ∈ S, DifferentiableAt ℝ F z)
    (hd : ∀ u ∈ S, ∀ v ∈ S, dist u v < d → dist (deriv F u) (deriv F v) < ε)
    (hab : a < b) (hpa : a ≤ p) (hpb : p ≤ b) (hbad : b - a < d)
    (hsub : Set.Icc a b ⊆ S) (hp : p ∈ S) :
    |slope F a b - deriv F p| < ε := by
  have hcont : ContinuousOn F (Set.Icc a b) :=
    fun z hz => (hFdiff z (hsub hz)).continuousAt.continuousWithinAt
  have hdiffon : DifferentiableOn ℝ F (Set.Ioo a b) :=
    fun z hz => (hFdiff z (hsub (Set.Ioo_subset_Icc_self hz))).differentiableWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope F hab hcont hdiffon
  rw [← slope_def_field F a b] at hceq
  have hcS : c ∈ S := hsub (Set.Ioo_subset_Icc_self hc)
  have hcicc : c ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hc
  have hdist : dist c p < d := by
    rw [Real.dist_eq]
    have : |c - p| ≤ b - a := by
      rw [abs_le]; constructor
      · linarith [hcicc.1, hpb]
      · linarith [hcicc.2, hpa]
    linarith
  have hfin := hd c hcS p hp hdist
  rw [Real.dist_eq] at hfin
  rw [← hceq]
  exact hfin

/--
Convex convergence implies derivative convergence.

This proves the derivative-convergence part of `lem:convex-derivatives`
in `Paper/CLT_SYK.tex`, assuming locally uniform convergence of the functions.
The manuscript also derives that convergence from pointwise convergence;
that step is not proved here.
The open interval is represented by an open set `I`; convexity of `I` is
included in each `ConvexOn` hypothesis.  The assumption that the limit is $C^1$
is encoded as differentiability on `I` and continuity of `deriv F` on `I`.
-/
theorem convex_convergence_deriv_tendstoUniformlyOn
    {I K : Set ℝ} {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hI : IsOpen I)
    (hconv : ∀ n, ConvexOn ℝ I (f n))
    (hfdiff : ∀ n x, x ∈ I → DifferentiableAt ℝ (f n) x)
    (hlim : TendstoLocallyUniformlyOn f F atTop I)
    (hFdiff : ∀ x, x ∈ I → DifferentiableAt ℝ F x)
    (hFderiv_cont : ContinuousOn (fun x => deriv F x) I)
    (hK : IsCompact K)
    (hKI : K ⊆ I) :
    TendstoUniformlyOn (fun n x => deriv (f n) x) (fun x => deriv F x) atTop K := by
  classical
  -- Choose a closed metric thickening of `K` contained in the interval.
  obtain ⟨δ, hδ_pos, hδI⟩ := hK.exists_cthickening_subset_open hI hKI
  -- On this thickening the convergence is uniform, and `deriv F` is uniformly continuous.
  have hδ_compact : IsCompact (cthickening δ K) := hK.cthickening
  have hδ_uniform :
      TendstoUniformlyOn f F atTop (cthickening δ K) := by
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hδ_compact).mp
      (hlim.mono hδI)
  have hFderiv_uniform :
      UniformContinuousOn (fun x => deriv F x) (cthickening δ K) := by
    exact hδ_compact.uniformContinuousOn_of_continuous (hFderiv_cont.mono hδI)
  have h_squeeze :
      ∀ n x h, x ∈ K → 0 < h → h ≤ δ →
        slope (f n) (x - h) x ≤ deriv (f n) x ∧
          deriv (f n) x ≤ slope (f n) x (x + h) := by
    intro n x h hxK hh hle
    have hxI : x ∈ I := hKI hxK
    have hxmhI : x - h ∈ I := by
      apply hδI
      exact mem_cthickening_of_dist_le (x - h) x δ K hxK (by
        simpa [Real.dist_eq, abs_of_nonneg hh.le] using hle)
    have hxphI : x + h ∈ I := by
      apply hδI
      exact mem_cthickening_of_dist_le (x + h) x δ K hxK (by
        simpa [Real.dist_eq, abs_of_nonneg hh.le] using hle)
    constructor
    · exact (hconv n).slope_le_deriv hxmhI hxI (sub_lt_self x hh) (hfdiff n x hxI)
    · exact (hconv n).deriv_le_slope hxI hxphI (lt_add_of_pos_right x hh) (hfdiff n x hxI)
  -- Membership of nearby points in the thickening.
  have h_mem : ∀ x ∈ K, ∀ y : ℝ, dist y x ≤ δ → y ∈ cthickening δ K :=
    fun x hx y hy => mem_cthickening_of_dist_le y x δ K hx hy
  -- Differentiability of `F` on the thickening.
  have hFdiff' : ∀ z ∈ cthickening δ K, DifferentiableAt ℝ F z :=
    fun z hz => hFdiff z (hδI hz)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- From uniform continuity of `deriv F` choose the step scale.
  obtain ⟨d, hd_pos, hd⟩ :=
    (Metric.uniformContinuousOn_iff.mp hFderiv_uniform) (ε / 3) (by positivity)
  -- `hd` after beta reduction talks about `deriv F`.
  have hd' : ∀ u ∈ cthickening δ K, ∀ v ∈ cthickening δ K,
      dist u v < d → dist (deriv F u) (deriv F v) < ε / 3 := hd
  set t : ℝ := min d δ / 2 with ht_def
  have hmin_pos : 0 < min d δ := lt_min hd_pos hδ_pos
  have ht_pos : 0 < t := by rw [ht_def]; linarith
  have ht_le_δ : t ≤ δ := by
    have := min_le_right d δ; rw [ht_def]; linarith
  have ht_lt_d : t < d := by
    have := min_le_left d δ; rw [ht_def]; linarith
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  -- The tolerance for the uniform convergence of `f`.
  set η : ℝ := ε * t / 6 with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have hev := (Metric.tendstoUniformlyOn_iff.mp hδ_uniform) η hη_pos
  filter_upwards [hev] with n hn
  intro x hxK
  -- The three relevant points lie in the thickening.
  have hdistR : dist (x + t) x = t := by
    rw [Real.dist_eq]
    have he : x + t - x = t := by ring
    rw [he, abs_of_pos ht_pos]
  have hdistL : dist (x - t) x = t := by
    rw [Real.dist_eq]
    have he : x - t - x = -t := by ring
    rw [he, abs_neg, abs_of_pos ht_pos]
  have hxc : x ∈ cthickening δ K := h_mem x hxK x (by rw [dist_self]; exact hδ_pos.le)
  have hxR : x + t ∈ cthickening δ K := h_mem x hxK (x + t) (hdistR.le.trans ht_le_δ)
  have hxL : x - t ∈ cthickening δ K := h_mem x hxK (x - t) (hdistL.le.trans ht_le_δ)
  -- Uniform closeness of `f n` and `F` at these points.
  have hFx : |F x - f n x| < η := by rw [← Real.dist_eq]; exact hn x hxc
  have hFR : |F (x + t) - f n (x + t)| < η := by rw [← Real.dist_eq]; exact hn (x + t) hxR
  have hFL : |F (x - t) - f n (x - t)| < η := by rw [← Real.dist_eq]; exact hn (x - t) hxL
  -- The secant squeeze from convexity.
  obtain ⟨hsq1, hsq2⟩ := h_squeeze n x t hxK ht_pos ht_le_δ
  -- Uniform convergence of the right secant slope.
  have hslopeR : |slope F x (x + t) - slope (f n) x (x + t)| < ε / 3 := by
    have hb := abs_slope_sub_le F (f n) (show x < x + t by linarith)
    rw [(by ring : x + t - x = t)] at hb
    have hbound : (|F x - f n x| + |F (x + t) - f n (x + t)|) / t < ε / 3 := by
      rw [div_lt_iff₀ ht_pos]
      have h2η : (2 : ℝ) * η = ε / 3 * t := by rw [hη_def]; ring
      linarith [hFx, hFR, h2η]
    exact lt_of_le_of_lt hb hbound
  -- Uniform convergence of the left secant slope.
  have hslopeL : |slope F (x - t) x - slope (f n) (x - t) x| < ε / 3 := by
    have hb := abs_slope_sub_le F (f n) (show x - t < x by linarith)
    rw [(by ring : x - (x - t) = t)] at hb
    have hbound : (|F (x - t) - f n (x - t)| + |F x - f n x|) / t < ε / 3 := by
      rw [div_lt_iff₀ ht_pos]
      have h2η : (2 : ℝ) * η = ε / 3 * t := by rw [hη_def]; ring
      linarith [hFx, hFL, h2η]
    exact lt_of_le_of_lt hb hbound
  -- Mean-value bounds for `F`.
  have hmvtR : |slope F x (x + t) - deriv F x| < ε / 3 := by
    apply abs_slope_sub_deriv_lt hFdiff' hd' (show x < x + t by linarith) (le_refl x)
      (by linarith) (by rw [(by ring : x + t - x = t)]; exact ht_lt_d) ?_ hxc
    intro z hz
    exact h_mem x hxK z (by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hz.1])]; linarith [hz.2, ht_le_δ])
  have hmvtL : |slope F (x - t) x - deriv F x| < ε / 3 := by
    apply abs_slope_sub_deriv_lt hFdiff' hd' (show x - t < x by linarith) (by linarith)
      (le_refl x) (by rw [(by ring : x - (x - t) = t)]; exact ht_lt_d) ?_ hxc
    intro z hz
    exact h_mem x hxK z (by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hz.2]), neg_sub]; linarith [hz.1, ht_le_δ])
  -- Combine everything.
  rw [abs_lt] at hslopeR hslopeL hmvtR hmvtL
  rw [Real.dist_eq, abs_lt]
  constructor <;>
    linarith [hslopeR.1, hslopeR.2, hslopeL.1, hslopeL.2, hmvtR.1, hmvtR.2, hmvtL.1, hmvtL.2,
      hsq1, hsq2]

end Analysis
end SYK
