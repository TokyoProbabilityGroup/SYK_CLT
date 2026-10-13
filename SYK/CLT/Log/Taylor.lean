import SYK.CLT.Basic

/-!
# Pointwise logarithmic approximation

The error in linearizing `log y` is nonnegative. On `y ≥ 1/2` it is at most
twice the square of `y - 1`. The complementary event is controlled in
`CLT/Log/EventBound.lean` using the lower partition-function bound and a
Gaussian moment estimate.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SYK.CLT

private theorem log_linear_error_nonneg {y : ℝ} (hy : 0 < y) :
    0 ≤ y - 1 - Real.log y := by
  linarith [Real.log_le_sub_one_of_pos hy]

private theorem log_linear_error_le_sq {y : ℝ}
    (hy : 0 < y) (hhalf : (1 / 2 : ℝ) ≤ y) :
    y - 1 - Real.log y ≤ 2 * (y - 1) ^ 2 := by
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at hlog
  have h1 : y - 1 - Real.log y ≤ (y - 1) ^ 2 / y := by
    apply (le_div_iff₀ hy).2
    have h := mul_le_mul_of_nonneg_left hlog hy.le
    field_simp at h
    nlinarith
  have h2 : (y - 1) ^ 2 / y ≤ 2 * (y - 1) ^ 2 := by
    apply (div_le_iff₀ hy).2
    nlinarith [sq_nonneg (y - 1)]
  exact h1.trans h2

/-- The error Y_N - 1 - log Y_N in the linear approximation to the logarithm. -/
noncomputable def Setting.logLinearError {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) : ℝ :=
  S.Y β n g - 1 - Real.log (S.Y β n g)

theorem Setting.logLinearError_nonneg {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    0 ≤ S.logLinearError β n g :=
  log_linear_error_nonneg (S.Y_pos β n g)

theorem Setting.logLinearError_le_sq_of_half_le {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q)
    (hhalf : (1 / 2 : ℝ) ≤ S.Y β n g) :
    S.logLinearError β n g ≤ 2 * (S.Y β n g - 1) ^ 2 :=
  log_linear_error_le_sq (S.Y_pos β n g) hhalf

theorem Setting.logLinearError_le_log_meanZ_of_lt_half {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q)
    (hhalf : S.Y β n g < (1 / 2 : ℝ)) :
    S.logLinearError β n g ≤ Real.log (S.meanZ β n) := by
  unfold Setting.logLinearError
  linarith [S.neg_log_Y_le_log_meanZ β n g]

theorem Setting.logLinearError_integrable {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    Integrable (S.logLinearError β n)
      (standardGaussianMeasure (S.N n) q) := by
  change Integrable (fun g => S.Y β n g - 1 - Real.log (S.Y β n g)) _
  exact ((S.Y_integrable β n).sub (integrable_const _)).sub
    (S.log_Y_integrable β n)

theorem Setting.integral_logLinearError {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    (∫ g, S.logLinearError β n g ∂standardGaussianMeasure (S.N n) q) =
      -(∫ g, Real.log (S.Y β n g) ∂standardGaussianMeasure (S.N n) q) := by
  have hsub : (∫ g, S.logLinearError β n g
      ∂standardGaussianMeasure (S.N n) q) =
    (∫ g, S.Y β n g - 1 ∂standardGaussianMeasure (S.N n) q) -
      (∫ g, Real.log (S.Y β n g)
        ∂standardGaussianMeasure (S.N n) q) := by
    exact integral_sub ((S.Y_integrable β n).sub (integrable_const (1 : ℝ)))
      (S.log_Y_integrable β n)
  rw [hsub, integral_sub (S.Y_integrable β n) (integrable_const (1 : ℝ))]
  have hμ : (standardGaussianMeasure (S.N n) q).real Set.univ = 1 := by simp
  simp only [integral_const, hμ, one_smul]
  have hY := S.integral_Y β n
  rw [hY]
  ring

theorem Setting.logFluctuation_eq_relative_sub_centeredError {q : ℕ}
    (S : Setting q) (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    S.logFluctuation β n g = S.relativeFluctuation β n g -
      S.fluctuationScale n *
        (S.logLinearError β n g -
          ∫ x, S.logLinearError β n x ∂standardGaussianMeasure (S.N n) q) := by
  unfold Setting.logFluctuation Setting.relativeFluctuation
  rw [← S.centered_log_Y_eq β n g, S.integral_logLinearError]
  simp only [Setting.logLinearError]
  ring

/-- The permitted annealed pressure limit gives the linear upper bound
needed on the small-`Y` event. -/
theorem Setting.log_meanZ_le_linear_eventually {q : ℕ} (S : Setting q)
    (hFE : AnnealedInput q S) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      Real.log (S.meanZ β n) ≤ C * (S.N n : ℝ) := by
  let C := |hFE.ℓ β| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlt : hFE.ℓ β < C := by
    dsimp [C]
    linarith [le_abs_self (hFE.ℓ β)]
  have hev := (annealedFreeEnergy_tendsto hFE β).eventually_lt_const hlt
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn
  have hN : (0 : ℝ) < S.N n := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4)
      (S.q_ge_four.trans (S.q_le_N n))
  change Real.log (S.meanZ β n) / (S.N n : ℝ) < C at hn
  exact ((div_lt_iff₀ hN).mp hn).le

end SYK.CLT
