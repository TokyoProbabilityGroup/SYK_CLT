import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Distributional perturbations on varying probability spaces

An `L¹` or `L²` error tending to zero preserves weak convergence even when
the source space and probability measure vary with the index.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SYK.Probability

theorem varying_l1_perturb_clt
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μs : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μs n)]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (X Y : (n : ℕ) → Ω n → ℝ) (Z : ℝ → ℝ)
    (hX : TendstoInDistribution X atTop Z μs ν)
    (hY : ∀ n, AEMeasurable (Y n) (μs n))
    (hErrInt : ∀ n, Integrable (fun ω => Y n ω - X n ω) (μs n))
    (hErr : Tendsto (fun n => ∫ ω, ‖Y n ω - X n ω‖ ∂μs n)
      atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z μs ν := by
  refine ⟨hY, hX.aemeasurable_limit, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  have hbase := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hX.tendsto)
    F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hbound (n : ℕ) :
      |(∫ ω, F ω ∂(μs n).map (Y n)) -
        (∫ ω, F ω ∂(μs n).map (X n))| ≤
        (L : ℝ) * ∫ ω, ‖Y n ω - X n ω‖ ∂μs n := by
    have h_int_Y : Integrable (fun ω => F (Y n ω)) (μs n) := by
      refine Integrable.of_bound
        (hF_cont.measurable.comp_aemeasurable (hY n)).aestronglyMeasurable
        (‖F (0:ℝ)‖ + M) (ae_of_all _ fun ω => ?_)
      specialize hF_bounded (Y n ω) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n ω)) (F 0)).trans hF_bounded
    have h_int_X : Integrable (fun ω => F (X n ω)) (μs n) := by
      refine Integrable.of_bound
        (hF_cont.measurable.comp_aemeasurable (hX.forall_aemeasurable n)).aestronglyMeasurable
        (‖F (0:ℝ)‖ + M) (ae_of_all _ fun ω => ?_)
      specialize hF_bounded (X n ω) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n ω)) (F 0)).trans hF_bounded
    rw [integral_map (hY n) hF_cont.aestronglyMeasurable,
      integral_map (hX.forall_aemeasurable n) hF_cont.aestronglyMeasurable,
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc
      ‖∫ ω, F (Y n ω) - F (X n ω) ∂μs n‖ ≤
          ∫ ω, ‖F (Y n ω) - F (X n ω)‖ ∂μs n :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (L : ℝ) * ‖Y n ω - X n ω‖ ∂μs n := by
        apply integral_mono
        · exact (h_int_Y.sub h_int_X).norm
        · exact (hErrInt n).norm.const_mul _
        · intro ω
          exact hF_lip.norm_sub_le _ _
      _ = (L : ℝ) * ∫ ω, ‖Y n ω - X n ω‖ ∂μs n := by
        rw [integral_const_mul]
  have hdiff : Tendsto (fun n =>
      (∫ ω, F ω ∂(μs n).map (Y n)) -
        (∫ ω, F ω ∂(μs n).map (X n))) atTop (𝓝 0) := by
    have hR : Tendsto (fun n => (L : ℝ) *
        ∫ ω, ‖Y n ω - X n ω‖ ∂μs n) atTop (𝓝 0) := by
      simpa using hErr.const_mul (L : ℝ)
    have hAbs := squeeze_zero (fun n => abs_nonneg _) hbound hR
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact hAbs
  simp only [ProbabilityMeasure.coe_mk] at hbase
  convert hdiff.add hbase using 1
  · ext n
    abel
  · simp

private theorem integral_norm_le_Lp_norm {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : (∫ x, ‖f x‖ ∂μ) ≤ ‖f‖ := by
  have hLp : eLpNorm (fun x => f x) 1 μ ≤ eLpNorm (fun x => f x) 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable f)
  have hInt : Integrable (fun x => ‖f x‖) μ :=
    ((Lp.memLp f).integrable (by norm_num)).norm
  have hEq : (∫ x, ‖f x‖ ∂μ) = ENNReal.toReal (eLpNorm (fun x => f x) 1 μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    have h := lintegral_coe_eq_integral (fun x => ‖f x‖₊) (by simpa using hInt)
    change (∫ x, ‖f x‖ ∂μ) =
      ENNReal.toReal (∫⁻ x, (‖f x‖₊ : ENNReal) ∂μ)
    rw [h]
    exact (ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg (f x))).symm
  rw [hEq, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hLp

theorem varying_l2_perturb_clt
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μs : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μs n)]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (X Y : (n : ℕ) → Ω n → ℝ) (Z : ℝ → ℝ)
    (hX : TendstoInDistribution X atTop Z μs ν)
    (hY : ∀ n, AEMeasurable (Y n) (μs n))
    (R : (n : ℕ) → Lp ℝ 2 (μs n))
    (hR : ∀ n, (R n : Ω n → ℝ) =ᵐ[μs n] fun ω => Y n ω - X n ω)
    (hNorm : Tendsto (fun n => ‖R n‖) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z μs ν := by
  have hErrInt (n : ℕ) : Integrable (fun ω => Y n ω - X n ω) (μs n) :=
    ((Lp.memLp (R n)).integrable (by norm_num)).congr (hR n)
  have hErrBound (n : ℕ) :
      (∫ ω, ‖Y n ω - X n ω‖ ∂μs n) ≤ ‖R n‖ := by
    have hNormAE :
        (fun ω => ‖Y n ω - X n ω‖) =ᵐ[μs n]
          (fun ω => ‖R n ω‖) :=
      (hR n).mono fun ω hω => (congrArg norm hω).symm
    rw [integral_congr_ae hNormAE]
    exact integral_norm_le_Lp_norm (μs n) (R n)
  have hErr : Tendsto (fun n => ∫ ω, ‖Y n ω - X n ω‖ ∂μs n)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun n => integral_nonneg fun ω => norm_nonneg _)
      hErrBound hNorm
  exact varying_l1_perturb_clt μs ν X Y Z hX hY hErrInt hErr

end SYK.Probability
