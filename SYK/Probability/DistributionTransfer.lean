module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

public section

/-!
# A changing scalar in weak convergence

The scalar and the random law may both depend on the index. A Dirac law
and continuity of product and pushforward probability measures give the
needed multiplication rule.
-/

open MeasureTheory Filter
open scoped Topology

namespace SYK.Probability

private theorem dirac_prod_mul_law (c : ℝ) (μ : ProbabilityMeasure ℝ) :
    ((diracProba c).prod μ).map ((by fun_prop :
      Measurable (fun p : ℝ × ℝ => p.1 * p.2)).aemeasurable) =
      μ.map ((by fun_prop : Measurable (fun x : ℝ => c * x)).aemeasurable) := by
  apply Subtype.ext
  change Measure.map (fun p : ℝ × ℝ => p.1 * p.2)
      ((Measure.dirac c).prod (μ : Measure ℝ)) =
    Measure.map (fun x : ℝ => c * x) (μ : Measure ℝ)
  rw [Measure.dirac_prod,
    Measure.map_map (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 * p.2))
      (by fun_prop : Measurable (Prod.mk c : ℝ → ℝ × ℝ))]
  rfl

/-- Weak convergence of laws is preserved when multiplication coefficients converge. -/
private theorem probabilityMeasure_mul_tendsto
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : Tendsto μs atTop (𝓝 μ))
    (a : ℕ → ℝ) (b : ℝ) (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => (μs n).map ((by fun_prop :
      Measurable (fun x : ℝ => a n * x)).aemeasurable)) atTop
      (𝓝 (μ.map ((by fun_prop :
        Measurable (fun x : ℝ => b * x)).aemeasurable))) := by
  let m (n : ℕ) : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ :=
    (diracProba (a n), μs n)
  let mlim : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ := (diracProba b, μ)
  have hdirac : Tendsto (fun n => diracProba (a n)) atTop (𝓝 (diracProba b)) :=
    continuous_diracProba.continuousAt.tendsto.comp ha
  have hpair : Tendsto m atTop (𝓝 mlim) := by
    simpa only [m, mlim, nhds_prod_eq] using hdirac.prodMk hμ
  have hprod : Tendsto (fun n => (m n).1.prod (m n).2) atTop
      (𝓝 (mlim.1.prod mlim.2)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (m n).1.prod (m n).2) (mlim.1.prod mlim.2)
    hprod (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1 * p.2))
  simpa only [m, mlim, dirac_prod_mul_law] using hmap

/-- Multiplication by a convergent scalar preserves convergence in distribution,
including when the source probability space varies with the index. -/
theorem tendstoInDistribution_mul_coeff
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μs : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μs n)]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (X : (n : ℕ) → Ω n → ℝ) (Z : ℝ → ℝ)
    (hX : TendstoInDistribution X atTop Z μs ν)
    (a : ℕ → ℝ) (b : ℝ) (ha : Tendsto a atTop (𝓝 b)) :
    TendstoInDistribution (fun n ω => a n * X n ω) atTop
      (fun x => b * Z x) μs ν := by
  let laws (n : ℕ) : ProbabilityMeasure ℝ :=
    ⟨(μs n).map (X n), Measure.isProbabilityMeasure_map (hX.forall_aemeasurable n)⟩
  let lawlim : ProbabilityMeasure ℝ :=
    ⟨ν.map Z, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩
  have hmul := probabilityMeasure_mul_tendsto laws lawlim hX.tendsto a b ha
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact aemeasurable_const.mul (hX.forall_aemeasurable n)
  · exact aemeasurable_const.mul hX.aemeasurable_limit
  · have heq (n : ℕ) :
        (laws n).map ((by fun_prop :
          Measurable (fun x : ℝ => a n * x)).aemeasurable) =
        ⟨(μs n).map (fun ω => a n * X n ω),
          Measure.isProbabilityMeasure_map
            (aemeasurable_const.mul (hX.forall_aemeasurable n))⟩ := by
      apply Subtype.ext
      change Measure.map (fun x : ℝ => a n * x) (Measure.map (X n) (μs n)) =
        Measure.map (fun ω => a n * X n ω) (μs n)
      exact AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hX.forall_aemeasurable n)
    have hlim :
        lawlim.map ((by fun_prop :
          Measurable (fun x : ℝ => b * x)).aemeasurable) =
        ⟨ν.map (fun x => b * Z x),
          Measure.isProbabilityMeasure_map
            (aemeasurable_const.mul hX.aemeasurable_limit)⟩ := by
      apply Subtype.ext
      change Measure.map (fun x : ℝ => b * x) (Measure.map Z ν) =
        Measure.map (fun x => b * Z x) ν
      exact AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX.aemeasurable_limit
    simpa only [heq, hlim] using hmul

end SYK.Probability
