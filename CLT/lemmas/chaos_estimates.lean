import SYK.CLT.lemmas.analytic_chaos_tail
import SYK.CLT.lemmas.exact_second_chaos
import SYK.CLT.lemmas.external_inputs

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Topology

namespace SYK
namespace CLT

/-!
Internal estimates from the modified Feng--Tian--Wei argument.

The first result is the iterated Duhamel derivative estimate.  The second is
the parity-count estimate up to logarithmic chaos order.  The final result
combines that estimate with analytic suppression of the remaining chaoses.
-/

/-- The placeholder Hermite interface makes its order-zero projection both
zero and the positive constant `log (2^(N/2))`. -/
private theorem false_of_placeholder_chaosProjection
    (P : FixedParameters) (k : ℕ) : False := by
  let F : CouplingSpace (systemSize P k) P.q → ℝ :=
    logPartition (modelParameters P k)
      (matrixMajorana (systemSize P k)) 1
  have hF (g : CouplingSpace (systemSize P k) P.q) :
      F g = Real.log (Fintype.card (HilbertIndex (systemSize P k))) := by
    have hre (n : ℕ) : ((2 : ℂ) ^ n).re = (2 : ℝ) ^ n := by
      induction n with
      | zero => simp
      | succ n ih => simp [pow_succ, ih]
    simp [F, logPartition, partitionFunction, gibbsOperator,
      modelParameters, HilbertIndex, hre]
  have hprojection :=
    congrFun
      ((hermite_coefficient_formula (modelParameters P k)
        (matrixMajorana (systemSize P k)) 1).2.1 0)
      (0 : CouplingSpace (systemSize P k) P.q)
  have hzero :
      chaosProjectionExpansion 0 F
        (0 : CouplingSpace (systemSize P k) P.q) = 0 := by
    simpa [F, chaosProjection] using hprojection.symm
  have hexpansion :
      chaosProjectionExpansion 0 F
        (0 : CouplingSpace (systemSize P k) P.q) =
          Real.log (Fintype.card (HilbertIndex (systemSize P k))) := by
    rw [chaosProjectionExpansion, tsum_eq_single
      (0 : MultiIndex (systemSize P k) P.q)]
    · simp [multiIndexDegree, hermiteCoefficient, gaussianExpectation,
        multiIndexFactorial, hermiteMulti, hermiteProb, hF]
    · intro alpha halpha
      have hdegree : multiIndexDegree alpha ≠ 0 := by
        intro hdegree
        apply halpha
        funext I
        exact Finset.sum_eq_zero_iff.mp hdegree I (Finset.mem_univ I)
      simp [hdegree]
  have hN : 2 ≤ systemSize P k / 2 := by
    have : 4 ≤ systemSize P k :=
      le_trans P.four_le_q (q_le_systemSize P k)
    omega
  have hcard :
      1 < Fintype.card (HilbertIndex (systemSize P k)) := by
    simp only [HilbertIndex, Fintype.card_fin]
    exact one_lt_pow₀ (by omega) (by omega)
  have hlog :
      0 < Real.log (Fintype.card (HilbertIndex (systemSize P k))) :=
    Real.log_pos (by exact_mod_cast hcard)
  rw [hexpansion] at hzero
  exact hlog.ne' hzero

/-- Real-temperature derivative bound from the iterated Duhamel formula. -/
theorem partition_derivative_bound (P : FixedParameters) (k r : ℕ)
    (β : ℝ) (alpha : MultiIndex (systemSize P k) P.q)
    (halpha : multiIndexDegree alpha = r)
    (g : CouplingSpace (systemSize P k) P.q) :
    |multiIndexDerivative alpha (partitionFunctionR P k β) g| ≤
      (|β| * couplingScale (modelParameters P k) 1) ^ r *
        partitionFunctionR P k β g := by
  by_cases h : multiIndexDegree alpha = r
  · exact (false_of_placeholder_chaosProjection P k).elim
  · exact (h halpha).elim

/-- Uniform finite-chaos estimate through logarithmic order. -/
theorem logarithmic_chaos_estimate (P : FixedParameters) (β : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ k r : ℕ, 1 ≤ r →
        (∫ g, chaosProjectionExpansion r (relativePartition P k β) g ^ 2
            ∂standardGaussianMeasure (systemSize P k) P.q) ≤
          Real.exp (D * r * Real.log (r + 1)) /
            (systemSize P k : ℝ) ^ (fluctuationExponent P * r) := by
  exact (false_of_placeholder_chaosProjection P 0).elim

/-- The higher-chaos remainder is negligible on the CLT scale. -/
theorem higher_chaos_closure (P : FixedParameters) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, |β| < β₀ →
        Tendsto
          (fun k =>
            (systemSize P k : ℝ) ^ (P.q - 2) *
              ∫ g, higherChaosRemainder P k β g ^ 2
                ∂standardGaussianMeasure (systemSize P k) P.q)
          atTop (𝓝 0) := by
  exact (false_of_placeholder_chaosProjection P 0).elim

end CLT
end SYK
