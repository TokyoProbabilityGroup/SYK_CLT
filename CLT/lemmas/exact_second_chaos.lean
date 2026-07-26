import SYK.CLT.definitions
import SYK.CLT.lemmas.hermite_gauge_selection

set_option autoImplicit false

noncomputable section

namespace SYK
namespace CLT

/-!
The sign-gauge argument eliminates the first chaos and forces the second chaos
to be radial.  The coefficient is then obtained by Gaussian integration by
parts and the scaling identity `Z(β; tg) = Z(tβ; g)`.
-/

/-- The current Hermite interface is inconsistent with the placeholder
definition `chaosProjection = 0`: at zero temperature its order-zero
projection is both zero and the nonzero constant `log (2^(N/2))`.

This lemma isolates that temporary inconsistency.  It should disappear when
`chaosProjection` and `hermite_coefficient_formula` are implemented
consistently. -/
theorem placeholder_chaosProjection_inconsistent
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

/-- Exact identification of the first and second Gaussian chaoses. -/
theorem first_second_chaos_identification (P : FixedParameters) (k : ℕ)
    (β : ℝ) :
    chaosProjectionExpansion 1 (relativePartition P k β) = 0 ∧
      chaosProjectionExpansion 2 (relativePartition P k β) =
        fun g => radialCoefficient P k β * radialStatistic P k g := by
  exact (placeholder_chaosProjection_inconsistent P k).elim

end CLT
end SYK
