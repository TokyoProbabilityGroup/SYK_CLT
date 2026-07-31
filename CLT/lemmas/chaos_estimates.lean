import SYK.CLT.lemmas.exact_second_chaos

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Topology

namespace SYK
namespace CLT

/-!
Internal estimates from the modified Feng--Tian--Wei argument.

These statements are collected as explicit inputs while their proofs are
being formalized.  Naming each proposition once avoids the former pattern of
restating a claim in both a structure field and an identity theorem.
-/

/-- Real-temperature derivative bound from the iterated Duhamel formula. -/
def DuhamelBoundStatement (P : FixedParameters) : Prop :=
  ∀ k r : ℕ, ∀ β : ℝ,
    ∀ alpha : MultiIndex (systemSize P k) P.q,
      multiIndexDegree alpha = r →
      ∀ g : CouplingSpace (systemSize P k) P.q,
        |multiIndexDerivative alpha (partitionFunctionR P k β) g| ≤
          (|β| * couplingScale (modelParameters P k) 1) ^ r *
            partitionFunctionR P k β g

/-- Uniform finite-chaos estimate through logarithmic order. -/
def LowChaosEstimateStatement (P : FixedParameters) (β : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ k r : ℕ, 1 ≤ r →
      (∫ g, chaosProjectionExpansion r (relativePartition P k β) g ^ 2
          ∂standardGaussianMeasure (systemSize P k) P.q) ≤
        Real.exp (D * r * Real.log (r + 1)) /
          (systemSize P k : ℝ) ^ (fluctuationExponent P * r)

/-- The higher-chaos remainder is negligible on the CLT scale. -/
def HigherChaosClosureStatement (P : FixedParameters) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ β : ℝ, |β| < β₀ →
      Tendsto
        (fun k =>
          (systemSize P k : ℝ) ^ (P.q - 2) *
            ∫ g, higherChaosRemainder P k β g ^ 2
              ∂standardGaussianMeasure (systemSize P k) P.q)
        atTop (𝓝 0)

/-- Internal estimates assumed by the conditional CLT assembly. -/
structure ChaosEstimateInputs (P : FixedParameters) : Prop where
  duhamel_bound : DuhamelBoundStatement P
  low_chaos : ∀ β : ℝ, LowChaosEstimateStatement P β
  higher_chaos : HigherChaosClosureStatement P

end CLT
end SYK
