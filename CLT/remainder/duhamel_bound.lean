import SYK.CLT.gaussian.integration_by_parts
import SYK.CLT.lemmas.chaos_estimates

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- Explicit interface for the iterated Duhamel derivative estimate. -/
structure DuhamelBoundInputs (C : CLTContext) : Prop where
  derivative_bound : ∀ k r : ℕ, ∀ β : ℝ,
    ∀ alpha : MultiIndex (systemSize C k) C.q,
      multiIndexDegree alpha = r →
      ∀ g : CouplingSpace (systemSize C k) C.q,
        |multiIndexDerivative alpha (partitionFunctionR C k β) g| ≤
          (|β| * couplingScale (modelParameters C k) 1) ^ r *
            partitionFunctionR C k β g

theorem partitionFunction_gaussian_derivative_bound (C : CLTContext)
    (h : DuhamelBoundInputs C) (k r : ℕ) (β : ℝ)
    (alpha : MultiIndex (systemSize C k) C.q)
    (halpha : multiIndexDegree alpha = r)
    (g : CouplingSpace (systemSize C k) C.q) :
    |multiIndexDerivative alpha (partitionFunctionR C k β) g| ≤
      (|β| * couplingScale (modelParameters C k) 1) ^ r *
        partitionFunctionR C k β g :=
  partition_derivative_bound C k r β alpha halpha g
    (h.derivative_bound k r β alpha halpha g)

end SYK.CLT
