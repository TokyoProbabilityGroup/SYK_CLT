import SYK.CLT.context

set_option autoImplicit false

namespace SYK.CLT

/-- The finite Gaussian coupling space at size index `k`. -/
abbrev GaussianCouplingSpace (C : CLTContext) (k : ℕ) :=
  CouplingSpace (systemSize C k) C.q

/-- Its canonical product Gaussian probability measure. -/
noncomputable def gaussianCouplingMeasure (C : CLTContext) (k : ℕ) :=
  standardGaussianMeasure (systemSize C k) C.q

end SYK.CLT
