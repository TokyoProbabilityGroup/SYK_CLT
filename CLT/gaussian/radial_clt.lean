import SYK.CLT.main_result

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- The Gaussian coupling space at system size `k`. -/
abbrev GaussianCouplingSpace (C : FixedParameters) (k : ℕ) :=
  CouplingSpace (systemSize C k) C.q

/-- The standard product Gaussian law on the coupling space. -/
noncomputable def gaussianCouplingMeasure (C : FixedParameters) (k : ℕ) :=
  standardGaussianMeasure (systemSize C k) C.q

/-- The radial statistic normalized to its expected unit-variance scale. -/
noncomputable def normalizedRadialStatistic (C : FixedParameters) (k : ℕ)
    (g : GaussianCouplingSpace C k) : ℝ :=
  Real.sqrt ((interactionCount C k : ℝ) / 2) * radialStatistic C k g

/-- The scalar Gaussian CLT needed by the final radial decomposition. -/
def RadialCLTStatement (C : FixedParameters) : Prop :=
  ConvergesToCenteredGaussian
    (fun k => gaussianCouplingMeasure C k)
    (normalizedRadialStatistic C) 1

end SYK.CLT
