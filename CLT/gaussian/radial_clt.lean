import SYK.CLT.gaussian.product_space

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- The radial statistic normalized to its expected unit-variance scale. -/
noncomputable def normalizedRadialStatistic (C : CLTContext) (k : ℕ)
    (g : GaussianCouplingSpace C k) : ℝ :=
  Real.sqrt ((interactionCount C k : ℝ) / 2) * radialStatistic C k g

/-- The scalar Gaussian CLT needed by the final radial decomposition. -/
def RadialCLTStatement (C : CLTContext) : Prop :=
  ConvergesToCenteredGaussian
    (fun k => gaussianCouplingMeasure C k)
    (normalizedRadialStatistic C) 1

/-- Explicit interface for the radial CLT until its Mathlib adapter is complete. -/
structure RadialCLTInputs (C : CLTContext) : Prop where
  radial_clt : RadialCLTStatement C

theorem radialStatistic_clt (C : CLTContext) (h : RadialCLTInputs C) :
    RadialCLTStatement C :=
  h.radial_clt

end SYK.CLT
