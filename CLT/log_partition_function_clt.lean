import SYK.CLT.partition_function_clt

set_option autoImplicit false

noncomputable section

namespace SYK.CLT

/-- The centered log-partition fluctuation on the same scale. -/
noncomputable def scaledLogRelativePartition (C : CLTContext) (β : ℝ)
    (k : ℕ) (g : CouplingSpace (systemSize C k) C.q) : ℝ :=
  (systemSize C k : ℝ) ^ fluctuationExponent C *
    Real.log (relativePartition C k β g)

/-- Conditional conclusion for the log-partition function. -/
def LogPartitionFunctionCLTStatement (C : CLTContext) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ β : ℝ, β ≠ 0 → |β| < β₀ →
      ConvergesToCenteredGaussian
        (fun k => standardGaussianMeasure (systemSize C k) C.q)
        (scaledLogRelativePartition C β)
        ((Nat.factorial C.q : ℝ) / 2 * β ^ 2 *
          limitingPressureDerivative C β ^ 2)

/-- The concentration and logarithmic-comparison input, kept explicit. -/
structure LogPartitionFunctionCLTInputs (C : CLTContext)
    (_hHT : HighTemperatureInputs C) : Prop where
  log_clt : LogPartitionFunctionCLTStatement C

theorem logPartitionFunction_clt_of_inputs (C : CLTContext)
    (hHT : HighTemperatureInputs C)
    (hLog : LogPartitionFunctionCLTInputs C hHT) :
    LogPartitionFunctionCLTStatement C :=
  hLog.log_clt

end SYK.CLT
