import SYK.CLT.definitions

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace SYK
namespace CLT

theorem gaussianHamiltonian_selfAdjoint (P : FixedParameters) (k : ℕ)
    (g : CouplingSpace (systemSize P k) P.q) :
    star (gaussianHamiltonian P k g) = gaussianHamiltonian P k g := by
  exact normalizedHamiltonian_self_adjoint
    (modelParameters P k) (matrixMajorana (systemSize P k)) 1 g

/-- On the real axis, the complex and real definitions of the annealed
partition function agree. -/
theorem annealedPartitionR_eq_complex_re (P : FixedParameters) (k : ℕ)
    (β : ℝ) :
    annealedPartitionR P k β =
      (annealedPartitionC P k (β : ℂ)).re := by
  sorry

/-- The exact finite-volume radial decomposition. -/
theorem exact_FTW_decomposition (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) :
    relativePartition P k β g - 1 =
      radialCoefficient P k β * radialStatistic P k g +
        higherChaosRemainder P k β g := by
  simp [higherChaosRemainder]

end CLT
end SYK
