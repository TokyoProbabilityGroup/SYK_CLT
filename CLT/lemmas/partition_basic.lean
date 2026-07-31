import SYK.CLT.main_result

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
  have hreal : ∀ g : CouplingSpace (systemSize P k) P.q,
      ((partitionFunctionR P k β g : ℝ) : ℂ) =
        partitionFunctionC P k (β : ℂ) g := by
    intro g
    have hH :
        star ((β : ℂ) • gaussianHamiltonian P k g) =
          (β : ℂ) • gaussianHamiltonian P k g := by
      rw [star_smul, gaussianHamiltonian_selfAdjoint]
      simp
    have him :
        (partitionFunctionC P k (β : ℂ) g).im = 0 := by
      have htrace :=
        partitionFunction_im_eq_zero (1 : NNReal) hH
      have htrace' :
          (Matrix.trace
            (NormedSpace.exp
              (-((β : ℂ) • gaussianHamiltonian P k g)))).im = 0 := by
        simpa [partitionFunction, gibbsOperator, smul_smul] using htrace
      have hcoeff :
          ((Fintype.card (HilbertIndex (systemSize P k)) : ℂ)⁻¹).im = 0 := by
        simp only [Complex.inv_im, Complex.natCast_im, neg_zero, zero_div]
      unfold partitionFunctionC normalizedTrace
      rw [Complex.mul_im, htrace', hcoeff]
      ring
    apply Complex.ext
    · rfl
    · simpa [partitionFunctionR] using him.symm
  unfold annealedPartitionR annealedPartitionC
  calc
    (∫ g, partitionFunctionR P k β g
        ∂standardGaussianMeasure (systemSize P k) P.q) =
        (∫ g, ((partitionFunctionR P k β g : ℝ) : ℂ)
          ∂standardGaussianMeasure (systemSize P k) P.q).re := by
            rw [integral_complex_ofReal]
            rfl
    _ = (∫ g, partitionFunctionC P k (β : ℂ) g
          ∂standardGaussianMeasure (systemSize P k) P.q).re := by
            congr 2
            funext g
            exact hreal g

/-- The exact finite-volume radial decomposition. -/
theorem exact_FTW_decomposition (P : FixedParameters) (k : ℕ)
    (β : ℝ) (g : CouplingSpace (systemSize P k) P.q) :
    relativePartition P k β g - 1 =
      radialCoefficient P k β * radialStatistic P k g +
        higherChaosRemainder P k β g := by
  simp [higherChaosRemainder]

end CLT
end SYK
