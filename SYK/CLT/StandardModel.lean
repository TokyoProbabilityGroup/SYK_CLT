import SYK.CLT.Main
import SYK.CLT.Normalization

/-!
# The standard Gaussian SYK family

The sizes `q + 2 * n` enumerate all even sizes at least `q` in
`subsec:SYK-model`. The concrete conditional versions of
`thm:partition-clt` and `thm:free-energy-clt` assume
`prop:annealed-free-energy` for this family through `AnnealedInput`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal Matrix.Norms.Operator

namespace SYK.CLT

/-- Standard matrix representations at every admissible even size. -/
def standardSetting (q : ℕ) (hq : Even q) (hq4 : 4 ≤ q) : Setting q where
  q_even := hq
  q_ge_four := hq4
  N n := q + 2 * n
  N_even n := hq.add ⟨n, by omega⟩
  q_le_N n := Nat.le_add_right q (2 * n)
  N_tendsto := tendsto_atTop.2 fun b =>
    eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  d n := StandardBasis ((q + 2 * n) / 2)
  fintype n := inferInstance
  decidableEq n := inferInstance
  nonempty n := inferInstance
  majorana n := standardMajoranaSystem (q + 2 * n) (hq.add ⟨n, by omega⟩)

/-- The indexing covers all even `N ≥ q`, rather than a proper subsequence. -/
theorem standardSetting_size_iff {q : ℕ} (hq : Even q) (hq4 : 4 ≤ q) (N : ℕ) :
    (∃! n, (standardSetting q hq hq4).N n = N) ↔ Even N ∧ q ≤ N := by
  constructor
  · rintro ⟨n, hn, _⟩
    rw [← hn]
    exact ⟨(standardSetting q hq hq4).N_even n,
      (standardSetting q hq hq4).q_le_N n⟩
  · rintro ⟨hN, hqN⟩
    obtain ⟨k, hk⟩ := hN
    obtain ⟨j, hj⟩ := hq
    refine ⟨(N - q) / 2, ?_, ?_⟩
    · change q + 2 * ((N - q) / 2) = N
      omega
    · intro n hn
      change q + 2 * n = N at hn
      omega

/-- The concrete `Z` has the manuscript's normalized trace, Hamiltonian
scale, and negative Gibbs exponent, by `partitionFunction_standard`. -/
theorem standardSetting_Z {q : ℕ} (hq : Even q) (hq4 : 4 ≤ q)
    (β : ℝ) (n : ℕ) (g : CouplingSpace (q + 2 * n) q) :
    (standardSetting q hq hq4).Z β n g =
      (((2 : ℂ) ^ ((q + 2 * n) / 2))⁻¹ *
        SYK.partitionFunction (β : ℂ)
          (normalizedHamiltonian ((standardSetting q hq hq4).params n)
            ((standardSetting q hq hq4).majorana n) g)).re := by
  exact congrArg Complex.re
    (partitionFunction_standard ((standardSetting q hq hq4).params n)
      ((standardSetting q hq hq4).N_even n) (β : ℂ) g)

/-- The three CLTs and variance positivity for the standard family,
under the explicit annealed proposition for that same family. -/
theorem standard_partition_and_log_partition_clt {q : ℕ}
    (hq : Even q) (hq4 : 4 ≤ q)
    (hFE : AnnealedInput q (standardSetting q hq hq4)) :
    let S := standardSetting q hq hq4
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
        TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1) :=
  partition_and_log_partition_clt (standardSetting q hq hq4) hFE

/-- `thm:partition-clt` for the standard family, projected from the joint CLT. -/
theorem standard_partition_clt {q : ℕ}
    (hq : Even q) (hq4 : 4 ≤ q)
    (hFE : AnnealedInput q (standardSetting q hq hq4)) :
    let S := standardSetting q hq hq4
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.relativeFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) ∧
        0 < limitVariance q hFE.ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
        TendstoInDistribution (S.standardizedFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q) (gaussianReal 0 1) := by
  obtain ⟨r, hr, h⟩ := standard_partition_and_log_partition_clt hq hq4 hFE
  refine ⟨r, hr, ?_⟩
  intro β hβ hβ0
  exact ⟨(h β hβ hβ0).1, (h β hβ hβ0).2.1, (h β hβ hβ0).2.2.2⟩

/-- `thm:free-energy-clt` for the standard family, with the same joint radius. -/
theorem standard_log_partition_clt {q : ℕ}
    (hq : Even q) (hq4 : 4 ≤ q)
    (hFE : AnnealedInput q (standardSetting q hq hq4)) :
    let S := standardSetting q hq hq4
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 →
        Tendsto (S.annealedFreeEnergy β) atTop (𝓝 (hFE.ℓ β)) ∧
        TendstoInDistribution (S.logFluctuation β) atTop (fun x : ℝ ↦ x)
          (fun n ↦ standardGaussianMeasure (S.N n) q)
          (gaussianReal 0 (limitVariance q hFE.ℓ β)) := by
  obtain ⟨r, hr, h⟩ := standard_partition_and_log_partition_clt hq hq4 hFE
  refine ⟨r, hr, ?_⟩
  intro β hβ hβ0
  exact ⟨(h β hβ hβ0).1, (h β hβ hβ0).2.2.1⟩

end SYK.CLT
