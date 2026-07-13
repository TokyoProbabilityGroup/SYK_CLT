import Mathlib
import SYK.SYK_model.model

set_option autoImplicit false

/-!
# Annealed SYK free-energy limit

This file states the main result of `refs/SYK-HT-arxiv.tex` using the
normalizations of that preprint.  The substantial construction and proof
obligations are temporarily closed with `sorry`.

The displayed free energy in the preprint contains division by `β`, so its
formal statement below assumes `β ≠ 0`.  The pressure theorem has no such
restriction and includes `β = 0`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace SYK
namespace AnnealedFE

/-! ## Finite Rademacher SYK model -/

/-- Physical sizes tend to infinity through the even integers starting at `q`. -/
def admissibleSize (q k : ℕ) : ℕ := q + 2 * k

theorem admissibleSize_even {q : ℕ} (hq : Even q) (k : ℕ) :
    Even (admissibleSize q k) := by
  sorry

theorem tendsto_admissibleSize_atTop (q : ℕ) :
    Tendsto (admissibleSize q) atTop atTop := by
  sorry

/-- The Hilbert space in the preprint has dimension `2^(N/2)`. -/
abbrev HilbertIndex (N : ℕ) := Fin (2 ^ (N / 2))

/-- Interaction labels are the `q`-element subsets of `[N]`. -/
abbrev Edge (N q : ℕ) := InteractionIndex N q

/-- One outcome of all independent Rademacher couplings. -/
abbrev SpinConfig (N q : ℕ) := Edge N q → Fin 2

/-- The sign attached to an outcome of a Rademacher coupling. -/
def rademacher {N q : ℕ} (ω : SpinConfig N q) (I : Edge N q) : ℝ :=
  if ω I = 0 then 1 else -1

/-- The variance `(q-1)! / N^(q-1)` of each coupling. -/
def sigmaSq (N q : ℕ) : ℝ :=
  (Nat.factorial (q - 1) : ℝ) / (N : ℝ) ^ (q - 1)

/-- The standard deviation of each coupling. -/
noncomputable def sigma (N q : ℕ) : ℝ := Real.sqrt (sigmaSq N q)

/-- A concrete Clifford representation on the Hilbert space used in the paper.

The repository's `MajoranaSystem` has generators satisfying
`γᵢ γⱼ + γⱼ γᵢ = 2 δᵢⱼ`.  The factor in `paperInteraction` below changes
these to the preprint convention `ψᵢ ψⱼ + ψⱼ ψᵢ = δᵢⱼ`.
-/
noncomputable def canonicalMajorana (N : ℕ) :
    MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) ℂ) := by
  sorry

/-- The operator `i^(q/2) ψ_{i₁}⋯ψ_{i_q}` in the preprint convention. -/
noncomputable def paperInteraction {N q : ℕ}
    (I : Edge N q) : Matrix (HilbertIndex N) (HilbertIndex N) ℂ :=
  ((((Real.sqrt 2)⁻¹ ^ q : ℝ) : ℂ) •
    ((phase q) • (canonicalMajorana N).psiProduct I))

/-- The Rademacher SYK Hamiltonian with
`J_I = sqrt((q-1)! / N^(q-1)) ε_I`. -/
noncomputable def paperHamiltonian (N q : ℕ) (ω : SpinConfig N q) :
    Matrix (HilbertIndex N) (HilbertIndex N) ℂ :=
  ∑ I : Edge N q,
    (((sigma N q * rademacher ω I : ℝ) : ℂ) • paperInteraction I)

/-- The normalized trace `2^(-N/2) Tr`. -/
noncomputable def normalizedTrace {N : ℕ}
    (A : Matrix (HilbertIndex N) (HilbertIndex N) ℂ) : ℂ :=
  (Fintype.card (HilbertIndex N) : ℂ)⁻¹ * Matrix.trace A

/-- `Z_{N,q}(β) = tr(exp(β H_SYK))` for a fixed coupling outcome. -/
noncomputable def partitionFunction (N q : ℕ) (β : ℝ)
    (ω : SpinConfig N q) : ℝ :=
  (normalizedTrace
    (NormedSpace.exp ((β : ℂ) • paperHamiltonian N q ω))).re

/-- The finite uniform expectation `E[Z_{N,q}(β)]`. -/
noncomputable def annealedPartition (N q : ℕ) (β : ℝ) : ℝ :=
  (Fintype.card (SpinConfig N q) : ℝ)⁻¹ *
    ∑ ω : SpinConfig N q, partitionFunction N q β ω

/-- `N⁻¹ log E[Z_{N,q}(β)]`. -/
noncomputable def annealedPressure (N q : ℕ) (β : ℝ) : ℝ :=
  Real.log (annealedPartition N q β) / (N : ℝ)

/-- `f_{N,q}(β) = β⁻¹ log E[Z_{N,q}(β)]` from the preprint. -/
noncomputable def annealedFreeEnergy (N q : ℕ) (β : ℝ) : ℝ :=
  Real.log (annealedPartition N q β) / β

theorem annealedPartition_pos (N q : ℕ) (β : ℝ) :
    0 < annealedPartition N q β := by
  sorry

@[simp]
theorem annealedPartition_zero (N q : ℕ) :
    annealedPartition N q 0 = 1 := by
  sorry

/-! ## The tree series and the CCG closed formula -/

/--
`ρ = (((q-1)! β²) / 2^(q+1))^(1/(q-1))` from the preprint.
-/
noncomputable def rho (q : ℕ) (β : ℝ) : ℝ :=
  Real.rpow
    (((Nat.factorial (q - 1) : ℝ) * β ^ 2) / (2 : ℝ) ^ (q + 1))
    (1 / (q - 1 : ℝ))

/-- Chords are represented by their two real endpoints. -/
abbrev Chord := ℝ × ℝ

/-- Sort two endpoints into increasing order. -/
def sortChord (u : Chord) : Chord := (min u.1 u.2, max u.1 u.2)

/-- Uniform measure on `[0,1]`. -/
noncomputable def unitIntervalMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)

/-- The law `ν` of `(min(U₁,U₂), max(U₁,U₂))`. -/
noncomputable def chordMeasure : MeasureTheory.Measure Chord :=
  MeasureTheory.Measure.map sortChord
    (MeasureTheory.Measure.prod unitIntervalMeasure unitIntervalMeasure)

/-- The chord-intersection sign `K`. -/
def chordKernel (x y : Chord) : ℂ :=
  if (x.1 < y.1 ∧ y.1 < x.2 ∧ x.2 < y.2) ∨
      (y.1 < x.1 ∧ x.1 < y.2 ∧ y.2 < x.2)
    then -1
    else 1

/-- The CCG function `H` whose fixed-point identity is stated below. -/
noncomputable def ccgH (q : ℕ) : ℂ → Chord → ℂ := by
  sorry

/-- Product of the pairwise crossing signs for `d` chords. -/
noncomputable def pairCrossingProduct {d : ℕ} (y : Fin d → Chord) : ℂ :=
  ∏ i : Fin d, ∏ j : Fin d, if i < j then chordKernel (y i) (y j) else 1

/-- The integrand common to the definitions of `H` and `R`. -/
noncomputable def ccgProduct (q d : ℕ) (z : ℂ) (y : Fin d → Chord) : ℂ :=
  (∏ i : Fin d,
      ccgH q z (y i) ^ (q - 1) / (Nat.factorial (q - 1) : ℂ)) *
    pairCrossingProduct y

/-- The fixed-point equation `(H-def)` defining the CCG function. -/
theorem ccgH_fixedPoint (q : ℕ) (z : ℂ) (x : Chord) :
    ccgH q z x =
      z + z * ∑' d : ℕ,
        if d = 0 then 0 else
          (Nat.factorial d : ℂ)⁻¹ *
            ∫ y : Fin d → Chord,
              (∏ i : Fin d, chordKernel x (y i)) * ccgProduct q d z y
            ∂(MeasureTheory.Measure.pi (fun _ : Fin d => chordMeasure)) := by
  sorry

/-- The CCG vertex-pointed function `R` from equation `(Rdef)`. -/
noncomputable def ccgR (q : ℕ) (z : ℂ) : ℂ :=
  z + z * ∑' d : ℕ,
    if d = 0 then 0 else
      (Nat.factorial d : ℂ)⁻¹ *
        ∫ y : Fin d → Chord, ccgProduct q d z y
          ∂(MeasureTheory.Measure.pi (fun _ : Fin d => chordMeasure))

/-- The CCG edge-pointed function `E` from equation `(Edef)`. -/
noncomputable def ccgE (q : ℕ) (z : ℂ) : ℂ :=
  (Nat.factorial q : ℂ)⁻¹ *
    ∫ x : Chord, ccgH q z x ^ q ∂chordMeasure

/--
The closed CCG expression
`𝓕(z) = ρ⁻¹ (R(ρz) - (q-1)E(ρz))`.

It is used only for `β ≠ 0`; at `β = 0` the preprint's displayed expression
has a removable singularity.
-/
noncomputable def paperClosedFormulaC (q : ℕ) (β : ℝ) (z : ℂ) : ℂ :=
  ((rho q β : ℂ)⁻¹) *
    (ccgR q ((rho q β : ℂ) * z) -
      ((q - 1 : ℕ) : ℂ) * ccgE q ((rho q β : ℂ) * z))

/-- Real restriction of the preprint's closed CCG expression. -/
noncomputable def paperClosedFormulaR (q : ℕ) (β t : ℝ) : ℝ :=
  (paperClosedFormulaC q β (t : ℂ)).re

/-- The complex tree series `Φ(z) = ∑_{v≥1} μ_v z^v`. -/
noncomputable def phiC (q : ℕ) (β : ℝ) : ℂ → ℂ := by
  sorry

/-- The real restriction of the tree series. -/
noncomputable def phiR (q : ℕ) (β t : ℝ) : ℝ :=
  (phiC q β (t : ℂ)).re

/-- A high-temperature threshold depending only on `q`. -/
noncomputable def betaStar (q : ℕ) : ℝ := by
  sorry

theorem betaStar_pos (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
    0 < betaStar q := by
  sorry

/-- The stationary point `t*` selected in `(1/2, 3/2)`. -/
noncomputable def tStar (q : ℕ) (β : ℝ) : ℝ := by
  sorry

theorem tStar_mem_Ioo
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    tStar q β ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) := by
  sorry

theorem tStar_stationary
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    (tStar q β : ℂ) * deriv (phiC q β) (tStar q β : ℂ) = 1 := by
  sorry

theorem tStar_unique
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β t : ℝ) (hβ : |β| ≤ betaStar q)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ))
    (hstationary : (t : ℂ) * deriv (phiC q β) (t : ℂ) = 1) :
    t = tStar q β := by
  sorry

/-- The tree series equals the CCG expression on the disk used in the paper. -/
theorem phiC_eq_paperClosedFormulaC
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ betaStar q)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    phiC q β z = paperClosedFormulaC q β z := by
  sorry

/-! ## Main limit theorems -/

/--
Pressure form of the main result.  This is precisely
`lim N⁻¹ log E[Z_{N,q}(β)]`; it remains meaningful at `β = 0`.
-/
theorem annealed_pressure_limit
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q β)
      atTop
      (𝓝 (phiR q β (tStar q β) - 1 - Real.log (tStar q β))) := by
  sorry

/-- The pressure limit written with the exact CCG formula from the preprint. -/
theorem annealed_pressure_limit_closedFormula
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q β)
      atTop
      (𝓝 (paperClosedFormulaR q β (tStar q β) - 1 -
        Real.log (tStar q β))) := by
  sorry

/--
Theorem `theorem:main-result` of the preprint:

`lim f_{N,q}(β)/N = (𝓕(t*) - 1 - log t*)/β`.
-/
theorem annealed_freeEnergy_density_limit
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ betaStar q) :
    Tendsto
      (fun k =>
        annealedFreeEnergy (admissibleSize q k) q β /
          (admissibleSize q k : ℝ))
      atTop
      (𝓝 ((paperClosedFormulaR q β (tStar q β) - 1 -
        Real.log (tStar q β)) / β)) := by
  sorry

/-- Quantifier order matching the theorem statement in the preprint. -/
theorem main_result
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β ≠ 0 → |β| ≤ β₀ →
        Tendsto
          (fun k =>
            annealedFreeEnergy (admissibleSize q k) q β /
              (admissibleSize q k : ℝ))
          atTop
          (𝓝 ((paperClosedFormulaR q β (tStar q β) - 1 -
            Real.log (tStar q β)) / β)) := by
  sorry

end AnnealedFE
end SYK
