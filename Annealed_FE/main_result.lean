import SYK.SYK_model.model
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

set_option autoImplicit false

/-!
# Annealed SYK free-energy limit

This file gives a paper-facing adapter for the definitions in
`SYK.SYK_model.model` and states the main result of `refs/SYK-HT-arxiv.tex`.
All unfinished mathematical arguments occur in theorem proofs. Every
definition has a complete defining term.

The displayed free energy in the preprint contains division by `β`, so the
free-energy statement assumes `β ≠ 0`. The pressure statement also covers
`β = 0`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate NNReal

namespace SYK
namespace AnnealedFE

/-! ## Finite Rademacher SYK model -/

/-- Physical sizes tend to infinity through the even integers starting at `q`. -/
def admissibleSize (q k : ℕ) : ℕ := q + 2 * k

theorem admissibleSize_even {q : ℕ} (hq : Even q) (k : ℕ) :
    Even (admissibleSize q k) := by
  rcases hq with ⟨m, rfl⟩
  exact ⟨m + k, by simp [admissibleSize, two_mul]; omega⟩

theorem q_le_admissibleSize (q k : ℕ) : q ≤ admissibleSize q k := by
  simp [admissibleSize]

theorem tendsto_admissibleSize_atTop (q : ℕ) :
    Tendsto (admissibleSize q) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  simp only [admissibleSize]
  omega

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

/-- The scale converting the repository Majorana convention to the paper convention. -/
noncomputable def paperInteractionScale (q : ℕ) : ℝ :=
  (Real.sqrt 2)⁻¹ ^ q

/-- A concrete Clifford representation on the paper's Hilbert space. -/
theorem exists_canonicalMajorana (N : ℕ) :
    Nonempty (MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) ℂ)) := by
  sorry

/-- A fixed concrete Clifford representation. -/
noncomputable def canonicalMajorana (N : ℕ) :
    MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) ℂ) :=
  Classical.choice (exists_canonicalMajorana N)

/-- The operator `i^(q/2) ψ_{i₁}⋯ψ_{i_q}` in the preprint convention. -/
noncomputable def paperInteraction {N q : ℕ}
    (I : Edge N q) : Matrix (HilbertIndex N) (HilbertIndex N) ℂ :=
  ((paperInteractionScale q : ℝ) : ℂ) •
    ((phase q) • (canonicalMajorana N).psiProduct I)

/-- A `Params` value used to call the repository Hamiltonian on physical inputs.

The inverse-temperature field is set to zero because `SYK.hamiltonian` does not
use that field.
-/
def modelParamsOfPhysical (N q : ℕ)
    (h : 2 ≤ q ∧ Even q ∧ q ≤ N) : Params where
  N := N
  q := q
  q_even := h.2.1
  q_pos := by omega
  q_le_N := h.2.2
  β := 0
  β_nonneg := le_rfl

/-- The Rademacher SYK Hamiltonian, implemented through `SYK.hamiltonian`.

Outside the physical range `2 ≤ q`, `Even q`, and `q ≤ N`, this total adapter
is defined to be zero. Every asymptotic theorem below stays in the physical
range.
-/
noncomputable def paperHamiltonian (N q : ℕ) (ω : SpinConfig N q) :
    Matrix (HilbertIndex N) (HilbertIndex N) ℂ :=
  if h : 2 ≤ q ∧ Even q ∧ q ≤ N then
    SYK.hamiltonian (modelParamsOfPhysical N q h) (canonicalMajorana N)
      (fun I => paperInteractionScale q * sigma N q * rademacher ω I)
  else
    0

/-- Expansion of the model-based Hamiltonian in the notation of the preprint. -/
theorem paperHamiltonian_eq_sum
    (N q : ℕ) (ω : SpinConfig N q)
    (hq : 2 ≤ q) (hqEven : Even q) (hqN : q ≤ N) :
    paperHamiltonian N q ω =
      ∑ I : Edge N q,
        (((sigma N q * rademacher ω I : ℝ) : ℂ) • paperInteraction I) := by
  sorry

/-- The normalized trace `2^(-N/2) Tr`. -/
noncomputable def normalizedTrace {N : ℕ}
    (A : Matrix (HilbertIndex N) (HilbertIndex N) ℂ) : ℂ :=
  (Fintype.card (HilbertIndex N) : ℂ)⁻¹ * Matrix.trace A

/-- The nonnegative magnitude of a signed inverse temperature. -/
def betaMagnitude (β : ℝ) : NNReal := ⟨|β|, abs_nonneg β⟩

/-- Hamiltonian sign used to express `exp(βH)` through the repository's
`exp(-βH)` convention. -/
def hamiltonianForPaperSign {N : ℕ} (β : ℝ)
    (H : Matrix (HilbertIndex N) (HilbertIndex N) ℂ) :=
  if 0 ≤ β then -H else H

/-- `Z_{N,q}(β) = tr(exp(β H_SYK))` for a fixed coupling outcome.

This definition calls `SYK.partitionFunction`; `betaMagnitude` and
`hamiltonianForPaperSign` reconcile the sign and domain conventions.
-/
noncomputable def partitionFunction (N q : ℕ) (β : ℝ)
    (ω : SpinConfig N q) : ℝ :=
  ((Fintype.card (HilbertIndex N) : ℂ)⁻¹ *
    SYK.partitionFunction (betaMagnitude β)
      (hamiltonianForPaperSign β (paperHamiltonian N q ω))).re

/-- The adapter equals the preprint's signed exponential formula. -/
theorem partitionFunction_eq_exp (N q : ℕ) (β : ℝ) (ω : SpinConfig N q) :
    partitionFunction N q β ω =
      (normalizedTrace
        (NormedSpace.exp ((β : ℂ) • paperHamiltonian N q ω))).re := by
  sorry

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

theorem paperHamiltonian_selfAdjoint
    (N q : ℕ) (ω : SpinConfig N q)
    (hq : 2 ≤ q) (hqEven : Even q) (hqN : q ≤ N) :
    star (paperHamiltonian N q ω) = paperHamiltonian N q ω := by
  sorry

theorem annealedPartition_pos
    (N q : ℕ) (β : ℝ) (hq : 2 ≤ q) (hqEven : Even q) (hqN : q ≤ N) :
    0 < annealedPartition N q β := by
  sorry

@[simp]
theorem annealedPartition_zero
    (N q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) (hqN : q ≤ N) :
    annealedPartition N q 0 = 1 := by
  sorry

/-! ## Chord diagrams and the independent hypertree series -/

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

theorem chordMeasure_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure chordMeasure := by
  sorry

/-- The chord-intersection sign `K`. -/
def chordKernel (x y : Chord) : ℂ :=
  if (x.1 < y.1 ∧ y.1 < x.2 ∧ x.2 < y.2) ∨
      (y.1 < x.1 ∧ x.1 < y.2 ∧ y.2 < x.2)
    then -1
    else 1

/-- A finite simple `q`-uniform hypergraph on `Fin v`. -/
abbrev SimpleHypergraph (v q : ℕ) := Finset (Edge v q)

/-- Two vertices share a hyperedge of `G`. -/
def hypergraphAdjacent {v q : ℕ} (G : SimpleHypergraph v q)
    (i j : Fin v) : Prop :=
  ∃ e : Edge v q, e ∈ G ∧ i ∈ e.1 ∧ j ∈ e.1

/-- Connectivity of the two-section of a hypergraph. -/
def HypergraphConnected {v q : ℕ} (G : SimpleHypergraph v q) : Prop :=
  ∀ i j : Fin v, Relation.ReflTransGen (hypergraphAdjacent G) i j

/-- The paper's definition of a simple `q`-uniform hypertree. -/
def IsHypertree {v q : ℕ} (G : SimpleHypergraph v q) : Prop :=
  0 < v ∧ HypergraphConnected G ∧ (q - 1) * G.card = v - 1

/-- Labeled simple hypertrees on `Fin v`. -/
abbrev SimpleHypertree (v q : ℕ) :=
  {G : SimpleHypergraph v q // IsHypertree G}

/-- Whether two hyperedges have odd intersection cardinality. -/
def edgesMeetOddly {v q : ℕ} (e f : Edge v q) : Prop :=
  Odd ((e.1 ∩ f.1).card)

/-- Crossing sign of one chord assignment to a simple hypergraph. -/
noncomputable def crossingWeight {v q : ℕ} (G : SimpleHypergraph v q)
    (X : (e : G) → Chord) : ℂ :=
  by
    classical
    exact
      ∏ e : G, ∏ f : G,
        if e < f ∧ edgesMeetOddly e.1 f.1
          then chordKernel (X e) (X f)
          else 1

/-- Expected crossing sign `b_T` of a labeled simple hypertree. -/
noncomputable def bSimple {v q : ℕ} (T : SimpleHypertree v q) : ℂ :=
  ∫ X : (↥T.1 → Chord), crossingWeight T.1 X
    ∂(MeasureTheory.Measure.pi (fun _ : ↥T.1 => chordMeasure))

/-- `ρ = (((q-1)! β²) / 2^(q+1))^(1/(q-1))` from the preprint. -/
noncomputable def rho (q : ℕ) (β : ℝ) : ℝ :=
  Real.rpow
    (((Nat.factorial (q - 1) : ℝ) * β ^ 2) / (2 : ℝ) ^ (q + 1))
    (1 / (q - 1 : ℝ))

/-- The hypertree coefficient `μ_v` from equation `(mu-0)`. -/
noncomputable def treeMu (q : ℕ) (β : ℝ) (v : ℕ) : ℂ :=
  by
    classical
    exact
      ((rho q β : ℂ) ^ (v - 1) / (Nat.factorial v : ℂ)) *
        ∑ T : SimpleHypertree v q, bSimple T

/-- The independent hypertree series `Φ(z) = ∑ μ_v z^v`. -/
noncomputable def phiC (q : ℕ) (β : ℝ) (z : ℂ) : ℂ :=
  ∑' v : ℕ, treeMu q β v * z ^ v

/-- The real restriction of the hypertree series. -/
noncomputable def phiR (q : ℕ) (β t : ℝ) : ℝ :=
  (phiC q β (t : ℂ)).re

theorem phiC_real_of_real
    (q : ℕ) (β t : ℝ) :
    (phiC q β (t : ℂ)).im = 0 := by
  sorry

/-! ## The CCG fixed point and closed formula -/

/-- Product of the pairwise crossing signs for `d` chords. -/
noncomputable def pairCrossingProduct {d : ℕ} (y : Fin d → Chord) : ℂ :=
  ∏ i : Fin d, ∏ j : Fin d, if i < j then chordKernel (y i) (y j) else 1

/-- The integrand associated with a candidate CCG function. -/
noncomputable def ccgProductFor
    (H : ℂ → Chord → ℂ) (q d : ℕ) (z : ℂ) (y : Fin d → Chord) : ℂ :=
  (∏ i : Fin d,
      H z (y i) ^ (q - 1) / (Nat.factorial (q - 1) : ℂ)) *
    pairCrossingProduct y

/-- A chord in the support of the probability law `ν`. -/
def IsPaperChord (x : Chord) : Prop :=
  0 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ 1

/-- Radius `1/e²` used for the CCG fixed-point equation. -/
noncomputable def ccgDiskRadius : ℝ := 1 / Real.exp 2

/-- The disk on which the paper defines its CCG function. -/
noncomputable def ccgDisk : Set ℂ :=
  Metric.closedBall 0 ccgDiskRadius

/-- The physical domain of the CCG function. -/
noncomputable def ccgDomain : Set (ℂ × Chord) :=
  {p | p.1 ∈ ccgDisk ∧ IsPaperChord p.2}

/-- The complete paper-facing specification of a CCG representative. -/
def IsCCG (q : ℕ) (H : ℂ → Chord → ℂ) : Prop :=
  (∀ (z : ℂ) (x : Chord), z ∈ ccgDisk → IsPaperChord x →
    H z x =
      z + z * ∑' d : ℕ,
        if d = 0 then 0 else
          (Nat.factorial d : ℂ)⁻¹ *
            ∫ y : Fin d → Chord,
              (∏ i : Fin d, chordKernel x (y i)) * ccgProductFor H q d z y
            ∂(MeasureTheory.Measure.pi (fun _ : Fin d => chordMeasure))) ∧
  (∀ (z : ℂ) (x : Chord), z ∈ ccgDisk → IsPaperChord x → ‖H z x‖ ≤ 1) ∧
  ContinuousOn (fun p : ℂ × Chord => H p.1 p.2) ccgDomain ∧
  (∀ x : Chord, IsPaperChord x →
    AnalyticOnNhd ℂ (fun z : ℂ => H z x) ccgDisk)

/-- A CCG representative that is unique on the domain used by the paper. -/
def IsCanonicalCCG (q : ℕ) (H : ℂ → Chord → ℂ) : Prop :=
  IsCCG q H ∧
    ∀ G : ℂ → Chord → ℂ, IsCCG q G →
      ∀ (z : ℂ) (x : Chord), z ∈ ccgDisk → IsPaperChord x → G z x = H z x

/-- Existence of a bounded analytic CCG representative, unique on its domain. -/
theorem exists_canonicalCCG (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
    ∃ H : ℂ → Chord → ℂ, IsCanonicalCCG q H := by
  sorry

/-- A selected total representative of the paper's CCG function. -/
noncomputable def ccgH (q : ℕ) : ℂ → Chord → ℂ :=
  if h : 2 ≤ q ∧ Even q then
    Classical.choose (exists_canonicalCCG q h.1 h.2)
  else
    fun _ _ => 0

theorem ccgH_isCCG (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
    IsCCG q (ccgH q) := by
  rw [ccgH, dif_pos ⟨hq, hqEven⟩]
  exact (Classical.choose_spec (exists_canonicalCCG q hq hqEven)).1

theorem ccgH_uniqueOn
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (H : ℂ → Chord → ℂ) (hH : IsCCG q H) :
    ∀ (z : ℂ) (x : Chord), z ∈ ccgDisk → IsPaperChord x → H z x = ccgH q z x := by
  rw [ccgH, dif_pos ⟨hq, hqEven⟩]
  exact (Classical.choose_spec (exists_canonicalCCG q hq hqEven)).2 H hH

/-- The integrand common to the definitions of `H` and `R`. -/
noncomputable def ccgProduct (q d : ℕ) (z : ℂ) (y : Fin d → Chord) : ℂ :=
  ccgProductFor (ccgH q) q d z y

/-- The fixed-point equation `(H-def)` for the selected CCG function. -/
theorem ccgH_fixedPoint
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (z : ℂ) (x : Chord) (hz : z ∈ ccgDisk)
    (hx : IsPaperChord x) :
    ccgH q z x =
      z + z * ∑' d : ℕ,
        if d = 0 then 0 else
          (Nat.factorial d : ℂ)⁻¹ *
            ∫ y : Fin d → Chord,
              (∏ i : Fin d, chordKernel x (y i)) * ccgProduct q d z y
            ∂(MeasureTheory.Measure.pi (fun _ : Fin d => chordMeasure)) := by
  exact (ccgH_isCCG q hq hqEven).1 z x hz hx

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

/-- The preprint's formula, defined away from the removable singularity at zero. -/
noncomputable def paperClosedFormulaC (q : ℕ) (β : ℝ) (z : ℂ) : ℂ :=
  ((rho q β : ℂ)⁻¹) *
    (ccgR q ((rho q β : ℂ) * z) -
      ((q - 1 : ℕ) : ℂ) * ccgE q ((rho q β : ℂ) * z))

/-- The total closed formula with its removable value at `β = 0`. -/
noncomputable def closedFormulaC (q : ℕ) (β : ℝ) (z : ℂ) : ℂ :=
  if β = 0 then z else paperClosedFormulaC q β z

/-- Real restriction of the total closed formula. -/
noncomputable def closedFormulaR (q : ℕ) (β t : ℝ) : ℝ :=
  (closedFormulaC q β (t : ℂ)).re

/-- Real restriction of the literal nonzero-temperature formula. -/
noncomputable def paperClosedFormulaR (q : ℕ) (β t : ℝ) : ℝ :=
  (paperClosedFormulaC q β (t : ℂ)).re

/-- Away from zero, the total formula is the literal formula printed in the paper. -/
theorem closedFormulaC_eq_paperClosedFormulaC
    (q : ℕ) (β : ℝ) (hβ0 : β ≠ 0) (z : ℂ) :
    closedFormulaC q β z = paperClosedFormulaC q β z := by
  simp [closedFormulaC, hβ0]

/-! ## High-temperature threshold and stationary point -/

/-- The analytic, CCG, stationary-point, and asymptotic properties required of
a common high-temperature threshold. -/
def IsHighTemperatureThreshold (q : ℕ) (b : ℝ) : Prop :=
  0 < b ∧
    (2 ≤ q → Even q → ∀ β : ℝ, |β| ≤ b →
      AnalyticOnNhd ℂ (phiC q β) (Metric.closedBall 0 2) ∧
      (∀ z : ℂ, ‖z‖ ≤ 2 → phiC q β z = closedFormulaC q β z) ∧
      (∃! t : ℝ,
          t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) ∧
            (t : ℂ) * deriv (phiC q β) (t : ℂ) = 1) ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) →
        (t : ℂ) * deriv (phiC q β) (t : ℂ) = 1 →
        Tendsto
          (fun k => annealedPressure (admissibleSize q k) q β)
          atTop
          (𝓝 (phiR q β t - 1 - Real.log t)))

/-- Existence of a high-temperature window. -/
theorem exists_betaStar (q : ℕ) :
    ∃ b : ℝ, IsHighTemperatureThreshold q b := by
  sorry

/-- A high-temperature threshold depending only on `q`. -/
noncomputable def betaStar (q : ℕ) : ℝ :=
  Classical.choose (exists_betaStar q)

theorem betaStar_spec (q : ℕ) :
    IsHighTemperatureThreshold q (betaStar q) :=
  Classical.choose_spec (exists_betaStar q)

theorem betaStar_pos (q : ℕ) : 0 < betaStar q :=
  (betaStar_spec q).1

/-- The stationary point `t*` selected in `(1/2,3/2)`. -/
noncomputable def tStar (q : ℕ) (β : ℝ) : ℝ :=
  if h : 2 ≤ q ∧ Even q ∧ |β| ≤ betaStar q then
    Classical.choose (((betaStar_spec q).2 h.1 h.2.1 β h.2.2).2.2.1)
  else
    1

theorem phiC_analyticOn
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    AnalyticOnNhd ℂ (phiC q β) (Metric.closedBall 0 2) := by
  exact ((betaStar_spec q).2 hq hqEven β hβ).1

theorem tStar_mem_Ioo
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    tStar q β ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) := by
  rw [tStar, dif_pos ⟨hq, hqEven, hβ⟩]
  exact
    (Classical.choose_spec
      (((betaStar_spec q).2 hq hqEven β hβ).2.2.1)).1.1

theorem tStar_stationary
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    (tStar q β : ℂ) * deriv (phiC q β) (tStar q β : ℂ) = 1 := by
  rw [tStar, dif_pos ⟨hq, hqEven, hβ⟩]
  exact
    (Classical.choose_spec
      (((betaStar_spec q).2 hq hqEven β hβ).2.2.1)).1.2

theorem tStar_unique
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β t : ℝ) (hβ : |β| ≤ betaStar q)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ))
    (hstationary : (t : ℂ) * deriv (phiC q β) (t : ℂ) = 1) :
    t = tStar q β := by
  rw [tStar, dif_pos ⟨hq, hqEven, hβ⟩]
  exact
    (Classical.choose_spec
      (((betaStar_spec q).2 hq hqEven β hβ).2.2.1)).2 t ⟨ht, hstationary⟩

/-- The hypertree series equals the total CCG expression in the high-temperature disk. -/
theorem phiC_eq_closedFormulaC
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    phiC q β z = closedFormulaC q β z := by
  exact ((betaStar_spec q).2 hq hqEven β hβ).2.1 z hz

/-- The tree series equals the literal formula for nonzero small temperature. -/
theorem phiC_eq_paperClosedFormulaC
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ betaStar q)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    phiC q β z = paperClosedFormulaC q β z := by
  calc
    phiC q β z = closedFormulaC q β z :=
      phiC_eq_closedFormulaC q hq hqEven β hβ z hz
    _ = paperClosedFormulaC q β z :=
      closedFormulaC_eq_paperClosedFormulaC q β hβ0 z

/-- The literal closed formula is real on real inputs in its valid disk. -/
theorem paperClosedFormulaC_real
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ betaStar q)
    (t : ℝ) (ht : |t| ≤ 2) :
    (paperClosedFormulaC q β (t : ℂ)).im = 0 := by
  have hz : ‖(t : ℂ)‖ ≤ 2 := by simpa using ht
  calc
    (paperClosedFormulaC q β (t : ℂ)).im = (phiC q β (t : ℂ)).im := by
      rw [phiC_eq_paperClosedFormulaC q hq hqEven β hβ0 hβ (t : ℂ) hz]
    _ = 0 := phiC_real_of_real q β t

/-! ## Main limit theorems -/

/-- Pressure form: `lim N⁻¹ log E[Z_{N,q}(β)]`. -/
theorem annealed_pressure_limit
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q β)
      atTop
      (𝓝 (phiR q β (tStar q β) - 1 - Real.log (tStar q β))) := by
  exact
    ((betaStar_spec q).2 hq hqEven β hβ).2.2.2
      (tStar q β) (tStar_mem_Ioo q hq hqEven β hβ)
      (tStar_stationary q hq hqEven β hβ)

/-- Pressure limit written with the total CCG formula. -/
theorem annealed_pressure_limit_closedFormula
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ : |β| ≤ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q β)
      atTop
      (𝓝 (closedFormulaR q β (tStar q β) - 1 -
        Real.log (tStar q β))) := by
  have ht := tStar_mem_Ioo q hq hqEven β hβ
  have habs : |tStar q β| ≤ 2 := by
    rw [abs_of_pos (by linarith [ht.1])]
    linarith [ht.2]
  have hz : ‖(tStar q β : ℂ)‖ ≤ 2 := by simpa using habs
  have hformula := congrArg Complex.re
    (phiC_eq_closedFormulaC q hq hqEven β hβ (tStar q β : ℂ) hz)
  simpa only [phiR, closedFormulaR, hformula] using
    annealed_pressure_limit q hq hqEven β hβ

/-- Pressure limit using the literal formula printed in the preprint. -/
theorem annealed_pressure_limit_paperFormula
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q)
    (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q β)
      atTop
      (𝓝 (paperClosedFormulaR q β (tStar q β) - 1 -
        Real.log (tStar q β))) := by
  simpa [closedFormulaR, paperClosedFormulaR, closedFormulaC, hβ0] using
    annealed_pressure_limit_closedFormula q hq hqEven β hβ

/-- Existential pressure statement for `lim N⁻¹ log E[Z_{N,q}(β)]`. -/
theorem main_pressure_result
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, |β| ≤ β₀ →
        Tendsto
          (fun k => annealedPressure (admissibleSize q k) q β)
          atTop
          (𝓝 (closedFormulaR q β (tStar q β) - 1 -
            Real.log (tStar q β))) := by
  refine ⟨betaStar q, betaStar_pos q, ?_⟩
  intro β hβ
  exact annealed_pressure_limit_closedFormula q hq hqEven β hβ

/-- Theorem `theorem:main-result` of the preprint. -/
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
  have hp := annealed_pressure_limit_paperFormula q hq hqEven β hβ0 hβ
  have hfun :
      (fun k =>
        annealedFreeEnergy (admissibleSize q k) q β /
          (admissibleSize q k : ℝ)) =
      (fun k => annealedPressure (admissibleSize q k) q β / β) := by
    funext k
    simp only [annealedFreeEnergy, annealedPressure]
    ring
  rw [hfun]
  exact hp.div_const β

/-- Existential wrapper matching the quantifier order in the preprint. -/
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
  refine ⟨betaStar q, betaStar_pos q, ?_⟩
  intro β hβ0 hβ
  exact annealed_freeEnergy_density_limit q hq hqEven β hβ0 hβ

end AnnealedFE
end SYK
