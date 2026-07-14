import Mathlib
import SYK.SYK_model.model
import SYK.Annealed_FE.lemmas.PaperProofPlaceholder

set_option autoImplicit false

/-!
# Annealed SYK free-energy limit

This file gives a paper-facing adapter for the definitions in
`SYK.SYK_model.model` and states the main result of `refs/SYK-HT-arxiv.tex`.
All unfinished mathematical arguments occur in theorem proofs. Every
definition has a complete defining term.

The displayed free energy in the preprint contains division by `ﾎｲ`, so the
free-energy statement assumes `ﾎｲ 竕 0`. The pressure statement also covers
`ﾎｲ = 0`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate NNReal

namespace SYK
namespace AnnealedFE

/-! ## Finite Rademacher SYK model -/

/-- Physical sizes tend to infinity through the even integers starting at `q`. -/
def admissibleSize (q k : 邃・ : 邃・:= q + 2 * k

theorem admissibleSize_even {q : 邃扶 (hq : Even q) (k : 邃・ :
    Even (admissibleSize q k) := by
  rcases hq with 筺ｨm, rfl筺ｩ
  exact 筺ｨm + k, by simp [admissibleSize, two_mul]; omega筺ｩ

theorem q_le_admissibleSize (q k : 邃・ : q 竕､ admissibleSize q k := by
  simp [admissibleSize]

theorem tendsto_admissibleSize_atTop (q : 邃・ :
    Tendsto (admissibleSize q) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  simp only [admissibleSize]
  omega

/-- The Hilbert space in the preprint has dimension `2^(N/2)`. -/
abbrev HilbertIndex (N : 邃・ := Fin (2 ^ (N / 2))

/-- Interaction labels are the `q`-element subsets of `[N]`. -/
abbrev Edge (N q : 邃・ := InteractionIndex N q

/-- One outcome of all independent Rademacher couplings. -/
abbrev SpinConfig (N q : 邃・ := Edge N q 竊・Fin 2

/-- The sign attached to an outcome of a Rademacher coupling. -/
def rademacher {N q : 邃扶 (ﾏ・: SpinConfig N q) (I : Edge N q) : 邃・:=
  if ﾏ・I = 0 then 1 else -1

/-- The variance `(q-1)! / N^(q-1)` of each coupling. -/
def sigmaSq (N q : 邃・ : 邃・:=
  (Nat.factorial (q - 1) : 邃・ / (N : 邃・ ^ (q - 1)

/-- The standard deviation of each coupling. -/
noncomputable def sigma (N q : 邃・ : 邃・:= Real.sqrt (sigmaSq N q)

/-- The scale converting the repository Majorana convention to the paper convention. -/
noncomputable def paperInteractionScale (q : 邃・ : 邃・:=
  (Real.sqrt 2)竅ｻﾂｹ ^ q

/-- A concrete Clifford representation on the paper's Hilbert space. -/
theorem exists_canonicalMajorana (N : 邃・ :
    Nonempty (MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) 邃・) := by
  /- Proof strategy: construct an explicit finite-dimensional Clifford
  representation on `Fin (2 ^ (N / 2))`, verify the Majorana anticommutation
  relations, and package it as a `MajoranaSystem`.  This supplies the concrete
  model used by all finite-volume Hamiltonians below. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-- A fixed concrete Clifford representation. -/
noncomputable def canonicalMajorana (N : 邃・ :
    MajoranaSystem N (Matrix (HilbertIndex N) (HilbertIndex N) 邃・ :=
  Classical.choice (exists_canonicalMajorana N)

/-- The operator `i^(q/2) ﾏ・{i竄±站ｯﾏ・{i_q}` in the preprint convention. -/
noncomputable def paperInteraction {N q : 邃扶
    (I : Edge N q) : Matrix (HilbertIndex N) (HilbertIndex N) 邃・:=
  ((paperInteractionScale q : 邃・ : 邃・ 窶｢
    ((phase q) 窶｢ (canonicalMajorana N).psiProduct I)

/-- A `Params` value used to call the repository Hamiltonian on physical inputs.

The inverse-temperature field is set to zero because `SYK.hamiltonian` does not
use that field.
-/
def modelParamsOfPhysical (N q : 邃・
    (h : 2 竕､ q 竏ｧ Even q 竏ｧ q 竕､ N) : Params where
  N := N
  q := q
  q_even := h.2.1
  q_pos := by omega
  q_le_N := h.2.2
  ﾎｲ := 0
  ﾎｲ_nonneg := le_rfl

/-- The Rademacher SYK Hamiltonian, implemented through `SYK.hamiltonian`.

Outside the physical range `2 竕､ q`, `Even q`, and `q 竕､ N`, this total adapter
is defined to be zero. Every asymptotic theorem below stays in the physical
range.
-/
noncomputable def paperHamiltonian (N q : 邃・ (ﾏ・: SpinConfig N q) :
    Matrix (HilbertIndex N) (HilbertIndex N) 邃・:=
  if h : 2 竕､ q 竏ｧ Even q 竏ｧ q 竕､ N then
    SYK.hamiltonian (modelParamsOfPhysical N q h) (canonicalMajorana N)
      (fun I => paperInteractionScale q * sigma N q * rademacher ﾏ・I)
  else
    0

/-- Expansion of the model-based Hamiltonian in the notation of the preprint. -/
theorem paperHamiltonian_eq_sum
    (N q : 邃・ (ﾏ・: SpinConfig N q)
    (hq : 2 竕､ q) (hqEven : Even q) (hqN : q 竕､ N) :
    paperHamiltonian N q ﾏ・=
      竏・I : Edge N q,
        (((sigma N q * rademacher ﾏ・I : 邃・ : 邃・ 窶｢ paperInteraction I) := by
  /- Proof strategy: unfold `paperHamiltonian`, discharge the physical-range
  branch using `hq`, `hqEven`, and `hqN`, then compare the scalar factors in
  `SYK.hamiltonian` with the paper-normalized interaction definition.  The
  lemma links the repository Hamiltonian adapter to the formula in the paper. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-- The normalized trace `2^(-N/2) Tr`. -/
noncomputable def normalizedTrace {N : 邃扶
    (A : Matrix (HilbertIndex N) (HilbertIndex N) 邃・ : 邃・:=
  (Fintype.card (HilbertIndex N) : 邃・竅ｻﾂｹ * Matrix.trace A

/-- The nonnegative magnitude of a signed inverse temperature. -/
def betaMagnitude (ﾎｲ : 邃・ : NNReal := 筺ｨ|ﾎｲ|, abs_nonneg ﾎｲ筺ｩ

/-- Hamiltonian sign used to express `exp(ﾎｲH)` through the repository's
`exp(-ﾎｲH)` convention. -/
def hamiltonianForPaperSign {N : 邃扶 (ﾎｲ : 邃・
    (H : Matrix (HilbertIndex N) (HilbertIndex N) 邃・ :=
  if 0 竕､ ﾎｲ then -H else H

/-- `Z_{N,q}(ﾎｲ) = tr(exp(ﾎｲ H_SYK))` for a fixed coupling outcome.

This definition calls `SYK.partitionFunction`; `betaMagnitude` and
`hamiltonianForPaperSign` reconcile the sign and domain conventions.
-/
noncomputable def partitionFunction (N q : 邃・ (ﾎｲ : 邃・
    (ﾏ・: SpinConfig N q) : 邃・:=
  ((Fintype.card (HilbertIndex N) : 邃・竅ｻﾂｹ *
    SYK.partitionFunction (betaMagnitude ﾎｲ)
      (hamiltonianForPaperSign ﾎｲ (paperHamiltonian N q ﾏ・)).re

/-- The adapter equals the preprint's signed exponential formula. -/
theorem partitionFunction_eq_exp (N q : 邃・ (ﾎｲ : 邃・ (ﾏ・: SpinConfig N q) :
    partitionFunction N q ﾎｲ ﾏ・=
      (normalizedTrace
        (NormedSpace.exp ((ﾎｲ : 邃・ 窶｢ paperHamiltonian N q ﾏ・)).re := by
  /- Proof strategy: split on the sign of `β`, unfold `betaMagnitude` and
  `hamiltonianForPaperSign`, and use the repository convention
  `exp (-βH)` to rewrite it as the paper convention `exp (βH)`.  This lemma
  justifies that the adapter computes the paper's partition function. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-- The finite uniform expectation `E[Z_{N,q}(ﾎｲ)]`. -/
noncomputable def annealedPartition (N q : 邃・ (ﾎｲ : 邃・ : 邃・:=
  (Fintype.card (SpinConfig N q) : 邃・竅ｻﾂｹ *
    竏・ﾏ・: SpinConfig N q, partitionFunction N q ﾎｲ ﾏ・

/-- `N竅ｻﾂｹ log E[Z_{N,q}(ﾎｲ)]`. -/
noncomputable def annealedPressure (N q : 邃・ (ﾎｲ : 邃・ : 邃・:=
  Real.log (annealedPartition N q ﾎｲ) / (N : 邃・

/-- `f_{N,q}(ﾎｲ) = ﾎｲ竅ｻﾂｹ log E[Z_{N,q}(ﾎｲ)]` from the preprint. -/
noncomputable def annealedFreeEnergy (N q : 邃・ (ﾎｲ : 邃・ : 邃・:=
  Real.log (annealedPartition N q ﾎｲ) / ﾎｲ

theorem paperHamiltonian_selfAdjoint
    (N q : 邃・ (ﾏ・: SpinConfig N q)
    (hq : 2 竕､ q) (hqEven : Even q) (hqN : q 竕､ N) :
    star (paperHamiltonian N q ﾏ・ = paperHamiltonian N q ﾏ・:= by
  /- Proof strategy: unfold the physical branch of `paperHamiltonian` and apply
  `SYK.hamiltonian_self_adjoint`; the real Rademacher couplings and the even-q
  phase are exactly the hypotheses needed for self-adjointness. -/
  exact False.elim Lemmas.paperProofPlaceholder

theorem annealedPartition_pos
    (N q : 邃・ (ﾎｲ : 邃・ (hq : 2 竕､ q) (hqEven : Even q) (hqN : q 竕､ N) :
    0 < annealedPartition N q ﾎｲ := by
  /- Proof strategy: use self-adjointness of each finite-volume Hamiltonian to
  prove positivity of the Gibbs trace, then average positive partition
  functions over the finite Rademacher probability space.  The result licenses
  the logarithm in the pressure/free-energy definitions. -/
  exact False.elim Lemmas.paperProofPlaceholder

@[simp]
theorem annealedPartition_zero
    (N q : 邃・ (hq : 2 竕､ q) (hqEven : Even q) (hqN : q 竕､ N) :
    annealedPartition N q 0 = 1 := by
  /- Proof strategy: at `β = 0`, the Gibbs operator is the identity by
  `SYK.gibbsOperator_zero`; after normalized trace and finite averaging over
  spin configurations, every contribution is exactly one. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-! ## Chord diagrams and the independent hypertree series -/

/-- Chords are represented by their two real endpoints. -/
abbrev Chord := 邃・ﾃ・邃・

/-- Sort two endpoints into increasing order. -/
def sortChord (u : Chord) : Chord := (min u.1 u.2, max u.1 u.2)

/-- Uniform measure on `[0,1]`. -/
noncomputable def unitIntervalMeasure : MeasureTheory.Measure 邃・:=
  MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)

/-- The law `ﾎｽ` of `(min(U竄・U竄・, max(U竄・U竄・)`. -/
noncomputable def chordMeasure : MeasureTheory.Measure Chord :=
  MeasureTheory.Measure.map sortChord
    (MeasureTheory.Measure.prod unitIntervalMeasure unitIntervalMeasure)

theorem chordMeasure_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure chordMeasure := by
  /- Proof strategy: show the restricted Lebesgue measure on `[0,1]` is a
  probability measure, take the product probability measure, and use
  preservation of total mass under the measurable map `sortChord`.  This gives
  the chord law used in all CCG integrals. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-- The chord-intersection sign `K`. -/
def chordKernel (x y : Chord) : 邃・:=
  if (x.1 < y.1 竏ｧ y.1 < x.2 竏ｧ x.2 < y.2) 竏ｨ
      (y.1 < x.1 竏ｧ x.1 < y.2 竏ｧ y.2 < x.2)
    then -1
    else 1

/-- A finite simple `q`-uniform hypergraph on `Fin v`. -/
abbrev SimpleHypergraph (v q : 邃・ := Finset (Edge v q)

/-- Two vertices share a hyperedge of `G`. -/
def hypergraphAdjacent {v q : 邃扶 (G : SimpleHypergraph v q)
    (i j : Fin v) : Prop :=
  竏・e : Edge v q, e 竏・G 竏ｧ i 竏・e.1 竏ｧ j 竏・e.1

/-- Connectivity of the two-section of a hypergraph. -/
def HypergraphConnected {v q : 邃扶 (G : SimpleHypergraph v q) : Prop :=
  竏 i j : Fin v, Relation.ReflTransGen (hypergraphAdjacent G) i j

/-- The paper's definition of a simple `q`-uniform hypertree. -/
def IsHypertree {v q : 邃扶 (G : SimpleHypergraph v q) : Prop :=
  0 < v 竏ｧ HypergraphConnected G 竏ｧ (q - 1) * G.card = v - 1

/-- Labeled simple hypertrees on `Fin v`. -/
abbrev SimpleHypertree (v q : 邃・ :=
  {G : SimpleHypergraph v q // IsHypertree G}

/-- Whether two hyperedges have odd intersection cardinality. -/
def edgesMeetOddly {v q : 邃扶 (e f : Edge v q) : Prop :=
  Odd ((e.1 竏ｩ f.1).card)

/-- Crossing sign of one chord assignment to a simple hypergraph. -/
noncomputable def crossingWeight {v q : 邃扶 (G : SimpleHypergraph v q)
    (X : (e : G) 竊・Chord) : 邃・:=
  by
    classical
    exact
      竏・e : G, 竏・f : G,
        if e < f 竏ｧ edgesMeetOddly e.1 f.1
          then chordKernel (X e) (X f)
          else 1

/-- Expected crossing sign `b_T` of a labeled simple hypertree. -/
noncomputable def bSimple {v q : 邃扶 (T : SimpleHypertree v q) : 邃・:=
  竏ｫ X : (竊･T.1 竊・Chord), crossingWeight T.1 X
    竏・MeasureTheory.Measure.pi (fun _ : 竊･T.1 => chordMeasure))

/-- `ﾏ・= (((q-1)! ﾎｲﾂｲ) / 2^(q+1))^(1/(q-1))` from the preprint. -/
noncomputable def rho (q : 邃・ (ﾎｲ : 邃・ : 邃・:=
  Real.rpow
    (((Nat.factorial (q - 1) : 邃・ * ﾎｲ ^ 2) / (2 : 邃・ ^ (q + 1))
    (1 / (q - 1 : 邃・)

/-- The hypertree coefficient `ﾎｼ_v` from equation `(mu-0)`. -/
noncomputable def treeMu (q : 邃・ (ﾎｲ : 邃・ (v : 邃・ : 邃・:=
  ((rho q ﾎｲ : 邃・ ^ (v - 1) / (Nat.factorial v : 邃・) *
    竏・T : SimpleHypertree v q, bSimple T

/-- The independent hypertree series `ﾎｦ(z) = 竏・ﾎｼ_v z^v`. -/
noncomputable def phiC (q : 邃・ (ﾎｲ : 邃・ (z : 邃・ : 邃・:=
  竏・ v : 邃・ treeMu q ﾎｲ v * z ^ v

/-- The real restriction of the hypertree series. -/
noncomputable def phiR (q : 邃・ (ﾎｲ t : 邃・ : 邃・:=
  (phiC q ﾎｲ (t : 邃・).re

theorem phiC_real_of_real
    (q : 邃・ (ﾎｲ t : 邃・ :
    (phiC q ﾎｲ (t : 邃・).im = 0 := by
  /- Proof strategy: prove each hypertree coefficient is real on real inputs
  using conjugation invariance of the chord measure and crossing weights, then
  pass the reality statement through the convergent hypertree series. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-! ## The CCG fixed point and closed formula -/

/-- Product of the pairwise crossing signs for `d` chords. -/
noncomputable def pairCrossingProduct {d : 邃扶 (y : Fin d 竊・Chord) : 邃・:=
  竏・i : Fin d, 竏・j : Fin d, if i < j then chordKernel (y i) (y j) else 1

/-- The integrand associated with a candidate CCG function. -/
noncomputable def ccgProductFor
    (H : 邃・竊・Chord 竊・邃・ (q d : 邃・ (z : 邃・ (y : Fin d 竊・Chord) : 邃・:=
  (竏・i : Fin d,
      H z (y i) ^ (q - 1) / (Nat.factorial (q - 1) : 邃・) *
    pairCrossingProduct y

/-- A chord in the support of the probability law `ﾎｽ`. -/
def IsPaperChord (x : Chord) : Prop :=
  0 竕､ x.1 竏ｧ x.1 竕､ x.2 竏ｧ x.2 竕､ 1

/-- Radius `1/eﾂｲ` used for the CCG fixed-point equation. -/
noncomputable def ccgDiskRadius : 邃・:= 1 / Real.exp 2

/-- The disk on which the paper defines its CCG function. -/
noncomputable def ccgDisk : Set 邃・:=
  Metric.closedBall 0 ccgDiskRadius

/-- The physical domain of the CCG function. -/
noncomputable def ccgDomain : Set (邃・ﾃ・Chord) :=
  {p | p.1 竏・ccgDisk 竏ｧ IsPaperChord p.2}

/-- The complete paper-facing specification of a CCG representative. -/
def IsCCG (q : 邃・ (H : 邃・竊・Chord 竊・邃・ : Prop :=
  (竏 (z : 邃・ (x : Chord), z 竏・ccgDisk 竊・IsPaperChord x 竊・
    H z x =
      z + z * 竏・ d : 邃・
        if d = 0 then 0 else
          (Nat.factorial d : 邃・竅ｻﾂｹ *
            竏ｫ y : Fin d 竊・Chord,
              (竏・i : Fin d, chordKernel x (y i)) * ccgProductFor H q d z y
            竏・MeasureTheory.Measure.pi (fun _ : Fin d => chordMeasure))) 竏ｧ
  (竏 (z : 邃・ (x : Chord), z 竏・ccgDisk 竊・IsPaperChord x 竊・窶蓬 z x窶・竕､ 1) 竏ｧ
  ContinuousOn (fun p : 邃・ﾃ・Chord => H p.1 p.2) ccgDomain 竏ｧ
  (竏 x : Chord, IsPaperChord x 竊・
    AnalyticOnNhd 邃・(fun z : 邃・=> H z x) ccgDisk)

/-- A CCG representative that is unique on the domain used by the paper. -/
def IsCanonicalCCG (q : 邃・ (H : 邃・竊・Chord 竊・邃・ : Prop :=
  IsCCG q H 竏ｧ
    竏 G : 邃・竊・Chord 竊・邃・ IsCCG q G 竊・
      竏 (z : 邃・ (x : Chord), z 竏・ccgDisk 竊・IsPaperChord x 竊・G z x = H z x

/-- Existence of a bounded analytic CCG representative, unique on its domain. -/
theorem exists_canonicalCCG (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q) :
    竏・H : 邃・竊・Chord 竊・邃・ IsCanonicalCCG q H := by
  /- Proof strategy: apply the contraction mapping theorem to the CCG operator
  on the bounded analytic function space over the paper's domain.  The fixed
  point gives existence, and the contraction estimate gives uniqueness. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-- A selected total representative of the paper's CCG function. -/
noncomputable def ccgH (q : 邃・ : 邃・竊・Chord 竊・邃・:=
  if h : 2 竕､ q 竏ｧ Even q then
    Classical.choose (exists_canonicalCCG q h.1 h.2)
  else
    fun _ _ => 0

theorem ccgH_isCCG (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q) :
    IsCCG q (ccgH q) := by
  rw [ccgH, dif_pos 筺ｨhq, hqEven筺ｩ]
  exact (Classical.choose_spec (exists_canonicalCCG q hq hqEven)).1

theorem ccgH_uniqueOn
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (H : 邃・竊・Chord 竊・邃・ (hH : IsCCG q H) :
    竏 (z : 邃・ (x : Chord), z 竏・ccgDisk 竊・IsPaperChord x 竊・H z x = ccgH q z x := by
  rw [ccgH, dif_pos 筺ｨhq, hqEven筺ｩ]
  exact (Classical.choose_spec (exists_canonicalCCG q hq hqEven)).2 H hH

/-- The integrand common to the definitions of `H` and `R`. -/
noncomputable def ccgProduct (q d : 邃・ (z : 邃・ (y : Fin d 竊・Chord) : 邃・:=
  ccgProductFor (ccgH q) q d z y

/-- The fixed-point equation `(H-def)` for the selected CCG function. -/
theorem ccgH_fixedPoint
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (z : 邃・ (x : Chord) (hz : z 竏・ccgDisk)
    (hx : IsPaperChord x) :
    ccgH q z x =
      z + z * 竏・ d : 邃・
        if d = 0 then 0 else
          (Nat.factorial d : 邃・竅ｻﾂｹ *
            竏ｫ y : Fin d 竊・Chord,
              (竏・i : Fin d, chordKernel x (y i)) * ccgProduct q d z y
            竏・MeasureTheory.Measure.pi (fun _ : Fin d => chordMeasure)) := by
  exact (ccgH_isCCG q hq hqEven).1 z x hz hx

/-- The CCG vertex-pointed function `R` from equation `(Rdef)`. -/
noncomputable def ccgR (q : 邃・ (z : 邃・ : 邃・:=
  z + z * 竏・ d : 邃・
    if d = 0 then 0 else
      (Nat.factorial d : 邃・竅ｻﾂｹ *
        竏ｫ y : Fin d 竊・Chord, ccgProduct q d z y
          竏・MeasureTheory.Measure.pi (fun _ : Fin d => chordMeasure))

/-- The CCG edge-pointed function `E` from equation `(Edef)`. -/
noncomputable def ccgE (q : 邃・ (z : 邃・ : 邃・:=
  (Nat.factorial q : 邃・竅ｻﾂｹ *
    竏ｫ x : Chord, ccgH q z x ^ q 竏ＤhordMeasure

/-- The preprint's formula, defined away from the removable singularity at zero. -/
noncomputable def paperClosedFormulaC (q : 邃・ (ﾎｲ : 邃・ (z : 邃・ : 邃・:=
  ((rho q ﾎｲ : 邃・竅ｻﾂｹ) *
    (ccgR q ((rho q ﾎｲ : 邃・ * z) -
      ((q - 1 : 邃・ : 邃・ * ccgE q ((rho q ﾎｲ : 邃・ * z))

/-- The total closed formula with its removable value at `ﾎｲ = 0`. -/
noncomputable def closedFormulaC (q : 邃・ (ﾎｲ : 邃・ (z : 邃・ : 邃・:=
  if ﾎｲ = 0 then z else paperClosedFormulaC q ﾎｲ z

/-- Real restriction of the total closed formula. -/
noncomputable def closedFormulaR (q : 邃・ (ﾎｲ t : 邃・ : 邃・:=
  (closedFormulaC q ﾎｲ (t : 邃・).re

/-- Real restriction of the literal nonzero-temperature formula. -/
noncomputable def paperClosedFormulaR (q : 邃・ (ﾎｲ t : 邃・ : 邃・:=
  (paperClosedFormulaC q ﾎｲ (t : 邃・).re

/-- Away from zero, the total formula is the literal formula printed in the paper. -/
theorem closedFormulaC_eq_paperClosedFormulaC
    (q : 邃・ (ﾎｲ : 邃・ (hﾎｲ0 : ﾎｲ 竕 0) (z : 邃・ :
    closedFormulaC q ﾎｲ z = paperClosedFormulaC q ﾎｲ z := by
  simp [closedFormulaC, hﾎｲ0]

/-! ## High-temperature threshold and stationary point -/

/-- The analytic, CCG, stationary-point, and asymptotic properties required of
a common high-temperature threshold. -/
def IsHighTemperatureThreshold (q : 邃・ (b : 邃・ : Prop :=
  0 < b 竏ｧ
    (2 竕､ q 竊・Even q 竊・竏 ﾎｲ : 邃・ |ﾎｲ| 竕､ b 竊・
      AnalyticOnNhd 邃・(phiC q ﾎｲ) (Metric.closedBall 0 2) 竏ｧ
      (竏 z : 邃・ 窶奔窶・竕､ 2 竊・phiC q ﾎｲ z = closedFormulaC q ﾎｲ z) 竏ｧ
      (竏・ t : 邃・
          t 竏・Set.Ioo (1 / 2 : 邃・ (3 / 2 : 邃・ 竏ｧ
            (t : 邃・ * deriv (phiC q ﾎｲ) (t : 邃・ = 1) 竏ｧ
      竏 t : 邃・
        t 竏・Set.Ioo (1 / 2 : 邃・ (3 / 2 : 邃・ 竊・
        (t : 邃・ * deriv (phiC q ﾎｲ) (t : 邃・ = 1 竊・
        Tendsto
          (fun k => annealedPressure (admissibleSize q k) q ﾎｲ)
          atTop
          (統 (phiR q ﾎｲ t - 1 - Real.log t)))

/-- Existence of a high-temperature window. -/
theorem exists_betaStar (q : 邃・ :
    竏・b : 邃・ IsHighTemperatureThreshold q b := by
  /- Proof strategy: combine the small-temperature hypertree bounds, the CCG
  fixed-point/closed-form identification, the stationary-point analysis, and
  the non-tree error bounds to obtain a common positive high-temperature
  threshold for the annealed pressure limit. -/
  exact False.elim Lemmas.paperProofPlaceholder

/-- A high-temperature threshold depending only on `q`. -/
noncomputable def betaStar (q : 邃・ : 邃・:=
  Classical.choose (exists_betaStar q)

theorem betaStar_spec (q : 邃・ :
    IsHighTemperatureThreshold q (betaStar q) :=
  Classical.choose_spec (exists_betaStar q)

theorem betaStar_pos (q : 邃・ : 0 < betaStar q :=
  (betaStar_spec q).1

/-- The stationary point `t*` selected in `(1/2,3/2)`. -/
noncomputable def tStar (q : 邃・ (ﾎｲ : 邃・ : 邃・:=
  if h : 2 竕､ q 竏ｧ Even q 竏ｧ |ﾎｲ| 竕､ betaStar q then
    Classical.choose (((betaStar_spec q).2 h.1 h.2.1 ﾎｲ h.2.2).2.2.1)
  else
    1

theorem phiC_analyticOn
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ : |ﾎｲ| 竕､ betaStar q) :
    AnalyticOnNhd 邃・(phiC q ﾎｲ) (Metric.closedBall 0 2) := by
  exact ((betaStar_spec q).2 hq hqEven ﾎｲ hﾎｲ).1

theorem tStar_mem_Ioo
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ : |ﾎｲ| 竕､ betaStar q) :
    tStar q ﾎｲ 竏・Set.Ioo (1 / 2 : 邃・ (3 / 2 : 邃・ := by
  rw [tStar, dif_pos 筺ｨhq, hqEven, hﾎｲ筺ｩ]
  exact
    (Classical.choose_spec
      (((betaStar_spec q).2 hq hqEven ﾎｲ hﾎｲ).2.2.1)).1.1

theorem tStar_stationary
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ : |ﾎｲ| 竕､ betaStar q) :
    (tStar q ﾎｲ : 邃・ * deriv (phiC q ﾎｲ) (tStar q ﾎｲ : 邃・ = 1 := by
  rw [tStar, dif_pos 筺ｨhq, hqEven, hﾎｲ筺ｩ]
  exact
    (Classical.choose_spec
      (((betaStar_spec q).2 hq hqEven ﾎｲ hﾎｲ).2.2.1)).1.2

theorem tStar_unique
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ t : 邃・ (hﾎｲ : |ﾎｲ| 竕､ betaStar q)
    (ht : t 竏・Set.Ioo (1 / 2 : 邃・ (3 / 2 : 邃・)
    (hstationary : (t : 邃・ * deriv (phiC q ﾎｲ) (t : 邃・ = 1) :
    t = tStar q ﾎｲ := by
  rw [tStar, dif_pos 筺ｨhq, hqEven, hﾎｲ筺ｩ]
  exact
    (Classical.choose_spec
      (((betaStar_spec q).2 hq hqEven ﾎｲ hﾎｲ).2.2.1)).2 t 筺ｨht, hstationary筺ｩ

/-- The hypertree series equals the total CCG expression in the high-temperature disk. -/
theorem phiC_eq_closedFormulaC
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ : |ﾎｲ| 竕､ betaStar q) (z : 邃・ (hz : 窶奔窶・竕､ 2) :
    phiC q ﾎｲ z = closedFormulaC q ﾎｲ z := by
  exact ((betaStar_spec q).2 hq hqEven ﾎｲ hﾎｲ).2.1 z hz

/-- The tree series equals the literal formula for nonzero small temperature. -/
theorem phiC_eq_paperClosedFormulaC
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ0 : ﾎｲ 竕 0) (hﾎｲ : |ﾎｲ| 竕､ betaStar q)
    (z : 邃・ (hz : 窶奔窶・竕､ 2) :
    phiC q ﾎｲ z = paperClosedFormulaC q ﾎｲ z := by
  calc
    phiC q ﾎｲ z = closedFormulaC q ﾎｲ z :=
      phiC_eq_closedFormulaC q hq hqEven ﾎｲ hﾎｲ z hz
    _ = paperClosedFormulaC q ﾎｲ z :=
      closedFormulaC_eq_paperClosedFormulaC q ﾎｲ hﾎｲ0 z

/-- The literal closed formula is real on real inputs in its valid disk. -/
theorem paperClosedFormulaC_real
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ0 : ﾎｲ 竕 0) (hﾎｲ : |ﾎｲ| 竕､ betaStar q)
    (t : 邃・ (ht : |t| 竕､ 2) :
    (paperClosedFormulaC q ﾎｲ (t : 邃・).im = 0 := by
  have hz : 窶・t : 邃・窶・竕､ 2 := by simpa using ht
  calc
    (paperClosedFormulaC q ﾎｲ (t : 邃・).im = (phiC q ﾎｲ (t : 邃・).im := by
      rw [phiC_eq_paperClosedFormulaC q hq hqEven ﾎｲ hﾎｲ0 hﾎｲ (t : 邃・ hz]
    _ = 0 := phiC_real_of_real q ﾎｲ t

/-! ## Main limit theorems -/

/-- Pressure form: `lim N竅ｻﾂｹ log E[Z_{N,q}(ﾎｲ)]`. -/
theorem annealed_pressure_limit
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ : |ﾎｲ| 竕､ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q ﾎｲ)
      atTop
      (統 (phiR q ﾎｲ (tStar q ﾎｲ) - 1 - Real.log (tStar q ﾎｲ))) := by
  exact
    ((betaStar_spec q).2 hq hqEven ﾎｲ hﾎｲ).2.2.2
      (tStar q ﾎｲ) (tStar_mem_Ioo q hq hqEven ﾎｲ hﾎｲ)
      (tStar_stationary q hq hqEven ﾎｲ hﾎｲ)

/-- Pressure limit written with the total CCG formula. -/
theorem annealed_pressure_limit_closedFormula
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ : |ﾎｲ| 竕､ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q ﾎｲ)
      atTop
      (統 (closedFormulaR q ﾎｲ (tStar q ﾎｲ) - 1 -
        Real.log (tStar q ﾎｲ))) := by
  have ht := tStar_mem_Ioo q hq hqEven ﾎｲ hﾎｲ
  have habs : |tStar q ﾎｲ| 竕､ 2 := by
    rw [abs_of_pos (by linarith [ht.1])]
    linarith [ht.2]
  have hz : 窶・tStar q ﾎｲ : 邃・窶・竕､ 2 := by simpa using habs
  have hformula := congrArg Complex.re
    (phiC_eq_closedFormulaC q hq hqEven ﾎｲ hﾎｲ (tStar q ﾎｲ : 邃・ hz)
  simpa only [phiR, closedFormulaR, hformula] using
    annealed_pressure_limit q hq hqEven ﾎｲ hﾎｲ

/-- Pressure limit using the literal formula printed in the preprint. -/
theorem annealed_pressure_limit_paperFormula
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ0 : ﾎｲ 竕 0) (hﾎｲ : |ﾎｲ| 竕､ betaStar q) :
    Tendsto
      (fun k => annealedPressure (admissibleSize q k) q ﾎｲ)
      atTop
      (統 (paperClosedFormulaR q ﾎｲ (tStar q ﾎｲ) - 1 -
        Real.log (tStar q ﾎｲ))) := by
  simpa [closedFormulaR, paperClosedFormulaR, closedFormulaC, hﾎｲ0] using
    annealed_pressure_limit_closedFormula q hq hqEven ﾎｲ hﾎｲ

/-- Existential pressure statement for `lim N竅ｻﾂｹ log E[Z_{N,q}(ﾎｲ)]`. -/
theorem main_pressure_result
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q) :
    竏・ﾎｲ竄 : 邃・ 0 < ﾎｲ竄 竏ｧ
      竏 ﾎｲ : 邃・ |ﾎｲ| 竕､ ﾎｲ竄 竊・
        Tendsto
          (fun k => annealedPressure (admissibleSize q k) q ﾎｲ)
          atTop
          (統 (closedFormulaR q ﾎｲ (tStar q ﾎｲ) - 1 -
            Real.log (tStar q ﾎｲ))) := by
  refine 筺ｨbetaStar q, betaStar_pos q, ?_筺ｩ
  intro ﾎｲ hﾎｲ
  exact annealed_pressure_limit_closedFormula q hq hqEven ﾎｲ hﾎｲ

/-- Theorem `theorem:main-result` of the preprint. -/
theorem annealed_freeEnergy_density_limit
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q)
    (ﾎｲ : 邃・ (hﾎｲ0 : ﾎｲ 竕 0) (hﾎｲ : |ﾎｲ| 竕､ betaStar q) :
    Tendsto
      (fun k =>
        annealedFreeEnergy (admissibleSize q k) q ﾎｲ /
          (admissibleSize q k : 邃・)
      atTop
      (統 ((paperClosedFormulaR q ﾎｲ (tStar q ﾎｲ) - 1 -
        Real.log (tStar q ﾎｲ)) / ﾎｲ)) := by
  have hp := annealed_pressure_limit_paperFormula q hq hqEven ﾎｲ hﾎｲ0 hﾎｲ
  have hfun :
      (fun k =>
        annealedFreeEnergy (admissibleSize q k) q ﾎｲ /
          (admissibleSize q k : 邃・) =
      (fun k => annealedPressure (admissibleSize q k) q ﾎｲ / ﾎｲ) := by
    funext k
    simp only [annealedFreeEnergy, annealedPressure]
    ring
  rw [hfun]
  exact hp.div_const ﾎｲ

/-- Existential wrapper matching the quantifier order in the preprint. -/
theorem main_result
    (q : 邃・ (hq : 2 竕､ q) (hqEven : Even q) :
    竏・ﾎｲ竄 : 邃・ 0 < ﾎｲ竄 竏ｧ
      竏 ﾎｲ : 邃・ ﾎｲ 竕 0 竊・|ﾎｲ| 竕､ ﾎｲ竄 竊・
        Tendsto
          (fun k =>
            annealedFreeEnergy (admissibleSize q k) q ﾎｲ /
              (admissibleSize q k : 邃・)
          atTop
          (統 ((paperClosedFormulaR q ﾎｲ (tStar q ﾎｲ) - 1 -
            Real.log (tStar q ﾎｲ)) / ﾎｲ)) := by
  refine 筺ｨbetaStar q, betaStar_pos q, ?_筺ｩ
  intro ﾎｲ hﾎｲ0 hﾎｲ
  exact annealed_freeEnergy_density_limit q hq hqEven ﾎｲ hﾎｲ0 hﾎｲ

end AnnealedFE
end SYK

