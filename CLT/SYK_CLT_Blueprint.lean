/--
Lean blueprint for `CLT_for_SYK_v3.tex`.

This file is intentionally a blueprint, not a completed formalization.
The analytic, probabilistic, and operator-algebraic ingredients are represented
by predicates and axioms.  The point is to record the exact dependency graph of
the TeX proof and to provide names/targets for the Lean lemmas that should be
filled in later.

Suggested project layout when turning this into a real Lean development:

  SYK/Clifford.lean
    Majorana algebra, monomials psi_I, normalized trace, trace orthogonality,
    sign-gauge invariance.

  SYK/GaussianChaos.lean
    Gaussian product space, Hermite polynomials, homogeneous Wiener chaoses,
    Gaussian integration by parts, Malliavin derivative identities.

  SYK/MatrixDuhamel.lean
    Matrix exponential derivatives, Duhamel formula, Kubo covariance identity,
    log-partition derivative bounds.

  SYK/FiniteCounting.lean
    Even marked hypergraph counting and connected parity counting.

  SYK/ClusterExpansion.lean
    Source derivatives, Duhamel cumulants, dependency-graph tree bound,
    finite two-replica Wick formula, and the resummed two-replica L2
    cluster-expansion assumption.

  SYK/CLT.lean
    Assembly of the CLT from LLN + two-marked susceptibility.
-/

import Mathlib

noncomputable section
open Classical
open scoped BigOperators

namespace SYK
namespace CLTBlueprint

/-- A q-uniform hyperedge in `[n]`, represented as a `Finset (Fin n)` of
cardinality `q`. -/
abbrev Edge (n q : Nat) := {I : Finset (Fin n) // I.card = q}

/-- The number of q-hyperedges.  In a full formalization one proves
`Fintype.card (Edge n q) = Nat.choose n q`. -/
def numEdges (n q : Nat) : Nat := Nat.choose n q

/-- SYK variance normalization, written abstractly over `Real`. -/
def sigmaSq (n q : Nat) : Real :=
  (Nat.factorial (q - 1) : Real) / (n : Real) ^ (q - 1)

/-- Random variables live on an abstract sample space `Ω`.  The actual
probability measure is deliberately omitted in this blueprint. -/
abbrev RandVar (Ω : Type*) := Ω → Real

/-- Abstract data used by the CLT proof.

`L n β` is the log-partition function as a random variable.
`meanL n β` is its expectation.
`X n β` is the rescaled centered fluctuation.
`P r n β` is the projection of `L n β` onto the `r`-th Gaussian chaos.
`Kubo n I J β` is the Kubo connected covariance of the two Majorana monomials
indexed by `I` and `J`.
-/
structure SYKFamily (Ω : Type*) where
  q : Nat
  q_even : Even q
  q_ge_four : 4 ≤ q
  beta0 : Real
  betaSus : Real
  betaCE : Real
  ell : Real → Real
  L : Nat → Real → RandVar Ω
  meanL : Nat → Real → Real
  X : Nat → Real → RandVar Ω
  P : Nat → Nat → Real → RandVar Ω
  Kubo : (n : Nat) → Edge n q → Edge n q → Real → RandVar Ω

variable {Ω : Type*} (M : SYKFamily Ω)

/-- Limiting rank-one coefficient
`sqrt(q!/2) * β * ell'(β)`.
-/
def limitCoeff (M : SYKFamily Ω) (β : Real) : Real :=
  Real.sqrt ((Nat.factorial M.q : Real) / 2) * β * deriv M.ell β

/-! ## High-level predicates

The following predicates are placeholders for genuine analytic/probabilistic
statements.  They allow the Lean file to encode the proof graph without first
formalizing all of finite-dimensional Gaussian analysis and matrix analysis.
-/

/-- Locally uniform LLN:
`sup_{β in K} | n^{-1} E L_n(β) - ell(β) | -> 0` for compact `K`. -/
constant LocallyUniformLLN : SYKFamily Ω → Prop

/-- Derivative-strength LLN:
`sup_{β in K} | n^{-1} ∂_β E L_n(β) - ell'(β) | -> 0`. -/
constant DerivativeLLN : SYKFamily Ω → Prop

/-- Majorana sign-gauge invariance of the log-partition function. -/
constant GaugeInvariance : SYKFamily Ω → Prop

/-- Gauge parity selection rule for Hermite coefficients. -/
constant GaugeSelection : SYKFamily Ω → Prop

/-- Hermite coefficient formula for the Gaussian disorder. -/
constant HermiteCoefficientFormula : SYKFamily Ω → Prop

/-- Exact vanishing of the first chaos. -/
constant FirstChaosZero : SYKFamily Ω → Prop

/-- Exact diagonal second-chaos identity:
`P_2 L_n(β) = a_n(β) * sum_I (g_I^2 - 1)` and
`2 N_n a_n(β) = β ∂_β E L_n(β)`. -/
constant ExactSecondChaos : SYKFamily Ω → Prop

/-- CLT for the diagonal second chaos. -/
constant SecondChaosCLT : SYKFamily Ω → Prop

/-- Fixed finite chaos closure:
for each fixed `R`, `sum_{r=3}^R ||P_r L_n(β)||_2^2 = o(n^{2-q})`. -/
constant FiniteChaosClosure : SYKFamily Ω → Prop

/-- Two-marked high-temperature susceptibility:
`sup_I sum_J E |Kubo_{I,J}(β)|^2 <= C`. -/
constant TwoMarkedSusceptibility : SYKFamily Ω → Prop

/-- Kubo-Hessian identity and Hilbert--Schmidt Hessian bound. -/
constant HessianHSBound : SYKFamily Ω → Prop

/-- Malliavin second-derivative identity for the chaos tail. -/
constant MalliavinSecondTailIdentity : SYKFamily Ω → Prop

/-- Infinite higher-chaos closure:
`n^{q-2} sum_{r>=3} ||P_r L_n(β)||_2^2 -> 0`. -/
constant HigherChaosClosure : SYKFamily Ω → Prop

/-- Source derivative representation of the Kubo covariance. -/
constant KuboSourceDerivative : SYKFamily Ω → Prop

/-- Duhamel cumulants are ordinary cumulants of symmetrized trace moments. -/
constant DuhamelAsCumulant : SYKFamily Ω → Prop

/-- Dependency-graph tree bound for zero-source Duhamel cumulants. -/
constant DuhamelTreeGraphBound : SYKFamily Ω → Prop

/-- Exact finite two-replica Wick formula for the truncations. -/
constant FiniteTwoReplicaWickFormula : SYKFamily Ω → Prop

/-- Connected parity counting lemma:
`N_p(I,C) <= D_q^p p! n^{(q-1)p}`. -/
constant ConnectedParityCounting : SYKFamily Ω → Prop

/-- The only intentionally unproved CLT-level input in the TeX note:
resummed two-replica `L^2` cluster expansion. -/
constant TwoReplicaClusterExpansion : SYKFamily Ω → Prop

/-- Finite-dimensional convergence of the rescaled field to the rank-one
Gaussian field with coefficient `limitCoeff`. -/
constant RankOneFDDCLT : SYKFamily Ω → Prop

/-! ## Dependency axioms matching the TeX proof -/

/-- Proposition `Derivative LLN from convexity`. -/
axiom derivativeLLN_from_localLLN
  (hLLN : LocallyUniformLLN M) :
  DerivativeLLN M

/-- Lemma `Majorana sign-gauge invariance` implies the parity selection rule. -/
axiom gaugeSelection_from_gaugeInvariance
  (hgauge : GaugeInvariance M) :
  GaugeSelection M

/-- The selection rule kills the first chaos. -/
axiom firstChaosZero_from_selection
  (hsel : GaugeSelection M) :
  FirstChaosZero M

/-- Hermite coefficient formula plus gauge selection gives the exact second-chaos form. -/
axiom exactSecondChaos_from_hermite_and_selection
  (hHermite : HermiteCoefficientFormula M)
  (hsel : GaugeSelection M) :
  ExactSecondChaos M

/-- The exact second-chaos identity plus derivative LLN gives the second-chaos CLT. -/
axiom secondChaosCLT_from_exactSecondChaos
  (hSecond : ExactSecondChaos M)
  (hDeriv : DerivativeLLN M) :
  SecondChaosCLT M

/-- Kubo covariance is the Hessian of the log-partition function. -/
axiom hessianHS_from_twoMarked
  (hSus : TwoMarkedSusceptibility M) :
  HessianHSBound M

/-- Finite fixed chaoses plus Hessian tail give all higher chaoses negligible. -/
axiom higherChaosClosure_from_hessian
  (hFinite : FiniteChaosClosure M)
  (hHessian : HessianHSBound M)
  (hMalliavin : MalliavinSecondTailIdentity M) :
  HigherChaosClosure M

/-- The finite-chaos estimate follows from the log-partition derivative bound and
fixed-order even marked counting.  In a full formalization this should be a real
proof, not an axiom. -/
axiom finiteChaosClosure_from_counting
  (hHermite : HermiteCoefficientFormula M)
  (hsel : GaugeSelection M) :
  FiniteChaosClosure M

/-- The source-derivative, Duhamel tree bound, Wick formula, and connected parity
counting are the coefficientwise structural inputs for the cluster expansion. -/
axiom clusterInput_structure
  (hSource : KuboSourceDerivative M)
  (hCumulant : DuhamelAsCumulant M)
  (hTree : DuhamelTreeGraphBound M)
  (hWick : FiniteTwoReplicaWickFormula M)
  (hParity : ConnectedParityCounting M) :
  Prop

/-- Proposition `Cluster expansion implies two-marked susceptibility`. -/
axiom twoMarkedSusceptibility_from_cluster
  (hCE : TwoReplicaClusterExpansion M) :
  TwoMarkedSusceptibility M

/-- Assembly theorem in the TeX note: LLN + two-marked susceptibility imply the
rank-one high-temperature CLT. -/
axiom mainCLT_from_twoMarked
  (hLLN : LocallyUniformLLN M)
  (hHermite : HermiteCoefficientFormula M)
  (hgauge : GaugeInvariance M)
  (hMalliavin : MalliavinSecondTailIdentity M)
  (hSus : TwoMarkedSusceptibility M) :
  RankOneFDDCLT M

/-- Main theorem with the unproved input isolated exactly as in the TeX file:
LLN + resummed two-replica cluster expansion imply the high-temperature CLT. -/
theorem mainCLT_from_twoReplicaCluster
  (hLLN : LocallyUniformLLN M)
  (hHermite : HermiteCoefficientFormula M)
  (hgauge : GaugeInvariance M)
  (hMalliavin : MalliavinSecondTailIdentity M)
  (hCE : TwoReplicaClusterExpansion M) :
  RankOneFDDCLT M := by
  have hSus : TwoMarkedSusceptibility M :=
    twoMarkedSusceptibility_from_cluster M hCE
  exact mainCLT_from_twoMarked M hLLN hHermite hgauge hMalliavin hSus

/-! ## More detailed internal assembly

The next theorem expands `mainCLT_from_twoMarked` into the same chain used in
the TeX proof.  It is useful when gradually replacing the axioms above by real
Lean proofs.
-/

axiom clt_assembly_from_second_and_higher
  (hSecondCLT : SecondChaosCLT M)
  (hHigher : HigherChaosClosure M) :
  RankOneFDDCLT M

/-- Expanded assembly of the theorem from the individual components. -/
theorem mainCLT_expanded
  (hLLN : LocallyUniformLLN M)
  (hHermite : HermiteCoefficientFormula M)
  (hgauge : GaugeInvariance M)
  (hMalliavin : MalliavinSecondTailIdentity M)
  (hSus : TwoMarkedSusceptibility M) :
  RankOneFDDCLT M := by
  have hDeriv : DerivativeLLN M :=
    derivativeLLN_from_localLLN M hLLN
  have hSel : GaugeSelection M :=
    gaugeSelection_from_gaugeInvariance M hgauge
  have hSecond : ExactSecondChaos M :=
    exactSecondChaos_from_hermite_and_selection M hHermite hSel
  have hSecondCLT : SecondChaosCLT M :=
    secondChaosCLT_from_exactSecondChaos M hSecond hDeriv
  have hFinite : FiniteChaosClosure M :=
    finiteChaosClosure_from_counting M hHermite hSel
  have hHessian : HessianHSBound M :=
    hessianHS_from_twoMarked M hSus
  have hHigher : HigherChaosClosure M :=
    higherChaosClosure_from_hessian M hFinite hHessian hMalliavin
  exact clt_assembly_from_second_and_higher M hSecondCLT hHigher

/-! ## Formalization milestones

Below are the specific statements that should be converted from comments into
actual Lean theorem statements as the lower-level libraries become available.
They are listed in roughly increasing difficulty.
-/

namespace Milestones

/-- Milestone A1: finite type of q-edges. -/
axiom card_edge_eq_choose (n q : Nat) :
  Fintype.card (Edge n q) = Nat.choose n q

/-- Milestone A2: finite-order even marked counting. -/
constant EvenMultiIndexCountStatement (q R : Nat) : Prop

/-- Milestone A3: connected parity counting. -/
constant ConnectedParityCountingStatement (q p n : Nat) : Prop

/-- Milestone B1: Clifford sign gauge.  This requires a Clifford algebra or a
matrix model of Majoranas. -/
constant CliffordGaugeStatement : Prop

/-- Milestone B2: trace orthogonality of Majorana monomials. -/
constant MajoranaTraceOrthogonalityStatement : Prop

/-- Milestone C1: Gaussian Hermite coefficient formula by integration by parts. -/
constant HermiteIBPStatement : Prop

/-- Milestone C2: Malliavin second derivative identity
`E ||D^2 F||_HS^2 = sum_{r>=2} r(r-1) ||P_r F||_2^2`. -/
constant MalliavinSecondIdentityStatement : Prop

/-- Milestone D1: Duhamel formula for finite-dimensional matrix exponentials. -/
constant MatrixDuhamelFormulaStatement : Prop

/-- Milestone D2: Kubo covariance equals a source derivative and equals the Hessian. -/
constant KuboHessianStatement : Prop

/-- Milestone E1: dependency-graph cumulant tree inequality. -/
constant DependencyGraphTreeInequalityStatement : Prop

/-- Milestone E2: finite two-replica Wick formula. -/
constant FiniteTwoReplicaWickStatement : Prop

/-- Milestone F: resummed two-replica L2 cluster expansion.  This remains the
substantive unproved mathematical input. -/
constant ResummedTwoReplicaClusterExpansionStatement : Prop

end Milestones

end CLTBlueprint
end SYK
