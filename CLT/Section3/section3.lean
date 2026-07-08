import SYK.SYK_model.model
import SYK.super_concentration.super_conc
import Mathlib.RingTheory.Polynomial.Hermite.Basic

open scoped BigOperators
open MeasureTheory

namespace SYK
namespace CLT

/-!
Section 3 stubs from `CLT_for_SYK_v3.tex`.

The analytic facts are recorded as theorem statements with `sorry`.  The
projection operator is a placeholder until the Gaussian chaos formalization is
filled in.
-/

abbrev InteractionLabels (N q : Nat) := InteractionIndex N q

abbrev MultiIndex (N q : Nat) := InteractionLabels N q -> Nat

noncomputable def hermiteProb (k : Nat) (x : Real) : Real :=
  Polynomial.aeval x (Polynomial.hermite k)

def multiIndexDegree {N q : Nat} (alpha : MultiIndex N q) : Nat :=
  Finset.univ.sum alpha

def multiIndexFactorial {N q : Nat} (alpha : MultiIndex N q) : Nat :=
  Finset.univ.prod fun I => (alpha I).factorial

noncomputable def hermiteMulti {N q : Nat} (alpha : MultiIndex N q)
    (g : CouplingSpace N q) : Real :=
  Finset.univ.prod fun I => hermiteProb (alpha I) (g I)

noncomputable def gaussianExpectation {N q : Nat}
    (F : CouplingSpace N q -> Real) : Real :=
  integral (standardGaussianMeasure N q) F

noncomputable def centered {N q : Nat} (F : CouplingSpace N q -> Real) :
    CouplingSpace N q -> Real :=
  fun g => F g - gaussianExpectation F

noncomputable def chaosProjection {N q : Nat} (_r : Nat)
    (_F : CouplingSpace N q -> Real) : CouplingSpace N q -> Real :=
  0

noncomputable def coordinateDirection {N q : Nat}
    (I : InteractionLabels N q) : CouplingSpace N q :=
  WithLp.toLp 2 (Pi.single I (1 : Real))

noncomputable def coordinateDerivative {N q : Nat} (I : InteractionLabels N q)
    (F : CouplingSpace N q -> Real) : CouplingSpace N q -> Real :=
  fun g => fderiv Real F g (coordinateDirection I)

noncomputable def repeatedCoordinateDerivative {N q : Nat}
    (I : InteractionLabels N q) :
    Nat -> (CouplingSpace N q -> Real) -> CouplingSpace N q -> Real
  | 0, F => F
  | k + 1, F => coordinateDerivative I (repeatedCoordinateDerivative I k F)

noncomputable def multiIndexDerivative {N q : Nat} (alpha : MultiIndex N q)
    (F : CouplingSpace N q -> Real) : CouplingSpace N q -> Real :=
  (Finset.univ.toList : List (InteractionLabels N q)).foldl
    (fun G I => repeatedCoordinateDerivative I (alpha I) G) F

noncomputable def hermiteCoefficient {N q : Nat}
    (F : CouplingSpace N q -> Real) (alpha : MultiIndex N q) : Real :=
  gaussianExpectation (fun g => F g * hermiteMulti alpha g) /
    (multiIndexFactorial alpha : Real)

noncomputable def chaosDecompositionRhs {N q : Nat}
    (F : CouplingSpace N q -> Real) : CouplingSpace N q -> Real :=
  fun g => tsum (fun r : Nat => chaosProjection (r + 1) F g)

noncomputable def chaosProjectionExpansion {N q : Nat} (r : Nat)
    (F : CouplingSpace N q -> Real) : CouplingSpace N q -> Real :=
  fun g => tsum (fun alpha : MultiIndex N q =>
    if multiIndexDegree alpha = r then
      hermiteCoefficient F alpha * hermiteMulti alpha g
    else
      0)

def vertexMultiplicity {N q : Nat} (alpha : MultiIndex N q)
    (a : Fin N) : Nat :=
  Finset.univ.sum fun I : InteractionLabels N q =>
    ((I.1.filter fun b : Fin N => b = a).card) * alpha I

structure SignConfig (N : Nat) where
  val : Fin N -> Real
  sq_eq_one : forall a, val a ^ 2 = 1

noncomputable def gaugeCharacter {N q : Nat} (s : SignConfig N)
    (I : InteractionLabels N q) : Real :=
  I.1.prod fun a => s.val a

noncomputable def gaugeAction {N q : Nat} (s : SignConfig N)
    (g : CouplingSpace N q) : CouplingSpace N q :=
  let h : InteractionLabels N q -> Real := fun I => gaugeCharacter s I * g I
  WithLp.toLp 2 h

noncomputable def hermiteGaugeFactor {N q : Nat}
    (alpha : MultiIndex N q) (s : SignConfig N) : Real :=
  (Finset.univ : Finset (Fin N)).prod fun a =>
    s.val a ^ vertexMultiplicity alpha a

noncomputable def secondDerivativeExpectation {N q : Nat}
    (F : CouplingSpace N q -> Real) (I J : InteractionLabels N q) : Real :=
  gaussianExpectation (coordinateDerivative I (coordinateDerivative J F))

theorem hermite_coefficient_formula
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d Complex))
    (scale : Real) :
    And
      (centered (logPartition P M scale) =
        chaosDecompositionRhs (logPartition P M scale))
      (And
        (forall r : Nat,
          chaosProjection r (logPartition P M scale) =
            chaosProjectionExpansion r (logPartition P M scale))
        (forall alpha : MultiIndex P.N P.q,
          hermiteCoefficient (logPartition P M scale) alpha =
            gaussianExpectation
              (multiIndexDerivative alpha (logPartition P M scale)) /
              (multiIndexFactorial alpha : Real))) := by
  sorry

theorem majorana_sign_gauge_invariance
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d Complex))
    (scale : Real) (s : SignConfig P.N) (g : CouplingSpace P.N P.q) :
    logPartition P M scale g =
      logPartition P M scale (gaugeAction s g) := by
  sorry

theorem hermite_multi_gauge_action {N q : Nat} (alpha : MultiIndex N q)
    (s : SignConfig N) (g : CouplingSpace N q) :
    hermiteMulti alpha (gaugeAction s g) =
      hermiteGaugeFactor alpha s * hermiteMulti alpha g := by
  sorry

theorem gauge_parity_selection_rule
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d Complex))
    (scale : Real) :
    And
      (forall alpha : MultiIndex P.N P.q,
        (exists a : Fin P.N, Odd (vertexMultiplicity alpha a)) ->
          hermiteCoefficient (logPartition P M scale) alpha = 0)
      (And
        (chaosProjection 1 (logPartition P M scale) = 0)
        (forall I J : InteractionLabels P.N P.q, I != J ->
          secondDerivativeExpectation (logPartition P M scale) I J = 0)) := by
  sorry

end CLT
end SYK
