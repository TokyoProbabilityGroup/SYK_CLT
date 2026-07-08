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

/-- Reflection formula for the probabilist's Hermite polynomials:
`Hₖ(-x) = (-1)ᵏ Hₖ(x)`, a consequence of `Hₖ` having the parity of `k`. -/
theorem hermiteProb_neg (k : Nat) (x : Real) :
    hermiteProb k (-x) = (-1) ^ k * hermiteProb k x := by
  unfold hermiteProb
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.mem_support_iff] at hi
  have hpar : Even (k + i) := by
    rw [← Nat.not_odd_iff_even]
    intro h
    exact hi (Polynomial.coeff_hermite_of_odd_add h)
  have hsign : (-1 : ℝ) ^ i = (-1) ^ k := by
    rcases Nat.even_or_odd k with hk | hk
    · have hi' : Even i := by
        have := (Nat.even_add.mp hpar); exact (this.mp hk)
      rw [hk.neg_one_pow, hi'.neg_one_pow]
    · have hi' : Odd i := by
        rw [Nat.even_add] at hpar
        rcases Nat.even_or_odd i with h | h
        · exact absurd (hpar.mpr h) (by simpa using hk)
        · exact h
      rw [hk.neg_one_pow, hi'.neg_one_pow]
  rw [neg_pow, hsign]; ring

/-- For a sign `c` with `c² = 1`, the Hermite polynomial satisfies
`Hₖ(c·x) = cᵏ Hₖ(x)`. -/
theorem hermiteProb_sign_mul (k : Nat) (x : Real) {c : Real} (hc : c ^ 2 = 1) :
    hermiteProb k (c * x) = c ^ k * hermiteProb k x := by
  have hcc : c = 1 ∨ c = -1 := mul_self_eq_one_iff.mp (by nlinarith)
  rcases hcc with h | h
  · subst h; simp
  · subst h; simpa [neg_one_mul] using hermiteProb_neg k x

/-- The gauge character is a sign, i.e. its square is `1`. -/
theorem gaugeCharacter_sq {N q : Nat} (s : SignConfig N)
    (I : InteractionLabels N q) : gaugeCharacter s I ^ 2 = 1 := by
  unfold gaugeCharacter
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun a _ => s.sq_eq_one a

/-- The product of the gauge characters raised to the multi-index powers equals
the vertex-wise gauge factor. -/
theorem prod_gaugeCharacter_pow {N q : Nat} (alpha : MultiIndex N q)
    (s : SignConfig N) :
    (Finset.univ.prod fun I : InteractionLabels N q =>
        gaugeCharacter s I ^ alpha I) = hermiteGaugeFactor alpha s := by
  unfold hermiteGaugeFactor gaugeCharacter vertexMultiplicity
  have hcard : ∀ (I : InteractionLabels N q) (a : Fin N),
      (I.1.filter fun b : Fin N => b = a).card = if a ∈ I.1 then 1 else 0 := by
    intro I a
    by_cases h : a ∈ I.1
    · simp [h, Finset.filter_eq']
    · simp [h, Finset.filter_eq']
  simp only [hcard]
  rw [show (∏ a, s.val a ^ ∑ I : InteractionLabels N q,
          (if a ∈ I.1 then 1 else 0) * alpha I)
        = ∏ a, ∏ I : InteractionLabels N q,
          s.val a ^ ((if a ∈ I.1 then 1 else 0) * alpha I) from by
        apply Finset.prod_congr rfl
        intro a _
        rw [Finset.prod_pow_eq_pow_sum]]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro I _
  rw [← Finset.prod_pow]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ I.1)]
  have h2 : (∏ a ∈ Finset.univ.filter (· ∉ I.1),
      s.val a ^ ((if a ∈ I.1 then 1 else 0) * alpha I)) = 1 := by
    apply Finset.prod_eq_one
    intro a ha
    simp only [Finset.mem_filter] at ha
    simp [ha.2]
  rw [h2, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.prod_congr rfl
  intro a ha
  simp [ha]

theorem hermite_multi_gauge_action {N q : Nat} (alpha : MultiIndex N q)
    (s : SignConfig N) (g : CouplingSpace N q) :
    hermiteMulti alpha (gaugeAction s g) =
      hermiteGaugeFactor alpha s * hermiteMulti alpha g := by
  unfold hermiteMulti
  have hval : ∀ I : InteractionLabels N q,
      (gaugeAction s g) I = gaugeCharacter s I * g I := fun _ => rfl
  simp only [hval]
  rw [← prod_gaugeCharacter_pow alpha s, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro I _
  rw [hermiteProb_sign_mul (alpha I) (g I) (gaugeCharacter_sq s I)]

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
