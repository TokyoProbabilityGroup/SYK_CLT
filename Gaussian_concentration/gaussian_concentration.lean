import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open scoped BigOperators ENNReal
open MeasureTheory
open ProbabilityTheory

namespace SYK

/-- The Euclidean space of real SYK couplings. -/
abbrev CouplingSpace (N q : ℕ) :=
  EuclideanSpace ℝ (InteractionIndex N q)

@[simp]
theorem couplingSpace_card (N q : ℕ) :
    Fintype.card (InteractionIndex N q) = Nat.choose N q := by
  simp [InteractionIndex]

/-- The product standard Gaussian measure transported to coupling space. -/
noncomputable def standardGaussianMeasure (N q : ℕ) :
    Measure (CouplingSpace N q) :=
  (Measure.pi fun _ : InteractionIndex N q => gaussianReal 0 1).map
    (WithLp.toLp 2)

/-
Blueprint for `gaussian_lipschitz_concentration`

Goal in `SYK/Gaussian_concentration/gaussian_concentration.lean`:

```lean
theorem gaussian_lipschitz_concentration
    (N q : Nat) (F : CouplingSpace N q -> Real) (L t : Real)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasure N q
        {x | |F x - integral (fun y => F y) (standardGaussianMeasure N q)| > t} <=
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
```

The SYK theorem should be a short reduction to a general finite-dimensional
Gaussian concentration theorem. Keep the analytic theorem reusable and keep the
SYK-specific file limited to identifying the measure and index type.

## Local definitions

Use one standard Gaussian measure for every finite Euclidean coordinate type:

```lean
noncomputable def standardGaussianMeasureOnEuclidean
    (iota : Type*) [Fintype iota] :
    Measure (EuclideanSpace Real iota) :=
  (Measure.pi fun _ : iota => gaussianReal 0 1).map (WithLp.toLp 2)
```

Connect it to the SYK measure:

```lean
@[simp]
theorem standardGaussianMeasure_eq_onEuclidean (N q : Nat) :
    standardGaussianMeasure N q =
      standardGaussianMeasureOnEuclidean (InteractionIndex N q) := rfl
```

This works because

```lean
CouplingSpace N q = EuclideanSpace Real (InteractionIndex N q)
```

by definition, and both measures are the same pushed-forward product measure.

## Measure facts

Prove these helper facts before the concentration proof:

```lean
instance standardGaussianMeasureOnEuclidean_isProbability
    {iota : Type*} [Fintype iota] :
    IsProbabilityMeasure (standardGaussianMeasureOnEuclidean iota) := by
```

Use:

- `gaussianReal 0 1` has `IsProbabilityMeasure`.
- `Measure.pi` preserves `IsProbabilityMeasure` for finite products.
- `Measure.map` preserves total mass when the map is measurable.
- `WithLp.toLp 2` is measurable, usually by `fun_prop` or the `WithLp`
  measurable lemma.

Also prove measurability of tail events as needed. Since `hLip` implies
continuity, the function

```lean
fun x => |F x - integral (fun y => F y) gamma|
```

is measurable, so `{x | |F x - m| > t}` is measurable.

## Integrability of the mean

The integral in the statement should be a real Bochner integral. Prove:

```lean
lemma integrable_of_lipschitz_standardGaussian
    {iota : Type*} [Fintype iota]
    (F : EuclideanSpace Real iota -> Real) (L : Real)
    (hL : 0 < L) (hLip : LipschitzWith L.toNNReal F) :
    Integrable F (standardGaussianMeasureOnEuclidean iota) := by
```

The useful pointwise bound is:

```lean
have hbound : forall x,
    |F x| <= |F 0| + L * ||x|| := by
```

Derive it from the triangle inequality and `hLip.dist_le_mul x 0`. Since
`0 <= L`, rewrite

```lean
((L.toNNReal : NNReal) : Real) = L
```

with `Real.coe_toNNReal _ hL.le` or the closest available simp lemma in the
local mathlib version.

For the Gaussian norm term, either use Fernique:

```lean
ProbabilityTheory.IsGaussian.memLp_id
```

after importing

```lean
import Mathlib.Probability.Distributions.Gaussian.Fernique
```

or prove the finite-dimensional bound directly by pulling back through
`WithLp.toLp 2` and bounding the Euclidean norm by the sum of coordinate
absolute values.

## Analytic input

Isolate the main probability theorem. This is the only substantial analytic
ingredient.

```lean
theorem product_standardGaussian_upper_tail
    {iota : Type*} [Fintype iota]
    (F : EuclideanSpace Real iota -> Real) (L t : Real)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    let gamma := standardGaussianMeasureOnEuclidean iota
    gamma {x | F x - integral (fun y => F y) gamma > t} <=
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
```

This theorem is normally proved by the Gaussian log-Sobolev inequality and the
Herbst argument. If formalizing that proof is outside the current scope, keep a
single local `sorry` here, with a comment saying that this is the analytic
Gaussian concentration input. Do not introduce a global axiom.

The matching lower tail follows from the same theorem applied to `-F`:

```lean
theorem product_standardGaussian_lower_tail
    {iota : Type*} [Fintype iota]
    (F : EuclideanSpace Real iota -> Real) (L t : Real)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    let gamma := standardGaussianMeasureOnEuclidean iota
    gamma {x | integral (fun y => F y) gamma - F x > t} <=
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
```

The required Lipschitz fact is either:

```lean
have hLip_neg : LipschitzWith L.toNNReal (fun x => -F x) := hLip.neg
```

or a direct proof using `dist_neg_neg`.

For the mean of `-F`, use linearity of the integral after applying the
integrability lemma:

```lean
integral (fun x => -F x) gamma = - integral (fun x => F x) gamma
```

## Two-sided Euclidean theorem

Prove the reusable result:

```lean
theorem euclidean_lipschitz_gaussian_concentration
    {iota : Type*} [Fintype iota]
    (F : EuclideanSpace Real iota -> Real) (L t : Real)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    let gamma := standardGaussianMeasureOnEuclidean iota
    gamma {x | |F x - integral (fun y => F y) gamma| > t} <=
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
```

Let:

```lean
let gamma := standardGaussianMeasureOnEuclidean iota
let m := integral (fun y => F y) gamma
let A : Set (EuclideanSpace Real iota) := {x | F x - m > t}
let B : Set (EuclideanSpace Real iota) := {x | m - F x > t}
```

Use the elementary real lemma:

```lean
lemma abs_gt_iff_pos_or_neg {a t : Real} :
    |a| > t <-> a > t \/ -a > t := by
```

Then prove the event inclusion:

```lean
have hsubset : {x | |F x - m| > t} <= Set.union A B := by
  intro x hx
  have hx' : F x - m > t \/ -(F x - m) > t := by
    simpa using (abs_gt_iff_pos_or_neg.mp hx)
  exact hx'.elim
    (fun h => Or.inl h)
    (fun h => Or.inr (by simpa [sub_eq_add_neg] using h))
```

Apply the union bound:

```lean
have h_event_le : gamma {x | |F x - m| > t} <= gamma (Set.union A B) :=
  measure_mono hsubset
have h_union : gamma (Set.union A B) <= gamma A + gamma B :=
  measure_union_le A B
```

Apply `product_standardGaussian_upper_tail` to `A` and
`product_standardGaussian_lower_tail` to `B`.

Finish the right side with:

```lean
have hexp_nonneg : 0 <= Real.exp (-t ^ 2 / (2 * L ^ 2)) := Real.exp_nonneg _
rw [show
    2 * Real.exp (-t ^ 2 / (2 * L ^ 2))
      = Real.exp (-t ^ 2 / (2 * L ^ 2))
        + Real.exp (-t ^ 2 / (2 * L ^ 2)) by ring]
rw [ENNReal.ofReal_add hexp_nonneg hexp_nonneg]
```

Useful real side facts:

```lean
have hL2pos : 0 < L ^ 2 := sq_pos_of_pos hL
have hdenpos : 0 < 2 * L ^ 2 := mul_pos (by norm_num) hL2pos
have hrhs_nonneg :
    0 <= 2 * Real.exp (-t ^ 2 / (2 * L ^ 2)) := by positivity
```

## Final SYK theorem

Once `euclidean_lipschitz_gaussian_concentration` is available, the target
proof should be only:

```lean
theorem gaussian_lipschitz_concentration
    (N q : Nat) (F : CouplingSpace N q -> Real) (L t : Real)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasure N q
        {x | |F x - integral (fun y => F y) (standardGaussianMeasure N q)| > t} <=
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  simpa [standardGaussianMeasureOnEuclidean, standardGaussianMeasure]
    using euclidean_lipschitz_gaussian_concentration
      (iota := InteractionIndex N q) F L t hL ht hLip
```

## Order of implementation

- Define `standardGaussianMeasureOnEuclidean`.
- Prove it matches `standardGaussianMeasure`.
- Prove probability and measurability helper facts.
- Prove integrability of Lipschitz functions under the standard Gaussian.
- Add the upper-tail analytic input.
- Derive the lower-tail theorem from the upper-tail theorem applied to `-F`.
- Derive the two-sided Euclidean theorem by the union bound.
- Close the SYK theorem with `simpa`.

## Main risk

The analytic upper-tail theorem is the hard part. Everything after it is
finite-dimensional bookkeeping, event inclusion, the union bound, and `ENNReal`
algebra.
-/

/--
Gaussian concentration for the product standard Gaussian on the SYK coupling
space. The coupling space has `Nat.choose N q` coordinates by
`couplingSpace_card`.
-/
theorem gaussian_lipschitz_concentration
    (N q : ℕ) (F : CouplingSpace N q → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasure N q
        {x | |F x - ∫ y, F y ∂standardGaussianMeasure N q| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  sorry

end SYK
