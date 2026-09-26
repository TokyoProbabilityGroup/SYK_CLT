module

public import SYK.Model.Majorana
public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import RequestProject.SingularValues
public import RequestProject.GaussianIBPAux
public import RequestProject.SchattenAux
public import RequestProject.ExpAux
public import RequestProject.MatrixRealNormed
public import RequestProject.DerivAux
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory


/-!
# Reusable analytic lemmas for finite-dimensional matrix Gibbs functions

The first part contains no SYK-specific definitions.  (In the original version the
substantial analytic statements were left with `sorry`; they are now all proved, except for
`normalizedSchattenNorm_antitone`, which is false and has been commented out and replaced by a
corrected statement, see below.)

The main reusable pieces are:

* Gaussian--Hermite integration by parts in one dimension;
* a Banach-algebra Duhamel formula for the derivative of the exponential;
* normalized trace and normalized Schatten norms;
* Schatten Hölder and operator-norm multiplication bounds;
* the exact Schatten norm of an exponential of a Hermitian matrix;
* an iterated directional derivative bound for the normalized trace exponential.
-/

namespace MatrixAnalysis

/-! ## 1. Gaussian--Hermite integration by parts -/

namespace GaussianIBP

/-- The probabilists' Hermite polynomial `He_k`, evaluated at a real point. -/
noncomputable def hermiteEval (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.aeval x) (Polynomial.hermite k)

/--
A convenient exponential-growth hypothesis for a real function and all derivatives through order
`k`.  This is stronger than necessary, but is exactly the sort of hypothesis used to justify
repeated Gaussian integration by parts.
-/
def HasExpGrowthUpTo (k : ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ j, j ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
    |(deriv^[j] f) x| ≤ C * Real.exp (C * |x|)

/--
One-dimensional Gaussian--Hermite integration by parts for a standard Gaussian.

This is the reusable scalar statement from which the finite-product / multi-index version can be
obtained by iterating over independent coordinates.
-/
theorem hermite_ibp_standardGaussian
    (k : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ k f)
    (hgrowth : HasExpGrowthUpTo k f) :
    (∫ x : ℝ,
        hermiteEval k x * f x
          ∂ ProbabilityTheory.gaussianReal 0 1) =
      ∫ x : ℝ,
        (deriv^[k] f) x
          ∂ ProbabilityTheory.gaussianReal 0 1 := by
  exact GaussianIBPAux.hermite_ibp hf hgrowth

end GaussianIBP

/-! ## 2. Radial chain rule -/

namespace Radial

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Derivative of `t ↦ f (t • x)` at `t = 1`.  This is the abstract form of the Euler/radial identity
used when a model depends linearly on a collection of couplings.
-/
theorem hasFDerivAt_radial
    (f : E → F) (x : E) (f' : E →L[ℝ] F)
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun t : ℝ => f (t • x))
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)) 1 := by
  have h1 : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have h2 : HasFDerivAt f f' ((1 : ℝ) • x) := by simpa using hf
  exact (h2.comp_hasDerivAt 1 h1).hasFDerivAt

end Radial

/-! ## 3. Duhamel formula -/

namespace Duhamel

variable {𝔸 : Type*}
  [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The Duhamel kernel `exp(sX) V exp((1-s)X)`. -/
noncomputable def kernel (X V : 𝔸) (s : ℝ) : 𝔸 :=
  NormedSpace.exp (s • X) * V * NormedSpace.exp ((1 - s) • X)

/-- Integral form of `exp Y - exp X`. -/
theorem exp_sub_exp_eq_integral (X Y : 𝔸) :
    NormedSpace.exp Y - NormedSpace.exp X =
      ∫ s : ℝ in (0 : ℝ)..1,
        NormedSpace.exp (s • Y) * (Y - X) * NormedSpace.exp ((1 - s) • X) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Y) * NormedSpace.exp ((1 - s) • X))
        (NormedSpace.exp (s • Y) * (Y - X) * NormedSpace.exp ((1 - s) • X)) s := by
    intro s _
    have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Y)) (NormedSpace.exp (s • Y) * Y) s :=
      hasDerivAt_exp_smul_const Y s
    have h2' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
        (X * NormedSpace.exp ((1 - s) • X)) (1 - s) :=
      hasDerivAt_exp_smul_const' X (1 - s)
    have h3 : HasDerivAt (fun u : ℝ => 1 - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • X))
        ((-1 : ℝ) • (X * NormedSpace.exp ((1 - s) • X))) s := h2'.scomp s h3
    convert h1.mul h2 using 1
    simp [mul_sub, sub_mul, mul_assoc]
    abel
  have hcont : Continuous fun s : ℝ =>
      NormedSpace.exp (s • Y) * (Y - X) * NormedSpace.exp ((1 - s) • X) := by
    have : Continuous (NormedSpace.exp : 𝔸 → 𝔸) :=
      continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp

/-- Joint continuity of the Duhamel-type integral in the left exponent and the inserted term. -/
theorem continuous_duhamelIntegral (X : 𝔸) :
    Continuous fun p : 𝔸 × 𝔸 => ∫ s : ℝ in (0 : ℝ)..1,
        NormedSpace.exp (s • p.1) * p.2 * NormedSpace.exp ((1 - s) • X) := by
  have : Continuous (NormedSpace.exp : 𝔸 → 𝔸) :=
    continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

/--
Duhamel formula for a differentiable curve in a real Banach algebra.

If `A'(θ) = V`, then
`d/dθ exp(A(θ)) = ∫_0^1 exp(s A(θ)) V exp((1-s) A(θ)) ds`.
-/
theorem hasFDerivAt_exp
    (A : ℝ → 𝔸) (θ : ℝ) (V : 𝔸)
    (hA : HasFDerivAt A (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) V) θ) :
    HasFDerivAt (fun t : ℝ => NormedSpace.exp (A t))
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (∫ s : ℝ in (0 : ℝ)..1, kernel (A θ) V s)) θ := by
  set X := A θ with hX
  let Φ : 𝔸 × 𝔸 → 𝔸 := fun p => ∫ s : ℝ in (0 : ℝ)..1,
    NormedSpace.exp (s • p.1) * p.2 * NormedSpace.exp ((1 - s) • X)
  have hΦ : Continuous Φ := continuous_duhamelIntegral X
  have hA' : HasDerivAt A V θ := hasDerivAt_iff_hasFDerivAt.mpr hA
  suffices h : HasDerivAt (fun t => NormedSpace.exp (A t)) (Φ (X, V)) θ from h.hasFDerivAt
  rw [hasDerivAt_iff_tendsto_slope]
  have hslopeA := hasDerivAt_iff_tendsto_slope.mp hA'
  have hcontA : Filter.Tendsto A (nhdsWithin θ {θ}ᶜ) (nhds X) :=
    hA'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have key : ∀ t, slope (fun t => NormedSpace.exp (A t)) θ t = Φ (A t, slope A θ t) := by
    intro t
    rw [slope_def_module, slope_def_module, exp_sub_exp_eq_integral X (A t),
      ← intervalIntegral.integral_smul]
    show _ = ∫ s : ℝ in (0 : ℝ)..1,
      NormedSpace.exp (s • A t) * ((t - θ)⁻¹ • (A t - X)) * NormedSpace.exp ((1 - s) • X)
    congr 1
    ext s
    rw [mul_smul_comm, smul_mul_assoc]
  rw [show slope (fun t => NormedSpace.exp (A t)) θ = fun t => Φ (A t, slope A θ t) from
    funext key]
  exact hΦ.continuousAt.tendsto.comp (hcontA.prodMk_nhds hslopeA)

/-- Duhamel formula specialized to the affine curve `X + tV`. -/
theorem hasFDerivAt_exp_affine (X V : 𝔸) (θ : ℝ) :
    HasFDerivAt (fun t : ℝ => NormedSpace.exp (X + t • V))
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (∫ s : ℝ in (0 : ℝ)..1, kernel (X + θ • V) V s)) θ := by
  have h : HasDerivAt (fun t : ℝ => X + t • V) V θ := by
    simpa using ((hasDerivAt_id θ).smul_const V).const_add X
  exact hasFDerivAt_exp (fun t : ℝ => X + t • V) θ V h.hasFDerivAt

end Duhamel

/-! ## 4. Normalized Schatten norms -/

namespace Schatten

variable {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- `∑ s_i(T)^p`, where `s_i(T)` are the singular values. -/
noncomputable def powerSum (p : ℝ) (T : E →ₗ[𝕜] E) : ℝ :=
  T.singularValues.sum fun _ s => s ^ p

/--
The Schatten `p`-norm normalized by dimension:
`((1 / dim E) * ∑ s_i(T)^p)^(1/p)`.

The definition is intended for `0 < p`.  In applications below we use `1 ≤ p`.
-/
noncomputable def normalizedNorm (p : ℝ) (T : E →ₗ[𝕜] E) : ℝ :=
  (powerSum p T / (Module.finrank 𝕜 E : ℝ)) ^ (1 / p)

/-- Nonnegativity of the normalized Schatten norm. -/
theorem normalizedNorm_nonneg [Nontrivial E]
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[𝕜] E) :
    0 ≤ normalizedNorm p T := by
  unfold normalizedNorm powerSum
  refine Real.rpow_nonneg (div_nonneg ?_ (Nat.cast_nonneg _)) _
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (T.singularValues_nonneg i) _

end Schatten

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Normalized matrix trace `card(n)⁻¹ * Tr(A)`. -/
noncomputable def normalizedTrace (A : Matrix n n 𝕜) : 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ * A.trace

@[simp] theorem normalizedTrace_zero :
    normalizedTrace (0 : Matrix n n 𝕜) = 0 := by
  simp [normalizedTrace]

@[simp] theorem normalizedTrace_one [Nonempty n] :
    normalizedTrace (1 : Matrix n n 𝕜) = 1 := by
  have : (Fintype.card n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [normalizedTrace, Matrix.trace_one, this]

theorem normalizedTrace_add (A B : Matrix n n 𝕜) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_add, mul_add]

theorem normalizedTrace_smul (c : 𝕜) (A : Matrix n n 𝕜) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, Matrix.trace_smul, mul_left_comm]

/-- Cyclicity for two factors. -/
theorem normalizedTrace_mul_comm (A B : Matrix n n 𝕜) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  simp [normalizedTrace, Matrix.trace_mul_comm A B]

/-- Normalized Schatten `p`-norm of a matrix, using its Euclidean linear map. -/
noncomputable def normalizedSchattenNorm (p : ℝ) (A : Matrix n n 𝕜) : ℝ :=
  Schatten.normalizedNorm p (Matrix.toEuclideanLin A)

/-! ### Auxiliary facts relating matrices to their Euclidean linear maps -/

theorem normalizedSchattenNorm_eq_sum {p : ℝ} (hp : 0 < p) (A : Matrix n n 𝕜) :
    normalizedSchattenNorm p A =
      ((∑ i, SVDAux.sv (Matrix.toEuclideanLin A) i ^ p) / (Fintype.card n : ℝ)) ^ (1 / p) := by
  unfold normalizedSchattenNorm Schatten.normalizedNorm Schatten.powerSum
  rw [SVDAux.singularValues_sum_rpow _ hp,
    show (Module.finrank 𝕜 (EuclideanSpace 𝕜 n) : ℝ) = Fintype.card n by
      rw [finrank_euclideanSpace]]

theorem toEuclideanLin_mul' (A B : Matrix n n 𝕜) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_mul _ (EuclideanSpace.basisFun n 𝕜).toBasis]

theorem norm_toContinuousLinearMap_toEuclideanLin (B : Matrix n n 𝕜) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)‖ = ‖B‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  rfl

theorem trace_eq_trace_toEuclideanLin (A : Matrix n n 𝕜) :
    A.trace = LinearMap.trace 𝕜 (EuclideanSpace 𝕜 n) (Matrix.toEuclideanLin A) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace 𝕜 (EuclideanSpace.basisFun n 𝕜).toBasis,
    LinearMap.toMatrix_toLin]

theorem sum_sv_rpow_nonneg (A : Matrix n n 𝕜) (p : ℝ) :
    0 ≤ ∑ i, SVDAux.sv (Matrix.toEuclideanLin A) i ^ p :=
  Finset.sum_nonneg fun i _ => Real.rpow_nonneg (SVDAux.sv_nonneg _ i) _

/-- Trace is bounded by normalized Schatten 1-norm. -/
theorem norm_normalizedTrace_le_schatten_one [Nonempty n]
    (A : Matrix n n 𝕜) :
    ‖normalizedTrace A‖ ≤ normalizedSchattenNorm 1 A := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [normalizedSchattenNorm_eq_sum one_pos, div_one, Real.rpow_one, normalizedTrace, norm_mul,
    norm_inv, RCLike.norm_natCast, trace_eq_trace_toEuclideanLin, inv_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ hN.le
  simpa using SchattenAux.norm_trace_le (Matrix.toEuclideanLin A)

/-- Normalized Schatten Hölder inequality. -/
theorem normalizedSchattenNorm_mul_le
    [Nonempty n]
    {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hrecip : 1 / r = 1 / p + 1 / q)
    (A B : Matrix n n 𝕜) :
    normalizedSchattenNorm r (A * B) ≤
      normalizedSchattenNorm p A * normalizedSchattenNorm q B := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := SchattenAux.holder (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) hp hq hr hrecip
  rw [← toEuclideanLin_mul'] at h
  have hNr : (Fintype.card n : ℝ) ^ (1 / r) =
      (Fintype.card n : ℝ) ^ (1 / p) * (Fintype.card n : ℝ) ^ (1 / q) := by
    rw [hrecip, Real.rpow_add hN]
  rw [normalizedSchattenNorm_eq_sum (by linarith), normalizedSchattenNorm_eq_sum (by linarith),
    normalizedSchattenNorm_eq_sum (by linarith),
    Real.div_rpow (sum_sv_rpow_nonneg (A * B) r) hN.le,
    Real.div_rpow (sum_sv_rpow_nonneg A p) hN.le, Real.div_rpow (sum_sv_rpow_nonneg B q) hN.le,
    div_mul_div_comm, hNr]
  have hpos : 0 < (Fintype.card n : ℝ) ^ (1 / p) * (Fintype.card n : ℝ) ^ (1 / q) :=
    mul_pos (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
  exact div_le_div_of_nonneg_right h hpos.le

/-- Right multiplication by a bounded operator. -/
theorem normalizedSchattenNorm_mul_opNorm_le
    [Nonempty n]
    {p : ℝ} (hp : 1 ≤ p) (A B : Matrix n n 𝕜) :
    normalizedSchattenNorm p (A * B) ≤
      normalizedSchattenNorm p A * ‖B‖ := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := SchattenAux.mul_opNorm (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) hp
  rw [← toEuclideanLin_mul', norm_toContinuousLinearMap_toEuclideanLin] at h
  rw [normalizedSchattenNorm_eq_sum (by linarith), normalizedSchattenNorm_eq_sum (by linarith),
    Real.div_rpow (sum_sv_rpow_nonneg (A * B) p) hN.le,
    Real.div_rpow (sum_sv_rpow_nonneg A p) hN.le, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h (Real.rpow_pos_of_pos hN _).le

/-- Left multiplication by a bounded operator. -/
theorem normalizedSchattenNorm_opNorm_mul_le
    [Nonempty n]
    {p : ℝ} (hp : 1 ≤ p) (A B : Matrix n n 𝕜) :
    normalizedSchattenNorm p (A * B) ≤
      ‖A‖ * normalizedSchattenNorm p B := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := SchattenAux.opNorm_mul (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) hp
  rw [← toEuclideanLin_mul', norm_toContinuousLinearMap_toEuclideanLin] at h
  rw [normalizedSchattenNorm_eq_sum (by linarith), normalizedSchattenNorm_eq_sum (by linarith),
    Real.div_rpow (sum_sv_rpow_nonneg (A * B) p) hN.le,
    Real.div_rpow (sum_sv_rpow_nonneg B p) hN.le, mul_div_assoc']
  exact div_le_div_of_nonneg_right h (Real.rpow_pos_of_pos hN _).le

/-
The following statement from the original file is **false** and has been commented out.
Dimension-normalized Schatten norms are power means of the singular values, and power means are
*nondecreasing* in the exponent.  For instance, for `A = diagonal ![1, 0]` (a `2 × 2` real
matrix) the normalized Schatten `p`-norm is `(1/2)^(1/p)`, which equals `1/2` for `p = 1` but
`1/√2 > 1/2` for `p = 2`; see `normalizedSchattenNorm_antitone_counterexample` and
`not_normalizedSchattenNorm_antitone` below.  The corrected statement (monotonicity) is
`normalizedSchattenNorm_monotone`.

/-- Monotonicity in `p` for dimension-normalized Schatten norms. -/
theorem normalizedSchattenNorm_antitone
    [Nonempty n]
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (A : Matrix n n 𝕜) :
    normalizedSchattenNorm q A ≤ normalizedSchattenNorm p A := by
  sorry
-/

/-- Power means are nondecreasing in the exponent. -/
theorem powerMean_mono {ι : Type*} [Fintype ι] [Nonempty ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ((∑ i, σ i ^ p) / (Fintype.card ι : ℝ)) ^ (1 / p) ≤
      ((∑ i, σ i ^ q) / (Fintype.card ι : ℝ)) ^ (1 / q) := by
  have hq : 0 < q := by linarith
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ => 1 / (Fintype.card ι : ℝ)) (fun i => σ i ^ p) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun i _ => Real.rpow_nonneg (hσ i) _) (by rw [le_div_iff₀ hp]; linarith : 1 ≤ q / p)
  have hpow : ∀ i, (σ i ^ p) ^ (q / p) = σ i ^ q := fun i => by
    rw [← Real.rpow_mul (hσ i), mul_div_cancel₀ _ hp.ne']
  simp only [hpow, ← Finset.mul_sum] at hJ
  have hsp : 0 ≤ ∑ i, σ i ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hσ i) _
  have hsq : 0 ≤ ∑ i, σ i ^ q := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hσ i) _
  have e : ∀ x : ℝ, x / (Fintype.card ι : ℝ) = 1 / (Fintype.card ι : ℝ) * x := fun x => by ring
  rw [e (∑ i, σ i ^ p), e (∑ i, σ i ^ q)]
  have hm : 0 ≤ 1 / (Fintype.card ι : ℝ) * ∑ i, σ i ^ p := by positivity
  calc (1 / (Fintype.card ι : ℝ) * ∑ i, σ i ^ p) ^ (1 / p)
      = ((1 / (Fintype.card ι : ℝ) * ∑ i, σ i ^ p) ^ (q / p)) ^ (1 / q) := by
        rw [← Real.rpow_mul hm]
        congr 1
        field_simp
    _ ≤ (1 / (Fintype.card ι : ℝ) * ∑ i, σ i ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hm _) hJ (by positivity)

/-- Corrected version of `normalizedSchattenNorm_antitone`: dimension-normalized Schatten norms
are *nondecreasing* in `p` (power-mean inequality). -/
theorem normalizedSchattenNorm_monotone
    [Nonempty n]
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (A : Matrix n n 𝕜) :
    normalizedSchattenNorm p A ≤ normalizedSchattenNorm q A := by
  have hq : 0 < q := by linarith
  rw [normalizedSchattenNorm_eq_sum hp, normalizedSchattenNorm_eq_sum hq]
  haveI : Nonempty (Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 n))) :=
    ⟨⟨0, by rw [finrank_euclideanSpace]; exact Fintype.card_pos⟩⟩
  have := powerMean_mono (SVDAux.sv (Matrix.toEuclideanLin A)) (SVDAux.sv_nonneg _) hp hpq
  simpa [finrank_euclideanSpace] using this

/-- The normalized Schatten norms of `diagonal ![1, 0]`. -/
theorem normalizedSchattenNorm_diag_one_zero {p : ℝ} (hp : 0 < p) :
    normalizedSchattenNorm p (Matrix.diagonal ![(1 : ℝ), 0]) = (1 / 2 : ℝ) ^ (1 / p) := by
  rw [normalizedSchattenNorm_eq_sum hp]
  have h := ExpAux.sum_sv_diagonal (𝕜 := ℝ) ![(1 : ℝ), 0] (fun s => s ^ p)
  simp only [RCLike.ofReal_real_eq_id, id] at h
  rw [show (Matrix.diagonal ![(1 : ℝ), 0]) = Matrix.diagonal fun j => ![(1 : ℝ), 0] j from rfl, h]
  simp [Fin.sum_univ_two, Real.zero_rpow hp.ne']

/-- Counterexample to the original `normalizedSchattenNorm_antitone`. -/
theorem normalizedSchattenNorm_antitone_counterexample :
    normalizedSchattenNorm 1 (Matrix.diagonal ![(1 : ℝ), 0]) <
      normalizedSchattenNorm 2 (Matrix.diagonal ![(1 : ℝ), 0]) := by
  rw [normalizedSchattenNorm_diag_one_zero one_pos, normalizedSchattenNorm_diag_one_zero two_pos]
  exact Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by norm_num)

/-- The negation of the original `normalizedSchattenNorm_antitone` (already for `2 × 2` real
matrices). -/
theorem not_normalizedSchattenNorm_antitone :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (p q : ℝ), 1 ≤ p → p ≤ q →
        normalizedSchattenNorm q A ≤ normalizedSchattenNorm p A := by
  intro h
  have := h (Matrix.diagonal ![(1 : ℝ), 0]) 1 2 le_rfl (by norm_num)
  exact absurd this (not_le.mpr normalizedSchattenNorm_antitone_counterexample)

/--
For Hermitian `H`, the Schatten norm of a Gibbs factor is an exact power of the partition function.
This is the normalized version of
`‖exp(-t β H)‖_{1/t} = (tr exp(-β H))^t`.
-/
theorem normalizedSchattenNorm_exp_hermitian
    [Nonempty n]
    (H : Matrix n n 𝕜) (hH : H.IsHermitian)
    (β : ℝ) {t : ℝ} (ht : 0 < t) :
    normalizedSchattenNorm (1 / t)
        (NormedSpace.exp ((-(t * β)) • H)) =
      ‖normalizedTrace (NormedSpace.exp ((-β) • H))‖ ^ t := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [normalizedSchattenNorm_eq_sum (one_div_pos.mpr ht), one_div_one_div,
    ExpAux.sum_sv_exp H hH _ (fun s => s ^ (1 / t)), normalizedTrace,
    ExpAux.trace_exp H hH, norm_mul, norm_inv, RCLike.norm_natCast, RCLike.norm_ofReal,
    abs_of_pos (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty), inv_mul_eq_div]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.exp_mul]
  congr 1
  field_simp

end Matrix

/-! ## 5. Iterated directional derivatives of `tr(exp A)` -/

namespace DirectionalDerivative

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Iterated directional Fréchet derivative.  The empty list gives `f x`; prepending a direction takes
one more directional derivative.
-/
noncomputable def iterDirectionalFDeriv (f : E → F) : List E → E → F
  | [], x => f x
  | v :: vs, x =>
      (fderiv ℝ (fun y => iterDirectionalFDeriv f vs y) x) v

/-- For smooth functions the iterated directional derivative is the iterated Fréchet derivative
evaluated at the list of directions. -/
theorem iterDirectionalFDeriv_eq_iteratedFDeriv (f : E → F) (hf : ContDiff ℝ ⊤ f)
    (dirs : List E) (x : E) :
    iterDirectionalFDeriv f dirs x = iteratedFDeriv ℝ dirs.length f x (fun i => dirs.get i) := by
  induction dirs generalizing x with
  | nil => simp [iterDirectionalFDeriv]
  | cons v vs ih =>
    have hfun : (fun y => iterDirectionalFDeriv f vs y) =
        fun y => iteratedFDeriv ℝ vs.length f y (fun i => vs.get i) := funext ih
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ vs.length f) x :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _) x
    simp only [iterDirectionalFDeriv]
    rw [hfun, fderiv_continuousMultilinear_apply_const_apply hdiff]
    show _ = iteratedFDeriv ℝ (vs.length + 1) f x (fun i => (v :: vs).get i)
    rw [iteratedFDeriv_succ_apply_left]
    rfl

end DirectionalDerivative

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Normalized trace exponential. -/
noncomputable def traceExp (A : Matrix n n 𝕜) : 𝕜 :=
  normalizedTrace (NormedSpace.exp A)

/--
General higher-derivative estimate for a Hermitian base point.

This packages the repeated Duhamel formula, the simplex volume cancellation, and Schatten Hölder:
each inserted direction contributes only its operator norm.
-/
theorem iterDirectionalFDeriv_traceExp_bound
    [Nonempty n]
    (A : Matrix n n 𝕜) (hA : A.IsHermitian)
    (dirs : List (Matrix n n 𝕜)) :
    ‖DirectionalDerivative.iterDirectionalFDeriv traceExp dirs A‖ ≤
      (dirs.map (fun B => ‖B‖)).prod * ‖traceExp A‖ := by
  have htE : (traceExp : Matrix n n 𝕜 → 𝕜) = DerivAux.tE := rfl
  rw [DirectionalDerivative.iterDirectionalFDeriv_eq_iteratedFDeriv traceExp
    (htE ▸ DerivAux.contDiff_tE) dirs A, htE, ← Fin.prod_univ_fun_getElem dirs norm]
  exact DerivAux.iteratedFDeriv_tE_bound_hermitian A hA _ _

/-- Unit-ball specialization of the higher derivative bound. -/
theorem iterDirectionalFDeriv_traceExp_bound_of_norm_le_one
    [Nonempty n]
    (A : Matrix n n 𝕜) (hA : A.IsHermitian)
    (dirs : List (Matrix n n 𝕜))
    (hdirs : ∀ B ∈ dirs, ‖B‖ ≤ 1) :
    ‖DirectionalDerivative.iterDirectionalFDeriv traceExp dirs A‖ ≤
      ‖traceExp A‖ := by
  refine (iterDirectionalFDeriv_traceExp_bound A hA dirs).trans ?_
  have hprod : (dirs.map (fun B => ‖B‖)).prod ≤ 1 := by
    rw [← Fin.prod_univ_fun_getElem dirs norm]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _)
      (fun i _ => hdirs _ (List.getElem_mem _))
  calc (dirs.map (fun B => ‖B‖)).prod * ‖traceExp A‖ ≤ 1 * ‖traceExp A‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖traceExp A‖ := one_mul _

end Matrix

end MatrixAnalysis

/-!
# The parity rule for the SYK partition function

We prove the sign-gauge invariance of the SYK partition function
`Z_N(β; G) = tr exp(-β H_N(G))` (for an even number `N` of Majorana generators,
realised as complex matrices), and deduce that its Gaussian expectation against
the multivariate Hermite polynomial `H_α(G)` vanishes whenever the multi-index
`α` is odd.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SYK

namespace MajoranaSystem

variable {N : ℕ} {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (M : MajoranaSystem N A)

theorem listProduct_mul_reverse (l : List (Fin N)) :
    (l.map M.ψ).prod * (l.reverse.map M.ψ).prod = 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (l.map M.ψ).prod, ih, one_mul, M.majorana_sq]

/-- The interaction index consisting of all labels except `x`. -/
def complementIndex (x : Fin N) : InteractionIndex N (N - 1) :=
  ⟨Finset.univ.erase x, by simp⟩

/-- The product of all generators except `ψ x` (a single-coordinate reflection). -/
noncomputable def reflection (x : Fin N) : A := M.psiProduct (complementIndex x)

/-- The inverse of `reflection x`. -/
noncomputable def reflectionInv (x : Fin N) : A :=
  ((orderedIndices (complementIndex x)).reverse.map M.ψ).prod

theorem reflection_mul_inv (x : Fin N) : M.reflection x * M.reflectionInv x = 1 :=
  M.listProduct_mul_reverse _

theorem reflectionInv_mul (x : Fin N) : M.reflectionInv x * M.reflection x = 1 := by
  have := M.listProduct_mul_reverse (orderedIndices (complementIndex x)).reverse
  rw [List.reverse_reverse] at this
  exact this

theorem reflection_mul_generator (hN : Even N) (x j : Fin N) :
    M.reflection x * M.ψ j =
      (if j = x then (-1 : ℂ) else 1) • (M.ψ j * M.reflection x) := by
  by_cases hjx : j = x
  · subst hjx
    have hnot : j ∉ orderedIndices (complementIndex j) := by
      simp [orderedIndices, complementIndex]
    have h := M.listProduct_mul_generator j (orderedIndices (complementIndex j)) hnot
    rw [length_orderedIndices] at h
    have hodd : Odd (N - 1) := by
      have := j.pos
      obtain ⟨m, hm⟩ := hN
      exact ⟨m - 1, by omega⟩
    rw [hodd.neg_one_pow] at h
    simpa [reflection, psiProduct] using h
  · have hmem : j ∈ (complementIndex x).1 := by simp [complementIndex, hjx]
    have h := M.psiProduct_mul_generator_of_mem (complementIndex x) j hmem
    have hev : Even (N - 1 - 1) := by
      obtain ⟨m, hm⟩ := hN
      exact ⟨m - 1, by omega⟩
    rw [hev.neg_one_pow] at h
    simpa [reflection, hjx] using h

/-- For every set `S` of labels there is an invertible element conjugating
`ψ j` to `-ψ j` for `j ∈ S` and fixing `ψ j` otherwise. -/
theorem exists_gauge (hN : Even N) (S : Finset (Fin N)) :
    ∃ U V : A, U * V = 1 ∧ V * U = 1 ∧
      ∀ j, U * M.ψ j = (if j ∈ S then (-1 : ℂ) else 1) • (M.ψ j * U) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 1, by simp, by simp, fun j => by simp⟩
  | @insert x S hx ih =>
    obtain ⟨U, V, hUV, hVU, hU⟩ := ih
    refine ⟨M.reflection x * U, V * M.reflectionInv x, ?_, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc U, hUV, one_mul, M.reflection_mul_inv]
    · rw [mul_assoc, ← mul_assoc (M.reflectionInv x), M.reflectionInv_mul, one_mul, hVU]
    · intro j
      rw [mul_assoc, hU j, Algebra.mul_smul_comm, ← mul_assoc, M.reflection_mul_generator hN,
        Algebra.smul_mul_assoc, smul_smul, mul_assoc]
      congr 1
      by_cases hj : j = x
      · subst hj; simp [hx]
      · simp [hj]

theorem mul_listProduct {U : A} {ε : Fin N → ℂ}
    (h : ∀ j, U * M.ψ j = ε j • (M.ψ j * U)) (l : List (Fin N)) :
    U * (l.map M.ψ).prod = (l.map ε).prod • ((l.map M.ψ).prod * U) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, h i, Algebra.smul_mul_assoc, mul_assoc, ih, Algebra.mul_smul_comm,
      smul_smul, mul_assoc]

theorem mul_interactionOperator {q : ℕ} {U : A} {ε : Fin N → ℂ}
    (h : ∀ j, U * M.ψ j = ε j • (M.ψ j * U)) (s : InteractionIndex N q) :
    U * M.interactionOperator s = (∏ j ∈ s.1, ε j) • (M.interactionOperator s * U) := by
  have hl := M.mul_listProduct h (orderedIndices s)
  have hprod : ((orderedIndices s).map ε).prod = ∏ j ∈ s.1, ε j := by
    rw [← List.prod_toFinset _ (by simp [orderedIndices])]
    simp [orderedIndices]
  rw [hprod] at hl
  change U * M.psiProduct s = _ • (M.psiProduct s * U) at hl
  rw [interactionOperator, Algebra.mul_smul_comm, hl, Algebra.smul_mul_assoc, smul_comm]

end MajoranaSystem

/-- The sign character `χ_s(I) = ∏_{x ∈ I} s_x`. -/
def signCharacter {N q : ℕ} (s : Fin N → ℝ) (I : InteractionIndex N q) : ℝ :=
  ∏ x ∈ I.1, s x

/-- The SYK partition function `Z_N(β; J) = tr exp(-β H_N(J))`, for Majorana generators
realised as `n × n` complex matrices. (Any normalisation `σ_N` of the Hamiltonian can be
absorbed into `β`.) -/
noncomputable def partitionFunction {n : Type*} [Fintype n] [DecidableEq n]
    (P : Params) (M : MajoranaSystem P.N (Matrix n n ℂ)) (β : ℝ)
    (J : InteractionIndex P.N P.q → ℝ) : ℂ :=
  (NormedSpace.exp (-(β : ℂ) • hamiltonian P M J)).trace

/-- Conjugation of the Hamiltonian by a gauge element. -/
theorem hamiltonian_gauge {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (P : Params) (hN : Even P.N) (M : MajoranaSystem P.N A) (J : InteractionIndex P.N P.q → ℝ)
    (s : Fin P.N → ℝ) (hs : ∀ x, s x = 1 ∨ s x = -1) :
    ∃ U V : A, U * V = 1 ∧ V * U = 1 ∧
      hamiltonian P M (fun I => signCharacter s I * J I) = U * hamiltonian P M J * V := by
  classical
  obtain ⟨U, V, hUV, hVU, hU⟩ := M.exists_gauge hN (Finset.univ.filter fun x => s x = -1)
  have hε : ∀ j, (if j ∈ Finset.univ.filter (fun x => s x = -1) then (-1 : ℂ) else 1) =
      ((s j : ℝ) : ℂ) := by
    intro j
    rcases hs j with h | h <;> norm_num [h]
  simp only [hε] at hU
  refine ⟨U, V, hUV, hVU, ?_⟩
  have key : U * hamiltonian P M J =
      hamiltonian P M (fun I => signCharacter s I * J I) * U := by
    rw [hamiltonian, hamiltonian, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Algebra.mul_smul_comm, M.mul_interactionOperator hU, smul_smul,
      Algebra.smul_mul_assoc]
    congr 1
    simp [signCharacter, mul_comm]
  rw [key, mul_assoc, hUV, mul_one]

/-- **Sign-gauge invariance** of the partition function:
`Z_N(β; G) = Z_N(β; (χ_s(I) g_I)_I)` for every `s ∈ {±1}^N`, when `N` is even. -/
theorem partitionFunction_sign_gauge {n : Type*} [Fintype n] [DecidableEq n]
    (P : Params) (hN : Even P.N) (M : MajoranaSystem P.N (Matrix n n ℂ)) (β : ℝ)
    (J : InteractionIndex P.N P.q → ℝ) (s : Fin P.N → ℝ) (hs : ∀ x, s x = 1 ∨ s x = -1) :
    partitionFunction P M β J =
      partitionFunction P M β (fun I => signCharacter s I * J I) := by
  obtain ⟨U, V, hUV, hVU, hH⟩ := hamiltonian_gauge P hN M J s hs
  have hunit : IsUnit U := ⟨⟨U, V, hUV, hVU⟩, rfl⟩
  have hinv : U⁻¹ = V := Matrix.inv_eq_right_inv hUV
  rw [partitionFunction, partitionFunction, hH]
  have : -(β : ℂ) • (U * hamiltonian P M J * V) = U * (-(β : ℂ) • hamiltonian P M J) * U⁻¹ := by
    rw [hinv, Matrix.mul_smul, Matrix.smul_mul]
  rw [this, Matrix.exp_conj _ _ hunit, hinv, Matrix.trace_mul_comm, ← mul_assoc, hVU, one_mul]

/-! ### Multi-indices, Hermite polynomials and the Gaussian expectation -/

/-- A multi-index `α` is even if `∑_{I ∋ x} α_I` is even for every `x ∈ [N]`. -/
def IsEvenMultiIndex {N q : ℕ} (α : InteractionIndex N q → ℕ) : Prop :=
  ∀ x : Fin N, Even (∑ I with x ∈ I.1, α I)

/-- A multi-index is odd if it is not even. -/
def IsOddMultiIndex {N q : ℕ} (α : InteractionIndex N q → ℕ) : Prop :=
  ¬ IsEvenMultiIndex α

/-- The multivariate (probabilists') Hermite polynomial `H_α(g) = ∏_I He_{α_I}(g_I)`. -/
noncomputable def hermiteMulti {ι : Type*} [Fintype ι] (α : ι → ℕ) (g : ι → ℝ) : ℝ :=
  ∏ I, Polynomial.aeval (g I) (Polynomial.hermite (α I))

/-- The law of the couplings: i.i.d. standard Gaussians. -/
noncomputable def gaussianCouplings (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

theorem hermite_aeval_neg (n : ℕ) (x : ℝ) :
    Polynomial.aeval (-x) (Polynomial.hermite n) =
      (-1) ^ n * Polynomial.aeval x (Polynomial.hermite n) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hodd : Odd (n + i)
  · simp [Polynomial.coeff_hermite_of_odd_add hodd]
  · have hev : Even (n + i) := Nat.not_odd_iff_even.mp hodd
    have hsign : ((-1 : ℝ)) ^ i = (-1) ^ n := by
      rcases Nat.even_or_odd n with hn | hn
      · have : Even i := by
          rcases Nat.even_or_odd i with hi | hi
          · exact hi
          · exact absurd (hn.add_odd hi) hodd
        rw [hn.neg_one_pow, this.neg_one_pow]
      · have : Odd i := by
          rcases Nat.even_or_odd i with hi | hi
          · exact absurd (hn.add_even hi) hodd
          · exact hi
        rw [hn.neg_one_pow, this.neg_one_pow]
    rw [neg_pow, hsign, zsmul_eq_mul, zsmul_eq_mul]
    ring

theorem hermite_aeval_sign (n : ℕ) (c x : ℝ) (hc : c = 1 ∨ c = -1) :
    Polynomial.aeval (c * x) (Polynomial.hermite n) =
      c ^ n * Polynomial.aeval x (Polynomial.hermite n) := by
  rcases hc with rfl | rfl
  · simp
  · rw [neg_one_mul, hermite_aeval_neg]

/-- Flipping the sign of the coordinates is measure preserving for i.i.d. Gaussians. -/
theorem integral_gaussianCouplings_sign {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (F : (ι → ℝ) → ℂ) :
    ∫ g, F (fun i => c i * g i) ∂gaussianCouplings ι = ∫ g, F g ∂gaussianCouplings ι := by
  have hsq : ∀ i, c i * c i = 1 := fun i => by rcases hc i with h | h <;> simp [h]
  let e1 : ∀ i, ℝ ≃ᵐ ℝ := fun i =>
    { toFun := fun x => c i * x
      invFun := fun x => c i * x
      left_inv := fun x => by simp only [← mul_assoc, hsq, one_mul]
      right_inv := fun x => by simp only [← mul_assoc, hsq, one_mul]
      measurable_toFun := measurable_const_mul (c i)
      measurable_invFun := measurable_const_mul (c i) }
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.piCongrRight e1
  have hmp : MeasurePreserving e (gaussianCouplings ι) (gaussianCouplings ι) := by
    refine measurePreserving_pi (f := fun i x => c i * x) _ _ fun i => ?_
    rcases hc i with h | h
    · simp only [h, one_mul]
      exact MeasurePreserving.id _
    · simp only [h, neg_one_mul]
      exact ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
  exact hmp.integral_comp' F

/-- **Parity rule.** If `α` is odd (and `N` is even), then `𝔼[Z_N(β; G) H_α(G)] = 0`
for i.i.d. standard Gaussian couplings `G`. -/
theorem expectation_partitionFunction_mul_hermite_eq_zero {n : Type*} [Fintype n]
    [DecidableEq n] (P : Params) (hN : Even P.N) (M : MajoranaSystem P.N (Matrix n n ℂ))
    (β : ℝ) (α : InteractionIndex P.N P.q → ℕ) (hα : IsOddMultiIndex α) :
    ∫ g, partitionFunction P M β g * (hermiteMulti α g : ℂ)
      ∂gaussianCouplings (InteractionIndex P.N P.q) = 0 := by
  classical
  have hex : ∃ x : Fin P.N, Odd (∑ I with x ∈ I.1, α I) := by
    by_contra h
    push_neg at h
    exact hα fun x => Nat.not_odd_iff_even.mp (h x)
  obtain ⟨x, hx⟩ := hex
  set s : Fin P.N → ℝ := fun y => if y = x then -1 else 1 with hs_def
  have hs : ∀ y, s y = 1 ∨ s y = -1 := fun y => by
    by_cases h : y = x <;> simp [hs_def, h]
  set c : InteractionIndex P.N P.q → ℝ := fun I => if x ∈ I.1 then -1 else 1 with hc_def
  have hc : ∀ I, c I = 1 ∨ c I = -1 := fun I => by
    by_cases h : x ∈ I.1 <;> simp [hc_def, h]
  have hsc : ∀ I, signCharacter s I = c I := fun I => by
    simp only [signCharacter, hs_def, hc_def]
    rw [Finset.prod_ite_eq']
  have hZ : ∀ g, partitionFunction P M β (fun I => c I * g I) = partitionFunction P M β g :=
    fun g => by
      rw [partitionFunction_sign_gauge P hN M β g s hs]
      simp only [hsc]
  have hH : ∀ g, hermiteMulti α (fun I => c I * g I) = -hermiteMulti α g := fun g => by
    simp only [hermiteMulti]
    simp only [fun I => hermite_aeval_sign (α I) (c I) (g I) (hc I)]
    rw [Finset.prod_mul_distrib]
    have : ∏ I, c I ^ α I = -1 := by
      have h1 : ∀ I, c I ^ α I = (-1 : ℝ) ^ (if x ∈ I.1 then α I else 0) := fun I => by
        by_cases h : x ∈ I.1 <;> simp [hc_def, h]
      simp only [h1]
      rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter, hx.neg_one_pow]
    rw [this, neg_one_mul]
  have key := integral_gaussianCouplings_sign c hc
    (fun g => partitionFunction P M β g * (hermiteMulti α g : ℂ))
  simp only [hZ, hH, Complex.ofReal_neg, mul_neg, integral_neg] at key
  linear_combination -key / 2
end SYK
