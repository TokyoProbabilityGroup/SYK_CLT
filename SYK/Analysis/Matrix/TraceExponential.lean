import SYK.Analysis.Matrix.SingularValues
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

@[expose] public section

set_option autoImplicit false

noncomputable section

/-!
# Matrix exponential and normalized trace bounds

The spectral estimates used below are in `SingularValues`. The file contains the radial chain
rule and the Duhamel formula for the first derivative of the exponential, the normalized
Schatten norms, and the trace bounds for words together with the Taylor coefficients of
`τ ∘ exp`. Main entry points:
`SYK.MatrixAnalysis.normalizedTrace`, `SYK.MatrixAnalysis.normalizedSchattenNorm`,
`SYK.MatrixAnalysis.word_trace_bound`.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace SYK.MatrixAnalysis.PositiveTrace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Inserting a bounded operator next to a positive one costs only its operator norm. -/
theorem norm_trace_comp_positive_le (P B : E →ₗ[𝕜] E) (hP : P.IsPositive) :
    ‖LinearMap.trace 𝕜 E (B ∘ₗ P)‖ ≤
      ‖B.toContinuousLinearMap‖ *
        (∑ i : Fin (Module.finrank 𝕜 E), hP.isSymmetric.eigenvalues rfl i) := by
  let b := hP.isSymmetric.eigenvectorBasis rfl
  rw [LinearMap.trace_eq_sum_inner (B ∘ₗ P) b]
  calc
    ‖∑ i, ⟪b i, (B ∘ₗ P) (b i)⟫_𝕜‖ ≤
        ∑ i, ‖⟪b i, (B ∘ₗ P) (b i)⟫_𝕜‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖B.toContinuousLinearMap‖ * hP.isSymmetric.eigenvalues rfl i := by
      apply Finset.sum_le_sum
      intro i _
      rw [LinearMap.comp_apply, hP.isSymmetric.apply_eigenvectorBasis]
      simp only [map_smul, inner_smul_right]
      have hinner := norm_inner_le_norm (𝕜 := 𝕜) (b i) (B (b i))
      have hb : ‖b i‖ = 1 := b.norm_eq_one i
      rw [hb, one_mul] at hinner
      have hB : ‖B (b i)‖ ≤ ‖B.toContinuousLinearMap‖ := by
        simpa [hb] using B.toContinuousLinearMap.le_opNorm (b i)
      rw [norm_mul, RCLike.norm_ofReal,
        abs_of_nonneg (hP.nonneg_eigenvalues rfl i)]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right (hinner.trans hB) (hP.nonneg_eigenvalues rfl i)
    _ = ‖B.toContinuousLinearMap‖ *
          (∑ i, hP.isSymmetric.eigenvalues rfl i) := by
      rw [Finset.mul_sum]

/-- The trace bound expressed using the trace of the positive operator. -/
theorem norm_trace_comp_positive_le_norm_trace (P B : E →ₗ[𝕜] E)
    (hP : P.IsPositive) :
    ‖LinearMap.trace 𝕜 E (B ∘ₗ P)‖ ≤
      ‖B.toContinuousLinearMap‖ * ‖LinearMap.trace 𝕜 E P‖ := by
  have hsum : 0 ≤ ∑ i : Fin (Module.finrank 𝕜 E),
      hP.isSymmetric.eigenvalues rfl i :=
    Finset.sum_nonneg (fun i _ => hP.nonneg_eigenvalues rfl i)
  have hnorm : ‖LinearMap.trace 𝕜 E P‖ =
      ∑ i : Fin (Module.finrank 𝕜 E), hP.isSymmetric.eigenvalues rfl i := by
    rw [hP.isSymmetric.trace_eq_sum_eigenvalues rfl,
      RCLike.norm_ofReal, abs_of_nonneg hsum]
  rw [hnorm]
  exact norm_trace_comp_positive_le P B hP

end SYK.MatrixAnalysis.PositiveTrace



open scoped Matrix.Norms.L2Operator

noncomputable section

namespace SYK.MatrixAnalysis.ExpAux

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private theorem exp_smul_spectral (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    NormedSpace.exp (β • H) =
      (↑hH.eigenvectorUnitary : Matrix n n 𝕜) *
        Matrix.diagonal (fun j => (Real.exp (β * hH.eigenvalues j) : 𝕜)) *
          star (↑hH.eigenvectorUnitary : Matrix n n 𝕜) := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  have hstar : star (↑hH.eigenvectorUnitary : Matrix n n 𝕜) =
      (↑hH.eigenvectorUnitary : Matrix n n 𝕜)⁻¹ :=
    (Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self hH.eigenvectorUnitary)).symm
  rw [hstar, Matrix.exp_conj _ _ Unitary.isUnit_coe, ← hstar]
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  have hdiag : Matrix.diagonal (NormedSpace.exp (β • RCLike.ofReal ∘ hH.eigenvalues)) =
      Matrix.diagonal (fun j => (Real.exp (β * hH.eigenvalues j) : 𝕜)) := by
    congr 1
    funext j
    rw [Pi.coe_exp]
    simp only [Pi.smul_apply, Function.comp_apply]
    rw [RCLike.real_smul_ofReal, ← RCLike.ofReal_mul]
    change NormedSpace.exp ((β * hH.eigenvalues j : ℝ) : 𝕜) =
      (Real.exp (β * hH.eigenvalues j) : 𝕜)
    simpa only [RCLike.ofReal_alg, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.map_exp (algebraMap ℝ 𝕜) (continuous_algebraMap ℝ 𝕜)
        (β * hH.eigenvalues j)).symm
  rw [hdiag]

private theorem charpoly_exp_smul (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).charpoly =
      ∏ j, (Polynomial.X - Polynomial.C (Real.exp (β * hH.eigenvalues j) : 𝕜)) := by
  rw [exp_smul_spectral H hH β, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.charpoly_diagonal]

private theorem roots_charpoly_exp_smul (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).charpoly.roots =
      Multiset.map (fun j => (Real.exp (β * hH.eigenvalues j) : 𝕜)) Finset.univ.val := by
  rw [charpoly_exp_smul H hH β]
  rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr (fun j _ =>
    Polynomial.X_sub_C_ne_zero _))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

private theorem charpoly_toEuclideanLin (A : Matrix n n 𝕜) :
    (Matrix.toEuclideanLin A).charpoly = A.charpoly := by
  rw [← LinearMap.charpoly_toMatrix (Matrix.toEuclideanLin A)
    (EuclideanSpace.basisFun n 𝕜).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

section
open scoped ComplexOrder

private theorem exp_smul_posSemidef (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).PosSemidef := by
  rw [exp_smul_spectral H hH β]
  have hU : IsUnit (↑hH.eigenvectorUnitary : Matrix n n 𝕜) := Unitary.isUnit_coe
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU]
  rw [Matrix.posSemidef_diagonal_iff]
  exact fun i => RCLike.ofReal_nonneg.mpr (Real.exp_pos _).le

private theorem exp_smul_posDef (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).PosDef := by
  rw [exp_smul_spectral H hH β]
  have hU : IsUnit (↑hH.eigenvectorUnitary : Matrix n n 𝕜) := Unitary.isUnit_coe
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff hU]
  rw [Matrix.posDef_diagonal_iff]
  exact fun i => RCLike.ofReal_pos.mpr (Real.exp_pos _)

end

private theorem sum_eigenvalues_exp_smul (H : Matrix n n 𝕜) (hH : H.IsHermitian)
    (β : ℝ) (f : ℝ → ℝ)
    (hT : (Matrix.toEuclideanLin (NormedSpace.exp (β • H))).IsPositive) :
    ∑ i : Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 n)),
      f (hT.isSymmetric.eigenvalues rfl i) =
        ∑ j, f (Real.exp (β * hH.eigenvalues j)) := by
  exact sum_eigenvalues_eq_of_basis _ hT.isSymmetric hH.eigenvectorBasis
    (fun j => Real.exp (β * hH.eigenvalues j)) (fun j => by
      rw [exp_smul_spectral H hH β]
      exact toEuclideanLin_conj_diagonal_apply H hH _ j) f

end SYK.MatrixAnalysis.ExpAux


namespace SYK.MatrixAnalysis.SVDAux

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open Polynomial

private noncomputable def sv (T : E →ₗ[𝕜] E) (i : Fin (Module.finrank 𝕜 E)) : ℝ :=
  T.singularValues i

private theorem sv_nonneg (T : E →ₗ[𝕜] E) (i : Fin (Module.finrank 𝕜 E)) :
    0 ≤ sv T i := T.singularValues_nonneg i

private theorem singularValues_sum_rpow (T : E →ₗ[𝕜] E) {p : ℝ} (hp : 0 < p) :
    T.singularValues.sum (fun _ s => s ^ p) =
      ∑ i : Fin (Module.finrank 𝕜 E), sv T i ^ p := by
  unfold sv
  have hfin : (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues (i : ℕ) ^ p) =
      ∑ i ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues i ^ p := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Nat.not_le.mpr (Finset.mem_range.mp hi)]
  rw [hfin]
  refine T.singularValues.sum_of_support_subset
    (s := Finset.range (Module.finrank 𝕜 E)) ?_ (fun _ (s : ℝ) => s ^ p) ?_
  · intro i hi
    by_contra h
    have hz := T.singularValues_of_finrank_le (Nat.le_of_not_gt (Finset.mem_range.not.mp h))
    exact (Finsupp.mem_support_iff.mp hi) hz
  · intro i hi
    simp [Real.zero_rpow hp.ne']

private theorem charpoly_adjoint_comp_self_of_positive (T : E →ₗ[𝕜] E) (hT : T.IsPositive) :
    (T.adjoint ∘ₗ T).charpoly =
      ∏ i : Fin (Module.finrank 𝕜 E),
        (X - C ((hT.isSymmetric.eigenvalues rfl i ^ 2 : ℝ) : 𝕜)) := by
  let b := (hT.isSymmetric.eigenvectorBasis rfl).toBasis
  have hmat : LinearMap.toMatrix b b (T.adjoint ∘ₗ T) =
      Matrix.diagonal (fun i => ((hT.isSymmetric.eigenvalues rfl i ^ 2 : ℝ) : 𝕜)) := by
    ext i j
    have hbj : b j = hT.isSymmetric.eigenvectorBasis rfl j := congrFun (OrthonormalBasis.coe_toBasis _) j
    rw [LinearMap.toMatrix_apply, hT.adjoint_eq, LinearMap.comp_apply, hbj,
      hT.isSymmetric.apply_eigenvectorBasis, map_smul, hT.isSymmetric.apply_eigenvectorBasis,
      smul_smul, ← hbj, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp [sq]
    · simp [hij, Ne.symm hij]
  rw [← LinearMap.charpoly_toMatrix (T.adjoint ∘ₗ T) b, hmat, Matrix.charpoly_diagonal]

private theorem eigenvalues_adjoint_comp_self_of_positive (T : E →ₗ[𝕜] E)
    (hT : T.IsPositive) :
    T.isSymmetric_adjoint_comp_self.eigenvalues rfl =
      fun i => (hT.isSymmetric.eigenvalues rfl i) ^ 2 :=
  eigenvalues_adjoint_comp_self_of_positive' T hT

private theorem singularValues_fin_of_positive (T : E →ₗ[𝕜] E) (hT : T.IsPositive)
    (i : Fin (Module.finrank 𝕜 E)) :
    T.singularValues i = hT.isSymmetric.eigenvalues rfl i := by
  rw [T.singularValues_fin rfl,
    eigenvalues_adjoint_comp_self_of_positive T hT,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (hT.nonneg_eigenvalues rfl i)]

end SYK.MatrixAnalysis.SVDAux

namespace SYK.MatrixAnalysis.ExpAux

private theorem sum_sv_exp {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) (f : ℝ → ℝ) :
    ∑ i : Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 n)),
      f (SVDAux.sv (Matrix.toEuclideanLin (NormedSpace.exp (β • H))) i) =
        ∑ j, f (Real.exp (β * hH.eigenvalues j)) := by
  let T := Matrix.toEuclideanLin (NormedSpace.exp (β • H))
  have hT : T.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (exp_smul_posSemidef H hH β)
  simpa only [SVDAux.sv, T, SVDAux.singularValues_fin_of_positive T hT] using
    sum_eigenvalues_exp_smul H hH β f hT

end SYK.MatrixAnalysis.ExpAux


open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory

/-!
# Reusable spectral and analytic lemmas for finite-dimensional matrix Gibbs functions

`SingularValues` develops singular values, eigenvalue comparisons, and Schatten bounds.
The sections below turn these tools into estimates for matrix exponentials.

The main reusable pieces are:

* a radial chain rule for scalar rescaling;
* a Banach-algebra Duhamel formula for the derivative of the exponential;
* normalized trace and normalized Schatten norms;
* Schatten Hölder and operator-norm multiplication bounds;
* the exact Schatten norm of an exponential of a Hermitian matrix;
* positive-trace and word bounds, followed by change-of-origin Taylor-coefficient estimates;
The higher-derivative bound itself is in `TraceExpDerivatives`: it uses the word and
Taylor-coefficient bounds here after shifting the Hermitian base point to a positive matrix.
-/

namespace SYK.MatrixAnalysis

/-! ## Radial chain rule -/

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

/-! ## Duhamel formula

The integral kernel represents the first derivative of the exponential without assuming
commutativity. Cyclicity of the trace later removes the position of the inserted direction.
Higher derivatives in `TraceExpDerivatives` use the analytic power-series bounds instead.
-/

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
    · rfl
    · rw [neg_smul, one_smul]
      noncomm_ring
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

/-- The full Fréchet derivative of the Banach-algebra exponential in a direction. -/
theorem fderiv_exp_apply (X V : 𝔸) :
    (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) X) V =
      ∫ s : ℝ in (0 : ℝ)..1, kernel X V s := by
  have hdiff : DifferentiableAt ℝ (NormedSpace.exp : 𝔸 → 𝔸) X :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) X).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => X + t • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add X
  have hbase : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) X) (X + (0 : ℝ) • V) := by
    simpa using hdiff.hasFDerivAt
  have hchain := hbase.comp_hasDerivAt 0 hline
  have hduhamel := (hasFDerivAt_exp_affine X V 0).hasDerivAt
  simpa [kernel] using hchain.unique hduhamel

end Duhamel

/-! ## Normalized Schatten norms

Finite-dimensional Hölder bounds control products of matrices. Dividing the trace by the
dimension gives the normalization used for partition functions; operator-norm factors handle
directions that need no finite Schatten exponent.
-/

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
    {p : ℝ} (_hp : 0 < p) (T : E →ₗ[𝕜] E) :
    0 ≤ normalizedNorm p T := by
  unfold normalizedNorm powerSum
  refine Real.rpow_nonneg (div_nonneg ?_ (Nat.cast_nonneg _)) _
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (T.singularValues_nonneg i) _

end Schatten

namespace SchattenAux

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The absolute trace is bounded by the sum of singular values. -/
private theorem norm_trace_le (T : E →ₗ[𝕜] E) :
    ‖LinearMap.trace 𝕜 E T‖ ≤
      ∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  rw [T.trace_eq_sum_inner b]
  calc
    ‖∑ i, ⟪b i, T (b i)⟫_𝕜‖ ≤ (∑ i, ‖⟪b i, T (b i)⟫_𝕜‖) :=
      norm_sum_le _ _
    _ ≤ (∑ i, ‖T (b i)‖) := by
      apply Finset.sum_le_sum
      intro i _
      simpa using (norm_inner_le_norm (b i) (T (b i)))
    _ = (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [T.singularValues_fin rfl, norm_eq_sqrt_re_inner (𝕜 := 𝕜)]
      congr 1
      rw [← T.adjoint_inner_left (b i) (T (b i))]
      change RCLike.re ⟪(T.adjoint ∘ₗ T) (b i), b i⟫_𝕜 =
        T.isSymmetric_adjoint_comp_self.eigenvalues rfl i
      rw [T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i]
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp

private theorem sum_sv_rpow_eq_sum_range (T : E →ₗ[𝕜] E) (p : ℝ) :
    ∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv T i ^ p =
      ∑ i ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues i ^ p :=
  Fin.sum_univ_eq_sum_range (fun i => T.singularValues i ^ p) _

/-- **Schatten–Hölder inequality** for singular value sums. -/
private theorem holder (T S : E →ₗ[𝕜] E) {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hrecip : 1 / r = 1 / p + 1 / q) :
    (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv (T ∘ₗ S) i ^ r) ^ (1 / r) ≤
      (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv T i ^ p) ^ (1 / p) *
        (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv S i ^ q) ^ (1 / q) := by
  simp only [sum_sv_rpow_eq_sum_range]
  exact schatten_holder T S hp hq hr hrecip

/-- Right multiplication by a bounded operator in Schatten norm. -/
private theorem mul_opNorm (T S : E →ₗ[𝕜] E) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv (T ∘ₗ S) i ^ p) ^ (1 / p) ≤
      (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv T i ^ p) ^ (1 / p) *
        ‖S.toContinuousLinearMap‖ := by
  simp only [sum_sv_rpow_eq_sum_range]
  exact schatten_comp_right_le T S _ (norm_nonneg _)
    (fun v => S.toContinuousLinearMap.le_opNorm v) (by linarith)

/-- Left multiplication by a bounded operator in Schatten norm. -/
private theorem opNorm_mul (T S : E →ₗ[𝕜] E) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv (T ∘ₗ S) i ^ p) ^ (1 / p) ≤
      ‖T.toContinuousLinearMap‖ *
        (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv S i ^ p) ^ (1 / p) := by
  simp only [sum_sv_rpow_eq_sum_range]
  exact schatten_comp_left_le T S _ (norm_nonneg _)
    (fun v => T.toContinuousLinearMap.le_opNorm v) (by linarith)

end SchattenAux

section

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The trace of a Hermitian matrix exponential as a sum over real eigenvalues. -/
theorem trace_exp_smul_of_isHermitian (H : Matrix n n 𝕜)
    (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).trace =
      ∑ j, (Real.exp (β * hH.eigenvalues j) : 𝕜) := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  have hstar : star (↑hH.eigenvectorUnitary : Matrix n n 𝕜) =
      (↑hH.eigenvectorUnitary : Matrix n n 𝕜)⁻¹ :=
    (Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self hH.eigenvectorUnitary)).symm
  rw [hstar]
  rw [Matrix.exp_conj _ _ Unitary.isUnit_coe, Matrix.trace_mul_comm]
  rw [← mul_assoc, ← hstar, Unitary.coe_star_mul_self, one_mul]
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.coe_exp]
  simp only [Pi.smul_apply, Function.comp_apply]
  rw [RCLike.real_smul_ofReal, ← RCLike.ofReal_mul]
  change NormedSpace.exp ((β * hH.eigenvalues i : ℝ) : 𝕜) =
    (Real.exp (β * hH.eigenvalues i) : 𝕜)
  simpa only [RCLike.ofReal_alg, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.map_exp (algebraMap ℝ 𝕜) (continuous_algebraMap ℝ 𝕜)
      (β * hH.eigenvalues i)).symm

end

namespace ExpAux

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A Hermitian matrix exponential has strictly positive real trace. -/
private theorem trace_exp_re_pos [Nonempty n]
    (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    0 < RCLike.re (NormedSpace.exp (β • H)).trace := by
  rw [trace_exp_smul_of_isHermitian H hH β]
  simp only [map_sum, RCLike.ofReal_re]
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

end ExpAux

section

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Normalized matrix trace `card(n)⁻¹ * Tr(A)`. It allows an empty index type and is
distinct from `SYK.normalizedTrace` in `SYK.Model.FiniteDimensionalGibbs`. -/
noncomputable def normalizedTrace (A : Matrix n n 𝕜) : 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ * A.trace

/-- Normalized trace as a continuous linear map. -/
noncomputable def normalizedTraceCLM : Matrix n n 𝕜 →L[𝕜] 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ • (Matrix.traceLinearMap n 𝕜 𝕜).toContinuousLinearMap

omit [DecidableEq n] in
@[simp] theorem normalizedTraceCLM_apply (A : Matrix n n 𝕜) :
    normalizedTraceCLM A = normalizedTrace A := by
  simp [normalizedTraceCLM, normalizedTrace]

omit [DecidableEq n] in
@[simp] theorem normalizedTrace_zero :
    normalizedTrace (0 : Matrix n n 𝕜) = 0 := by
  simp [normalizedTrace]

@[simp] theorem normalizedTrace_one [Nonempty n] :
    normalizedTrace (1 : Matrix n n 𝕜) = 1 := by
  have : (Fintype.card n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [normalizedTrace, Matrix.trace_one, this]

omit [DecidableEq n] in
theorem normalizedTrace_add (A B : Matrix n n 𝕜) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_add, mul_add]

omit [DecidableEq n] in
theorem normalizedTrace_smul (c : 𝕜) (A : Matrix n n 𝕜) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, Matrix.trace_smul, mul_left_comm]

omit [DecidableEq n] in
/-- Cyclicity for two factors. -/
theorem normalizedTrace_mul_comm (A B : Matrix n n 𝕜) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  simp [normalizedTrace, Matrix.trace_mul_comm A B]

/-- Cyclicity makes the trace of a one-insertion Duhamel word independent of the weight. -/
theorem normalizedTrace_duhamel_kernel (A B : Matrix n n 𝕜) (s : ℝ) :
    normalizedTrace (NormedSpace.exp (s • A) * B *
      NormedSpace.exp ((1 - s) • A)) =
      normalizedTrace (B * NormedSpace.exp A) := by
  have hcomm : Commute ((1 - s) • A) (s • A) :=
    ((Commute.refl A).smul_left (1 - s)).smul_right s
  calc
    normalizedTrace (NormedSpace.exp (s • A) * B * NormedSpace.exp ((1 - s) • A)) =
        normalizedTrace (NormedSpace.exp ((1 - s) • A) *
          (NormedSpace.exp (s • A) * B)) :=
      normalizedTrace_mul_comm _ _
    _ = normalizedTrace ((NormedSpace.exp ((1 - s) • A) *
          NormedSpace.exp (s • A)) * B) := by rw [mul_assoc]
    _ = normalizedTrace (NormedSpace.exp (((1 - s) • A) + (s • A)) * B) := by
      rw [Matrix.exp_add_of_commute _ _ hcomm]
    _ = normalizedTrace (B * NormedSpace.exp A) := by
      rw [← add_smul, sub_add_cancel, one_smul, normalizedTrace_mul_comm]

/-- Normalized Schatten `p`-norm of a matrix, using its Euclidean linear map. -/
noncomputable def normalizedSchattenNorm (p : ℝ) (A : Matrix n n 𝕜) : ℝ :=
  Schatten.normalizedNorm p (Matrix.toEuclideanLin A)

/-! ### Auxiliary facts relating matrices to their Euclidean linear maps -/

private theorem normalizedSchattenNorm_eq_sum {p : ℝ} (hp : 0 < p) (A : Matrix n n 𝕜) :
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

/-- A Hermitian Gibbs factor is positive, so a neighboring matrix costs its operator norm. -/
theorem norm_trace_mul_exp_hermitian_le (A B : Matrix n n 𝕜) (hA : A.IsHermitian) :
    ‖(B * NormedSpace.exp A).trace‖ ≤ ‖B‖ * ‖(NormedSpace.exp A).trace‖ := by
  let P := Matrix.toEuclideanLin (NormedSpace.exp A)
  have hP : P.IsPositive := by
    dsimp [P]
    simpa only [one_smul] using
      Matrix.isPositive_toEuclideanLin_iff.mpr (ExpAux.exp_smul_posSemidef A hA 1)
  have h := PositiveTrace.norm_trace_comp_positive_le_norm_trace
    P (Matrix.toEuclideanLin B) hP
  simpa only [P, ← toEuclideanLin_mul', ← trace_eq_trace_toEuclideanLin,
    norm_toContinuousLinearMap_toEuclideanLin] using h

/-- Normalized version of the positive trace insertion estimate. -/
theorem norm_normalizedTrace_mul_exp_hermitian_le (A B : Matrix n n 𝕜)
    (hA : A.IsHermitian) :
    ‖normalizedTrace (B * NormedSpace.exp A)‖ ≤
      ‖B‖ * ‖normalizedTrace (NormedSpace.exp A)‖ := by
  have h := norm_trace_mul_exp_hermitian_le A B hA
  calc
    ‖normalizedTrace (B * NormedSpace.exp A)‖ =
        ‖(Fintype.card n : 𝕜)⁻¹‖ * ‖(B * NormedSpace.exp A).trace‖ := by
      rw [normalizedTrace, norm_mul]
    _ ≤ ‖(Fintype.card n : 𝕜)⁻¹‖ *
        (‖B‖ * ‖(NormedSpace.exp A).trace‖) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖B‖ * ‖normalizedTrace (NormedSpace.exp A)‖ := by
      rw [normalizedTrace, norm_mul]
      ring

private theorem sum_sv_rpow_nonneg (A : Matrix n n 𝕜) (p : ℝ) :
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
  simpa [SVDAux.sv] using SchattenAux.norm_trace_le (Matrix.toEuclideanLin A)

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

/-!
Dimension-normalized Schatten norms are nondecreasing in the exponent. The matrix
`diagonal ![1, 0]` gives a counterexample to the reverse inequality below.
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

/-- Dimension-normalized Schatten norms are nondecreasing in `p` by the power-mean inequality. -/
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

private def diagOneZero : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![(1 : ℝ), 0]

private lemma diagOneZero_star : diagOneZero.conjTranspose = diagOneZero := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOneZero, Matrix.conjTranspose_apply]

private lemma diagOneZero_mul : diagOneZero * diagOneZero = diagOneZero := by
  simp [diagOneZero, Matrix.diagonal_mul_diagonal]

private lemma diagOneZero_adjoint_comp :
    (Matrix.toEuclideanLin diagOneZero).adjoint ∘ₗ Matrix.toEuclideanLin diagOneZero =
      Matrix.toEuclideanLin diagOneZero := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, diagOneZero_star]
  rw [← toEuclideanLin_mul', diagOneZero_mul]

private lemma diagOneZero_det :
    LinearMap.det (Matrix.toEuclideanLin diagOneZero) = 0 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  simp [diagOneZero, Matrix.det_diagonal]

private lemma diagOneZero_trace :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
      (Matrix.toEuclideanLin diagOneZero) = 1 := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    LinearMap.toMatrix_toLin]
  simp [diagOneZero, Matrix.trace_diagonal, Fin.sum_univ_two]

private lemma diagOneZero_singularValues :
    (Matrix.toEuclideanLin diagOneZero).singularValues 0 = 1 ∧
      (Matrix.toEuclideanLin diagOneZero).singularValues 1 = 0 := by
  let T := Matrix.toEuclideanLin diagOneZero
  let hS := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
    simp [finrank_euclideanSpace]
  have heig : hS.eigenvalues hn = ![1, 0] := by
    refine eigenvalues_eq_of_basis _ hS hn (EuclideanSpace.basisFun (Fin 2) ℝ) _
      ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro j
      have hT : T.adjoint ∘ₗ T = T := diagOneZero_adjoint_comp
      rw [hT]
      ext i
      fin_cases i <;> fin_cases j <;>
        simp [T, diagOneZero, Matrix.toLpLin_apply]
  constructor
  · rw [T.singularValues_of_lt hn (by decide : 0 < 2), heig]
    simp
  · rw [T.singularValues_of_lt hn (by decide : 1 < 2), heig]
    simp

/-- The normalized Schatten norms of `diagonal ![1, 0]`. -/
theorem normalizedSchattenNorm_diag_one_zero {p : ℝ} (hp : 0 < p) :
    normalizedSchattenNorm p (Matrix.diagonal ![(1 : ℝ), 0]) = (1 / 2 : ℝ) ^ (1 / p) := by
  rw [normalizedSchattenNorm_eq_sum hp]
  simp only [SVDAux.sv, Fintype.card_fin]
  rw [finrank_euclideanSpace]
  change ((∑ i : Fin 2, (Matrix.toEuclideanLin diagOneZero).singularValues i ^ p) /
    (2 : ℝ)) ^ (1 / p) = (1 / 2 : ℝ) ^ (1 / p)
  obtain ⟨h0, h1⟩ := diagOneZero_singularValues
  simp [Fin.sum_univ_two, h0, h1, Real.zero_rpow hp.ne']

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
    trace_exp_smul_of_isHermitian H hH, norm_mul, norm_inv, RCLike.norm_natCast, ← map_sum,
    RCLike.norm_ofReal,
    abs_of_pos (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty), inv_mul_eq_div]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.exp_mul]
  congr 1
  field_simp


/-! ### Trace bounds for words and the Taylor coefficients of `τ ∘ exp`

`word_schatten_bound` counts the copies of one base matrix in a noncommutative word.
`word_trace_bound` then controls its trace, with an operator norm for each inserted direction.
`changeOrigin_coef_bound` sums these words to estimate each Taylor coefficient at the base point.
These are the inputs to the Hermitian higher-derivative estimate in `TraceExpDerivatives`.
-/

section WordBounds

open scoped Nat

theorem normalizedSchattenNorm_nonneg' {p : ℝ} (hp : 0 < p) (A : Matrix n n 𝕜) :
    0 ≤ normalizedSchattenNorm p A := by
  rw [normalizedSchattenNorm_eq_sum hp]
  exact Real.rpow_nonneg (div_nonneg (sum_sv_rpow_nonneg A p) (Nat.cast_nonneg _)) _

/-- Schatten bound for a word in which the letters in `P` are `D` and the other letters are
arbitrary matrices. -/
theorem word_schatten_bound [Nonempty n] (D : Matrix n n 𝕜) :
    ∀ (N : ℕ) (m : Fin N → Matrix n n 𝕜) (P : Fin N → Prop) [DecidablePred P],
      (∀ i, P i → m i = D) → ∀ (l : ℝ), ((Finset.univ.filter P).card : ℝ) ≤ l →
      ((Finset.univ.filter P).card = 0 →
          ‖(List.ofFn m).prod‖ ≤ ∏ i, if P i then 1 else ‖m i‖) ∧
        (1 ≤ (Finset.univ.filter P).card →
          normalizedSchattenNorm (l / (Finset.univ.filter P).card) (List.ofFn m).prod ≤
            (∏ i, if P i then 1 else ‖m i‖) *
              normalizedSchattenNorm l D ^ (Finset.univ.filter P).card) := by
  intro N
  induction N with
  | zero =>
    intro m P _ _ l _
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]
    exact le_of_eq (norm_one)
  | succ N ih =>
    intro m P _ hP l hl
    have hcard := Fin.card_filter_univ_succ' P
    obtain ⟨ih1, ih2⟩ := ih (fun i => m i.succ) (fun i => P i.succ) (fun i hi => hP _ hi) l
      (by
        refine le_trans ?_ hl
        rw [hcard]
        exact_mod_cast Nat.le_add_left _ _)
    set c := (Finset.univ.filter fun i : Fin N => P i.succ).card with hc
    set W := (List.ofFn fun i : Fin N => m i.succ).prod with hW
    set wt := ∏ i : Fin N, if P i.succ then 1 else ‖m i.succ‖ with hwt
    have hwt0 : 0 ≤ wt := Finset.prod_nonneg fun i _ => by split_ifs <;> positivity
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, hcard]
    by_cases h0 : P 0
    · simp only [h0, if_true, one_mul]
      rw [hP 0 h0]
      refine ⟨fun h => by omega, fun _ => ?_⟩
      have hl1 : 1 ≤ l := by
        refine le_trans ?_ hl
        rw [hcard]
        simp [h0]
      rcases Nat.eq_zero_or_pos c with hc0 | hcpos
      · simp only [hc0, add_zero, Nat.cast_one, div_one, pow_one]
        calc normalizedSchattenNorm l (D * W) ≤ normalizedSchattenNorm l D * ‖W‖ :=
              normalizedSchattenNorm_mul_opNorm_le hl1 D W
          _ ≤ normalizedSchattenNorm l D * wt :=
              mul_le_mul_of_nonneg_left (ih1 hc0) (normalizedSchattenNorm_nonneg' (by linarith) D)
          _ = wt * normalizedSchattenNorm l D := mul_comm _ _
      · have hcl : (c : ℝ) + 1 ≤ l := by
          have := hl
          rw [hcard] at this
          simpa [h0, add_comm] using this
        have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hcpos
        have hlpos : 0 < l := by linarith
        have hholder := normalizedSchattenNorm_mul_le (p := l) (q := l / c) (r := l / (1 + c))
          hl1 (by rw [le_div_iff₀ (by linarith)]; linarith)
          (by rw [le_div_iff₀ (by linarith)]; linarith)
          (by field_simp) D W
        push_cast
        calc normalizedSchattenNorm (l / (1 + c)) (D * W)
            ≤ normalizedSchattenNorm l D * normalizedSchattenNorm (l / c) W := hholder
          _ ≤ normalizedSchattenNorm l D * (wt * normalizedSchattenNorm l D ^ c) :=
              mul_le_mul_of_nonneg_left (ih2 hcpos) (normalizedSchattenNorm_nonneg' hlpos D)
          _ = wt * normalizedSchattenNorm l D ^ (1 + c) := by ring
    · simp only [h0, if_false, zero_add]
      refine ⟨fun hc0 => ?_, fun hcpos => ?_⟩
      · calc ‖m 0 * W‖ ≤ ‖m 0‖ * ‖W‖ := norm_mul_le _ _
          _ ≤ ‖m 0‖ * wt := mul_le_mul_of_nonneg_left (ih1 hc0) (norm_nonneg _)
      · have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hcpos
        have hcl : (c : ℝ) ≤ l := by
          have := hl
          rw [hcard] at this
          simpa [h0] using this
        calc normalizedSchattenNorm (l / c) (m 0 * W)
            ≤ ‖m 0‖ * normalizedSchattenNorm (l / c) W :=
              normalizedSchattenNorm_opNorm_mul_le
                (by rw [le_div_iff₀ (by linarith)]; linarith) _ _
          _ ≤ ‖m 0‖ * (wt * normalizedSchattenNorm l D ^ c) :=
              mul_le_mul_of_nonneg_left (ih2 hcpos) (norm_nonneg _)
          _ = ‖m 0‖ * wt * normalizedSchattenNorm l D ^ c := by ring

/-- The trace of a word is controlled by the trace of the corresponding power of `D`, when the
normalized Schatten norms of `D` are computed by traces of its powers. -/
theorem word_trace_bound [Nonempty n] (D : Matrix n n 𝕜)
    (hD : ∀ l : ℕ, 1 ≤ l → normalizedSchattenNorm l D ^ l = ‖normalizedTrace (D ^ l)‖)
    (N : ℕ) (m : Fin N → Matrix n n 𝕜) (P : Fin N → Prop) [DecidablePred P]
    (hP : ∀ i, P i → m i = D) :
    ‖normalizedTrace (List.ofFn m).prod‖ ≤
      (∏ i, if P i then 1 else ‖m i‖) * ‖normalizedTrace (D ^ (Finset.univ.filter P).card)‖ := by
  set c := (Finset.univ.filter P).card with hc
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · have h := (word_schatten_bound D N m P hP c le_rfl).1 hc0
    have htr : ‖normalizedTrace (List.ofFn m).prod‖ ≤ ‖(List.ofFn m).prod‖ := by
      have := norm_normalizedTrace_mul_exp_hermitian_le (0 : Matrix n n 𝕜)
        (List.ofFn m).prod Matrix.isHermitian_zero
      simpa [NormedSpace.exp_zero] using this
    rw [hc0, pow_zero, normalizedTrace_one, norm_one, mul_one]
    exact htr.trans h
  · have h := (word_schatten_bound D N m P hP c le_rfl).2 hcpos
    rw [div_self (by exact_mod_cast hcpos.ne')] at h
    rw [← hD c hcpos]
    exact (norm_normalizedTrace_le_schatten_one _).trans h

/-- `U diag(ν) U*` for the eigenvector unitary `U` of a Hermitian matrix. -/
noncomputable def conjDiag (H : Matrix n n 𝕜) (hH : H.IsHermitian) (ν : n → ℝ) :
    Matrix n n 𝕜 :=
  (↑hH.eigenvectorUnitary : Matrix n n 𝕜) * Matrix.diagonal (fun j => (ν j : 𝕜)) *
    star (↑hH.eigenvectorUnitary : Matrix n n 𝕜)

theorem conjDiag_pow (H : Matrix n n 𝕜) (hH : H.IsHermitian) (ν : n → ℝ) (l : ℕ) :
    conjDiag H hH ν ^ l = conjDiag H hH (fun j => ν j ^ l) := by
  unfold conjDiag
  rw [← Unitary.conjStarAlgAut_apply (S := 𝕜), ← map_pow, Matrix.diagonal_pow,
    Unitary.conjStarAlgAut_apply]
  congr 3
  ext j
  simp

theorem trace_conjDiag (H : Matrix n n 𝕜) (hH : H.IsHermitian) (ν : n → ℝ) :
    (conjDiag H hH ν).trace = ∑ j, (ν j : 𝕜) := by
  unfold conjDiag
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul,
    Matrix.trace_diagonal]

theorem normalizedTrace_conjDiag_pow (H : Matrix n n 𝕜) (hH : H.IsHermitian) (ν : n → ℝ)
    (l : ℕ) :
    normalizedTrace (conjDiag H hH ν ^ l) =
      (((∑ j, ν j ^ l) / Fintype.card n : ℝ) : 𝕜) := by
  rw [conjDiag_pow, normalizedTrace, trace_conjDiag]
  push_cast
  ring

section
open scoped ComplexOrder

theorem posSemidef_conjDiag (H : Matrix n n 𝕜) (hH : H.IsHermitian) (ν : n → ℝ)
    (hν : ∀ j, 0 ≤ ν j) : (conjDiag H hH ν).PosSemidef := by
  unfold conjDiag
  have hU : IsUnit (↑hH.eigenvectorUnitary : Matrix n n 𝕜) := Unitary.isUnit_coe
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU, Matrix.posSemidef_diagonal_iff]
  exact fun i => RCLike.ofReal_nonneg.mpr (hν i)

end

private theorem sum_sv_conjDiag (H : Matrix n n 𝕜) (hH : H.IsHermitian) (ν : n → ℝ)
    (hν : ∀ j, 0 ≤ ν j) (f : ℝ → ℝ) :
    ∑ i, f (SVDAux.sv (Matrix.toEuclideanLin (conjDiag H hH ν)) i) = ∑ j, f (ν j) := by
  have hT : (Matrix.toEuclideanLin (conjDiag H hH ν)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_conjDiag H hH ν hν)
  simp only [SVDAux.sv, singularValues_of_positive _ hT]
  exact sum_eigenvalues_eq_of_basis _ hT.isSymmetric hH.eigenvectorBasis ν
    (fun j => toEuclideanLin_conj_diagonal_apply H hH ν j) f

theorem normalizedSchattenNorm_conjDiag_pow [Nonempty n] (H : Matrix n n 𝕜)
    (hH : H.IsHermitian) (ν : n → ℝ) (hν : ∀ j, 0 ≤ ν j) (l : ℕ) (hl : 1 ≤ l) :
    normalizedSchattenNorm l (conjDiag H hH ν) ^ l = (∑ j, ν j ^ l) / Fintype.card n := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  rw [normalizedSchattenNorm_eq_sum hlR, sum_sv_conjDiag H hH ν hν (fun x => x ^ (l : ℝ))]
  simp only [Real.rpow_natCast]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (Finset.sum_nonneg fun j _ =>
    pow_nonneg (hν j) l) (Nat.cast_nonneg _)), one_div_mul_cancel hlR.ne', Real.rpow_one]

theorem conjDiag_add_const (H : Matrix n n 𝕜) (hH : H.IsHermitian) (c : ℝ) :
    conjDiag H hH (fun j => hH.eigenvalues j + c) = H + ((c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) := by
  conv_rhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  unfold conjDiag
  have hdiag : Matrix.diagonal (fun j => ((hH.eigenvalues j + c : ℝ) : 𝕜)) =
      Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) + ((c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, Function.comp_apply, RCLike.ofReal_add]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hUU : (↑hH.eigenvectorUnitary : Matrix n n 𝕜) *
      star (↑hH.eigenvectorUnitary : Matrix n n 𝕜) = 1 := by
    simp
  rw [hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hUU]

theorem abs_eigenvalues_le (H : Matrix n n 𝕜) (hH : H.IsHermitian) (j : n) :
    |hH.eigenvalues j| ≤ ‖H‖ := by
  have hH0 : H = conjDiag H hH (fun j => hH.eigenvalues j + 0) := by
    rw [conjDiag_add_const]; simp
  have happ := toEuclideanLin_conj_diagonal_apply H hH
    (fun j => hH.eigenvalues j + 0) j
  unfold conjDiag at hH0
  rw [← hH0] at happ
  have hle := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin H)).le_opNorm
    (hH.eigenvectorBasis j)
  rw [norm_toContinuousLinearMap_toEuclideanLin, LinearMap.coe_toContinuousLinearMap', happ,
    norm_smul, OrthonormalBasis.norm_eq_one, mul_one, mul_one, RCLike.norm_ofReal,
    add_zero] at hle
  exact hle

theorem prod_weight_finSumEquivOfFinset {k l : ℕ} {s : Finset (Fin (k + l))}
    (hs : s.card = l) (hl : sᶜ.card = k) (D : Matrix n n 𝕜) (w : Fin k → Matrix n n 𝕜) :
    (∏ i : Fin (k + l), if i ∈ s then (1 : ℝ) else
        ‖Sum.elim (fun _ : Fin l => D) w ((finSumEquivOfFinset hs hl).symm i)‖) =
      ∏ j, ‖w j‖ := by
  rw [← (finSumEquivOfFinset hs hl).prod_comp, Fintype.prod_sum_type]
  have h1 : ∀ a : Fin l, finSumEquivOfFinset hs hl (Sum.inl a) ∈ s := fun a => by
    rw [finSumEquivOfFinset_inl]; exact Finset.orderEmbOfFin_mem s hs a
  have h2 : ∀ b : Fin k, finSumEquivOfFinset hs hl (Sum.inr b) ∉ s := fun b => by
    rw [finSumEquivOfFinset_inr]
    exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem sᶜ hl b)
  simp only [h1, h2, if_true, if_false, Finset.prod_const_one, one_mul, Equiv.symm_apply_apply,
    Sum.elim_inr]

omit [RCLike 𝕜] [Fintype n] [DecidableEq n] in
theorem elim_finSumEquivOfFinset_of_mem {k l : ℕ} {s : Finset (Fin (k + l))}
    (hs : s.card = l) (hl : sᶜ.card = k) (D : Matrix n n 𝕜) (w : Fin k → Matrix n n 𝕜)
    (i : Fin (k + l)) (hi : i ∈ s) :
    Sum.elim (fun _ : Fin l => D) w ((finSumEquivOfFinset hs hl).symm i) = D := by
  rcases h : (finSumEquivOfFinset hs hl).symm i with a | b
  · rfl
  · exfalso
    have : i = finSumEquivOfFinset hs hl (Sum.inr b) := by
      rw [← h, Equiv.apply_symm_apply]
    rw [this, finSumEquivOfFinset_inr] at hi
    exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem sᶜ hl b) hi

/-- Bound on the Taylor coefficients of `a • τ ∘ exp` at a point `D` whose Schatten norms are
computed by traces of powers. -/
theorem changeOrigin_coef_bound [Nonempty n] (D : Matrix n n 𝕜)
    (hD : ∀ l : ℕ, 1 ≤ l → normalizedSchattenNorm l D ^ l = ‖normalizedTrace (D ^ l)‖)
    (a : 𝕜) (S : ℝ) (hS : HasSum (fun l : ℕ => ‖normalizedTrace (D ^ l)‖ / (l ! : ℝ)) S)
    (k : ℕ) (w : Fin k → Matrix n n 𝕜) :
    ‖(((a • normalizedTraceCLM : Matrix n n 𝕜 →L[𝕜] 𝕜).compFormalMultilinearSeries
        (NormedSpace.expSeries 𝕜 (Matrix n n 𝕜))).changeOrigin D k) w‖ ≤
      ‖a‖ * (∏ i, ‖w i‖) / (k ! : ℝ) * S := by
  set L : Matrix n n 𝕜 →L[𝕜] 𝕜 := a • normalizedTraceCLM with hL
  set P := L.compFormalMultilinearSeries (NormedSpace.expSeries 𝕜 (Matrix n n 𝕜)) with hP
  have hfps : HasFPowerSeriesOnBall (L ∘ NormedSpace.exp) P 0 ⊤ :=
    L.comp_hasFPowerSeriesOnBall NormedSpace.exp_hasFPowerSeriesOnBall
  have hrad : P.radius = ⊤ := top_le_iff.mp hfps.r_le
  have hsum := (P.hasFPowerSeriesOnBall_changeOrigin k (by simp [hrad])).hasSum
    (y := D) (by rw [hrad]; simp)
  rw [zero_add] at hsum
  have hsumw := (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin k => Matrix n n 𝕜) 𝕜 w).hasSum hsum
  simp only [ContinuousMultilinearMap.apply_apply] at hsumw
  refine hsumw.norm_le_of_bounded (hS.mul_left (‖a‖ * (∏ i, ‖w i‖) / (k ! : ℝ))) fun l => ?_
  -- bound on each term
  rw [FormalMultilinearSeries.changeOriginSeries, sum_apply,
    sum_apply]
  have hterm : ∀ s : {s : Finset (Fin (k + l)) // s.card = l},
      ‖P.changeOriginSeriesTerm k l s s.2 (fun _ => D) w‖ ≤
        ‖a‖ * ((k + l)! : ℝ)⁻¹ * ((∏ i, ‖w i‖) * ‖normalizedTrace (D ^ l)‖) := by
    intro s
    have hl : (sᶜ : Finset (Fin (k + l))).card = k := by
      rw [Finset.card_compl, Fintype.card_fin, s.2, Nat.add_sub_cancel]
    rw [FormalMultilinearSeries.changeOriginSeriesTerm, ContinuousMultilinearMap.curryFinFinset_apply]
    rw [hP, ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    simp only [NormedSpace.expSeries, smul_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply, map_smul, hL,
      normalizedTraceCLM_apply, smul_eq_mul, smul_eq_mul,
      norm_mul, norm_mul, norm_inv, RCLike.norm_natCast, mul_assoc]
    rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)
    have hw := word_trace_bound D hD (k + l)
      (fun i => Sum.elim (fun _ : Fin l => D) w ((finSumEquivOfFinset s.2 hl).symm i))
      (fun i => i ∈ (s : Finset (Fin (k + l))))
      (fun i hi => elim_finSumEquivOfFinset_of_mem s.2 hl D w i hi)
    rw [prod_weight_finSumEquivOfFinset s.2 hl D w] at hw
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter, s.2] using hw
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun s _ => hterm s).trans ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin, nsmul_eq_mul]
  have hfact : ((k + l).choose l : ℝ) * ((k + l)! : ℝ)⁻¹ = ((k ! : ℝ) * (l ! : ℝ))⁻¹ := by
    have h := Nat.choose_mul_factorial_mul_factorial (show l ≤ k + l by omega)
    rw [Nat.add_sub_cancel] at h
    have h' : ((k + l).choose l : ℝ) * (l ! : ℝ) * (k ! : ℝ) = ((k + l)! : ℝ) := by
      exact_mod_cast h
    have hk : (k ! : ℝ) ≠ 0 := by positivity
    have hl' : (l ! : ℝ) ≠ 0 := by positivity
    field_simp
    linarith
  calc ((k + l).choose l : ℝ) *
        (‖a‖ * ((k + l)! : ℝ)⁻¹ * ((∏ i, ‖w i‖) * ‖normalizedTrace (D ^ l)‖))
      = ‖a‖ * (((k + l).choose l : ℝ) * ((k + l)! : ℝ)⁻¹) *
          ((∏ i, ‖w i‖) * ‖normalizedTrace (D ^ l)‖) := by ring
    _ = ‖a‖ * (∏ i, ‖w i‖) / (k ! : ℝ) * (‖normalizedTrace (D ^ l)‖ / (l ! : ℝ)) := by
        rw [hfact]
        field_simp
    _ ≤ _ := le_rfl

theorem exp_add_smul_one (X : Matrix n n 𝕜) (c : ℝ) :
    NormedSpace.exp (X + ((c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) =
      ((Real.exp c : ℝ) : 𝕜) • NormedSpace.exp X := by
  have hcomm : Commute X (((c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) :=
    (Commute.one_right X).smul_right _
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  have h1 : ((c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) = Matrix.diagonal (fun _ => ((c : ℝ) : 𝕜)) :=
    Matrix.smul_one_eq_diagonal _
  have hexp : NormedSpace.exp (fun _ : n => ((c : ℝ) : 𝕜)) = fun _ => ((Real.exp c : ℝ) : 𝕜) := by
    funext i
    rw [Pi.coe_exp]
    simpa only [RCLike.ofReal_alg, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.map_exp (algebraMap ℝ 𝕜) (continuous_algebraMap ℝ 𝕜) c).symm
  have h2 : Matrix.diagonal (fun _ : n => ((Real.exp c : ℝ) : 𝕜)) =
      ((Real.exp c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) :=
    (Matrix.smul_one_eq_diagonal _).symm
  rw [h1, Matrix.exp_diagonal, hexp, h2, Matrix.mul_smul, Matrix.mul_one]

end WordBounds

end

end SYK.MatrixAnalysis
