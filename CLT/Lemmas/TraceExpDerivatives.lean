import SYK.CLT.Lemmas.MatrixTraceExponential

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory

/-!
# Directional derivatives of the normalized trace exponential

Main entry points: `MatrixAnalysis.DerivAux.contDiff_tE`,
`MatrixAnalysis.Matrix.traceExp`,
`MatrixAnalysis.Matrix.iterDirectionalFDeriv_traceExp_bound`.
-/

namespace MatrixAnalysis

/-! ## Iterated directional derivatives of `tr(exp A)` -/

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

namespace DerivAux

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

noncomputable local instance : NormedSpace ℝ (Matrix n n 𝕜) :=
  NormedSpace.restrictScalars ℝ 𝕜 (Matrix n n 𝕜)

local instance : SMul ℝ (Matrix n n 𝕜) :=
  (NormedSpace.toModule (𝕜 := ℝ) (E := Matrix n n 𝕜)).toDistribMulAction.toMulAction.toSMul

local instance : SMul 𝕜 (Matrix n n 𝕜) :=
  (NormedSpace.toModule (𝕜 := 𝕜) (E := Matrix n n 𝕜)).toDistribMulAction.toMulAction.toSMul

local instance : IsScalarTower ℝ 𝕜 (Matrix n n 𝕜) :=
  ⟨by
    intro a b A
    ext i j
    change ((a • b : 𝕜) * A i j) = (a : 𝕜) * (b * A i j)
    rw [RCLike.real_smul_eq_coe_mul]
    ring⟩

/-- Normalized trace of the matrix exponential. -/
noncomputable def tE (A : Matrix n n 𝕜) : 𝕜 :=
  Matrix.normalizedTrace (NormedSpace.exp A)

/-- Smoothness of the normalized trace exponential as a real map. -/
theorem contDiff_tE : ContDiff ℝ ⊤ (tE : Matrix n n 𝕜 → 𝕜) := by
  have hexp : ContDiff ℝ ⊤ (NormedSpace.exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (NormedSpace.exp_analytic (𝕂 := 𝕜) x).restrictScalars.contDiffAt
  have htrace : ContDiff ℝ ⊤ (Matrix.trace : Matrix n n 𝕜 → 𝕜) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    let L : Matrix n n 𝕜 →L[𝕜] 𝕜 := (Matrix.traceLinearMap n 𝕜 𝕜).toContinuousLinearMap
    exact (L.analyticAt x).restrictScalars.contDiffAt
  have hNS : (NormedAlgebra.toNormedSpace 𝕜 : NormedSpace ℝ 𝕜) =
      RCLike.toInnerProductSpaceReal.toNormedSpace := by
    ext a b
    rfl
  have hsmooth : @ContDiff ℝ _ (Matrix n n 𝕜) _ _ 𝕜 _
      (NormedAlgebra.toNormedSpace 𝕜) ⊤ tE := by
    change @ContDiff ℝ _ (Matrix n n 𝕜) _ _ 𝕜 _
      (NormedAlgebra.toNormedSpace 𝕜) ⊤ (fun A : Matrix n n 𝕜 =>
        (Fintype.card n : 𝕜)⁻¹ * Matrix.trace (NormedSpace.exp A))
    exact contDiff_const.mul (htrace.comp hexp)
  exact hNS ▸ hsmooth

open scoped Nat in
/-- Sharp bound on the iterated derivatives of the normalized trace exponential at a Hermitian
point: each direction contributes its operator norm. -/
theorem iteratedFDeriv_tE_bound_hermitian [Nonempty n] (A : Matrix n n 𝕜) (hA : A.IsHermitian)
    (k : ℕ) (v : Fin k → Matrix n n 𝕜) :
    ‖iteratedFDeriv ℝ k tE A v‖ ≤ (∏ i, ‖v i‖) * ‖tE A‖ := by
  set c0 := ‖A‖ with hc0
  set ν : n → ℝ := fun j => hA.eigenvalues j + c0 with hν_def
  have hν : ∀ j, 0 ≤ ν j := fun j => by
    have := Matrix.abs_eigenvalues_le A hA j
    simp only [ν]
    linarith [neg_abs_le (hA.eigenvalues j)]
  set D := Matrix.conjDiag A hA ν with hD_def
  have hDeq : D = A + ((c0 : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) := Matrix.conjDiag_add_const A hA c0
  have hDtr : ∀ l : ℕ, ‖Matrix.normalizedTrace (D ^ l)‖ =
      (∑ j, ν j ^ l) / Fintype.card n := fun l => by
    rw [Matrix.normalizedTrace_conjDiag_pow, RCLike.norm_ofReal, abs_of_nonneg
      (div_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (hν j) l) (Nat.cast_nonneg _))]
  have hDs : ∀ l : ℕ, 1 ≤ l →
      Matrix.normalizedSchattenNorm l D ^ l = ‖Matrix.normalizedTrace (D ^ l)‖ := fun l hl => by
    rw [hDtr, Matrix.normalizedSchattenNorm_conjDiag_pow A hA ν hν l hl]
  have htE : ‖tE A‖ = (∑ j, Real.exp (hA.eigenvalues j)) / Fintype.card n := by
    have h := ExpAux.trace_exp A hA 1
    rw [one_smul] at h
    simp only [one_mul] at h
    rw [tE, Matrix.normalizedTrace, h, ← RCLike.ofReal_sum, ← RCLike.ofReal_natCast,
      ← RCLike.ofReal_inv, ← RCLike.ofReal_mul, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      inv_mul_eq_div]
  set S := (∑ j, Real.exp (ν j)) / Fintype.card n with hS_def
  have hS : HasSum (fun l : ℕ => ‖Matrix.normalizedTrace (D ^ l)‖ / (l ! : ℝ)) S := by
    have h1 : ∀ j, HasSum (fun l : ℕ => ν j ^ l / (l ! : ℝ)) (Real.exp (ν j)) := fun j => by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (ν j)
    have h2 := (hasSum_sum (s := Finset.univ) fun j _ => h1 j).div_const (Fintype.card n : ℝ)
    have hterms : (fun l : ℕ => ‖Matrix.normalizedTrace (D ^ l)‖ / (l ! : ℝ)) =
        fun l => (∑ j, ν j ^ l / (l ! : ℝ)) / (Fintype.card n : ℝ) := by
      funext l
      rw [hDtr, Finset.sum_div, Finset.sum_div, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hterms, hS_def]
    exact h2
  have hSeq : Real.exp (-c0) * S = ‖tE A‖ := by
    rw [htE, hS_def, mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ν]
    rw [← Real.exp_add]
    congr 1
    ring
  set a : 𝕜 := ((Real.exp (-c0) : ℝ) : 𝕜) with ha
  set L : Matrix n n 𝕜 →L[𝕜] 𝕜 := a • Matrix.normalizedTraceCLM with hL
  set P := L.compFormalMultilinearSeries (NormedSpace.expSeries 𝕜 (Matrix n n 𝕜)) with hP
  have hfps : HasFPowerSeriesOnBall (L ∘ NormedSpace.exp) P 0 ⊤ :=
    L.comp_hasFPowerSeriesOnBall NormedSpace.exp_hasFPowerSeriesOnBall
  have hfpsD : HasFPowerSeriesOnBall (L ∘ NormedSpace.exp) (P.changeOrigin D) D ⊤ := by
    have := hfps.changeOrigin (y := D) (by simp)
    simpa using this
  have hfpsR := hfpsD.restrictScalars (𝕜 := ℝ)
  have hshift : (tE : Matrix n n 𝕜 → 𝕜) =
      fun X => (L ∘ NormedSpace.exp) (X + ((c0 : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) := by
    funext X
    simp only [Function.comp_apply, Matrix.exp_add_smul_one, hL, ha,
      ContinuousLinearMap.smul_apply, Matrix.normalizedTraceCLM_apply,
      Matrix.normalizedTrace_smul, smul_eq_mul, tE]
    rw [← mul_assoc, ← RCLike.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      RCLike.ofReal_one, one_mul]
  have hiter : iteratedFDeriv ℝ k tE A = iteratedFDeriv ℝ k (L ∘ NormedSpace.exp) D := by
    rw [hshift, iteratedFDeriv_comp_add_right']
    simp only
    rw [← hDeq]
  rw [hiter, hfpsR.iteratedFDeriv_eq_sum_of_completeSpace]
  have hcoef : ∀ σ : Equiv.Perm (Fin k),
      ‖(P.changeOrigin D).restrictScalars ℝ k (fun i => v (σ i))‖ ≤
        (∏ i, ‖v i‖) / (k ! : ℝ) * ‖tE A‖ := by
    intro σ
    have h := Matrix.changeOrigin_coef_bound D hDs a S hS k (fun i => v (σ i))
    rw [Equiv.prod_comp σ (fun i => ‖v i‖)] at h
    calc ‖(P.changeOrigin D).restrictScalars ℝ k (fun i => v (σ i))‖
        = ‖(P.changeOrigin D k) (fun i => v (σ i))‖ := rfl
      _ ≤ ‖a‖ * (∏ i, ‖v i‖) / (k ! : ℝ) * S := h
      _ = (∏ i, ‖v i‖) / (k ! : ℝ) * ‖tE A‖ := by
          rw [← hSeq, ha, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]
          ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun σ _ => hcoef σ).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end DerivAux

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

noncomputable local instance : NormedSpace ℝ (Matrix n n 𝕜) :=
  NormedSpace.restrictScalars ℝ 𝕜 (Matrix n n 𝕜)

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
