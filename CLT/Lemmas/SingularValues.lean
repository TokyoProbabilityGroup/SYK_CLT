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
# Singular values and Schatten bounds

This file develops singular-value estimates from the spectral theorem: min-max
bounds, von Neumann's trace inequality, and Schatten-Hölder. Main entry points:
`SingularAux.singularValues_of_positive`, `SingularAux.schatten_holder`,
`SingularAux.sum_sv_comp_le`.
-/

section InfrastructureA

open scoped InnerProductSpace

namespace SingularAux

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
/-- Rayleigh quotient expansion in an orthonormal eigenbasis. -/
theorem re_inner_eq_sum {ι : Type*} [Fintype ι] (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (e : OrthonormalBasis ι 𝕜 E) (ν : ι → ℝ) (he : ∀ j, T (e j) = (ν j : 𝕜) • e j) (x : E) :
    RCLike.re ⟪x, T x⟫_𝕜 = ∑ j, ν j * ‖⟪e j, x⟫_𝕜‖ ^ 2 := by
  have h1 : ⟪x, T x⟫_𝕜 = ∑ j, ⟪x, e j⟫_𝕜 * ⟪e j, T x⟫_𝕜 := (e.sum_inner_mul_inner x (T x)).symm
  have h2 : ∀ j, ⟪e j, T x⟫_𝕜 = (ν j : 𝕜) * ⟪e j, x⟫_𝕜 := by
    intro j
    rw [← hT, he, inner_smul_left, RCLike.conj_ofReal]
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2, ← inner_conj_symm x (e j), mul_left_comm, RCLike.conj_mul]
  rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

omit [FiniteDimensional 𝕜 E] in
theorem re_inner_le_of_orth_head (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {n : ℕ}
    (e : OrthonormalBasis (Fin n) 𝕜 E) (ν : Fin n → ℝ) (hν : Antitone ν)
    (he : ∀ j, T (e j) = (ν j : 𝕜) • e j) (i : Fin n) (x : E)
    (hx : ∀ j, j < i → ⟪e j, x⟫_𝕜 = 0) :
    RCLike.re ⟪x, T x⟫_𝕜 ≤ ν i * ‖x‖ ^ 2 := by
  rw [re_inner_eq_sum T hT e ν he x, ← e.sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge j i with h | h
  · simp [hx j h]
  · exact mul_le_mul_of_nonneg_right (hν h) (by positivity)

omit [FiniteDimensional 𝕜 E] in
theorem le_re_inner_of_orth_tail (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {n : ℕ}
    (e : OrthonormalBasis (Fin n) 𝕜 E) (ν : Fin n → ℝ) (hν : Antitone ν)
    (he : ∀ j, T (e j) = (ν j : 𝕜) • e j) (i : Fin n) (x : E)
    (hx : ∀ j, i < j → ⟪e j, x⟫_𝕜 = 0) :
    ν i * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_𝕜 := by
  rw [re_inner_eq_sum T hT e ν he x, ← e.sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge i j with h | h
  · simp [hx j h]
  · exact mul_le_mul_of_nonneg_right (hν h) (by positivity)

/-- A vector orthogonal to fewer than `dim E` given vectors exists. -/
theorem exists_ne_zero_orth {ι : Type*} [Fintype ι] (v : ι → E)
    (h : Fintype.card ι < Module.finrank 𝕜 E) :
    ∃ x : E, x ≠ 0 ∧ ∀ k, ⟪v k, x⟫_𝕜 = 0 := by
  let f : E →ₗ[𝕜] (ι → 𝕜) := LinearMap.pi fun k => innerₛₗ 𝕜 (v k)
  have hker : LinearMap.ker f ≠ ⊥ :=
    f.ker_ne_bot_of_finrank_lt (by rwa [Module.finrank_fintype_fun_eq_card])
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, hx0, fun k => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hx) k
  simpa [f] using this

theorem eigenvalues_eigenbasis_eq (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (j : Fin n) :
    T (hT.eigenvectorBasis hn j) = ((hT.eigenvalues hn j : ℝ) : 𝕜) • hT.eigenvectorBasis hn j :=
  hT.apply_eigenvectorBasis hn j

/-- Min-max, upper bound: if the Rayleigh quotient is at most `c` on the orthogonal complement of
at most `i` vectors, then the `i`-th eigenvalue is at most `c`. -/
theorem eigenvalues_le_of_forall (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Fintype.card ι ≤ i) (c : ℝ)
    (h : ∀ x, (∀ k, ⟪u k, x⟫_𝕜 = 0) → RCLike.re ⟪x, T x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    hT.eigenvalues hn i ≤ c := by
  let b := hT.eigenvectorBasis hn
  let w : ι ⊕ Fin (n - 1 - i) → E :=
    Sum.elim u fun j => b ⟨i + 1 + j, by omega⟩
  have hcard : Fintype.card (ι ⊕ Fin (n - 1 - i)) < Module.finrank 𝕜 E := by
    rw [Fintype.card_sum, Fintype.card_fin, hn]
    have := i.2
    omega
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_orth w hcard
  have h1 := h x (fun k => hx (Sum.inl k))
  have h2 := le_re_inner_of_orth_tail T hT b _ (hT.eigenvalues_antitone hn)
    (hT.apply_eigenvectorBasis hn) i x (fun j hj => by
      have := hx (Sum.inr ⟨j - i - 1, by omega⟩)
      simp only [w, Sum.elim_inr] at this
      convert this using 3
      ext
      simp only
      omega)
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h2.trans h1) hpos

/-- Min-max, lower bound. -/
theorem le_eigenvalues_of_forall (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Fintype.card ι + i + 1 ≤ n) (c : ℝ)
    (h : ∀ x, (∀ k, ⟪u k, x⟫_𝕜 = 0) → c * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_𝕜) :
    c ≤ hT.eigenvalues hn i := by
  let b := hT.eigenvectorBasis hn
  let w : ι ⊕ Fin i → E :=
    Sum.elim u fun j => b ⟨j, by omega⟩
  have hcard : Fintype.card (ι ⊕ Fin i) < Module.finrank 𝕜 E := by
    rw [Fintype.card_sum, Fintype.card_fin, hn]
    omega
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_orth w hcard
  have h1 := h x (fun k => hx (Sum.inl k))
  have h2 := re_inner_le_of_orth_head T hT b _ (hT.eigenvalues_antitone hn)
    (hT.apply_eigenvectorBasis hn) i x (fun j hj => by
      have := hx (Sum.inr ⟨j, hj⟩)
      simpa only [w, Sum.elim_inr] using this)
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h1.trans h2) hpos

/-- Eigenvalues are determined by any orthonormal eigenbasis with antitone eigenvalues. -/
theorem eigenvalues_eq_of_basis (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) (ν : Fin n → ℝ)
    (hν : Antitone ν) (he : ∀ j, T (e j) = (ν j : 𝕜) • e j) :
    hT.eigenvalues hn = ν := by
  funext i
  apply le_antisymm
  · refine eigenvalues_le_of_forall T hT hn i (fun j : Fin i => e ⟨j, by omega⟩)
      (by simp) _ fun x hx => ?_
    exact re_inner_le_of_orth_head T hT e ν hν he i x (fun j hj => hx ⟨j, hj⟩)
  · refine le_eigenvalues_of_forall T hT hn i
      (fun j : Fin (n - 1 - i) => e ⟨i + 1 + j, by omega⟩) (by simp; omega) _ fun x hx => ?_
    refine le_re_inner_of_orth_tail T hT e ν hν he i x (fun j hj => ?_)
    have := hx ⟨j - i - 1, by omega⟩
    convert this using 3
    ext
    simp only
    omega

end SingularAux

end InfrastructureA

section InfrastructureB

open scoped InnerProductSpace

namespace SingularAux

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

theorem re_inner_adjoint_comp_self (S : E →ₗ[𝕜] E) (x : E) :
    RCLike.re ⟪x, (S.adjoint ∘ₗ S) x⟫_𝕜 = ‖S x‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

theorem eig_nonneg (T : E →ₗ[𝕜] E) {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    0 ≤ T.isSymmetric_adjoint_comp_self.eigenvalues hn i :=
  T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i

theorem sv_sq (T : E →ₗ[𝕜] E) {i : ℕ} (hi : i < Module.finrank 𝕜 E) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, hi⟩ := by
  rw [T.singularValues_of_lt rfl hi, Real.sq_sqrt (eig_nonneg T rfl _)]

theorem sv_antitone (T : E →ₗ[𝕜] E) : Antitone (fun i => T.singularValues i) := by
  intro i j hij
  simp only
  by_cases hj : j < Module.finrank 𝕜 E
  · rw [T.singularValues_of_lt rfl hj, T.singularValues_of_lt rfl (by omega)]
    exact Real.sqrt_le_sqrt (T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl
      (show (⟨i, by omega⟩ : Fin _) ≤ ⟨j, hj⟩ from hij))
  · rw [T.singularValues_of_finrank_le (by omega)]
    exact T.singularValues_nonneg i

/-- The `i`-th singular value is bounded by any constant controlling the Rayleigh quotient of
`T†T` off at most `i` vectors. -/
theorem sv_le_of_forall (T : E →ₗ[𝕜] E) (i : ℕ) {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Fintype.card ι ≤ i) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x, (∀ k, ⟪u k, x⟫_𝕜 = 0) → ‖T x‖ ^ 2 ≤ c ^ 2 * ‖x‖ ^ 2) :
    T.singularValues i ≤ c := by
  by_cases hi : i < Module.finrank 𝕜 E
  · rw [T.singularValues_of_lt rfl hi]
    have := eigenvalues_le_of_forall _ T.isSymmetric_adjoint_comp_self rfl ⟨i, hi⟩ u hu (c ^ 2)
      (fun x hx => by rw [re_inner_adjoint_comp_self]; exact h x hx)
    calc √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, hi⟩) ≤ √(c ^ 2) :=
          Real.sqrt_le_sqrt this
      _ = c := Real.sqrt_sq hc
  · rw [T.singularValues_of_finrank_le (by omega)]
    exact hc

/-- For `x` orthogonal to the first `i` eigenvectors of `T†T`, `‖T x‖ ≤ s_i(T) ‖x‖`. -/
theorem norm_apply_sq_le_of_orth (T : E →ₗ[𝕜] E) {i : ℕ} (hi : i < Module.finrank 𝕜 E) (x : E)
    (hx : ∀ j : Fin (Module.finrank 𝕜 E), (j : ℕ) < i →
      ⟪T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j, x⟫_𝕜 = 0) :
    ‖T x‖ ^ 2 ≤ T.singularValues i ^ 2 * ‖x‖ ^ 2 := by
  rw [← re_inner_adjoint_comp_self, sv_sq T hi]
  exact re_inner_le_of_orth_head _ T.isSymmetric_adjoint_comp_self _ _
    (T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl)
    (T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl) ⟨i, hi⟩ x hx

theorem sv_comp_left_le (W T : E →ₗ[𝕜] E) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖W v‖ ≤ C * ‖v‖) (i : ℕ) :
    (W ∘ₗ T).singularValues i ≤ C * T.singularValues i := by
  by_cases hi : i < Module.finrank 𝕜 E
  · refine sv_le_of_forall (W ∘ₗ T) i
      (fun j : Fin i => T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨j, hi.trans' j.2⟩)
      (by simp) _ (mul_nonneg hC0 (T.singularValues_nonneg i)) fun x hx => ?_
    have h1 := norm_apply_sq_le_of_orth T hi x (fun j hj => hx ⟨j, hj⟩)
    have h2 : ‖W (T x)‖ ^ 2 ≤ C ^ 2 * ‖T x‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
    calc ‖(W ∘ₗ T) x‖ ^ 2 = ‖W (T x)‖ ^ 2 := rfl
      _ ≤ C ^ 2 * ‖T x‖ ^ 2 := h2
      _ ≤ C ^ 2 * (T.singularValues i ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (C * T.singularValues i) ^ 2 * ‖x‖ ^ 2 := by ring
  · rw [(W ∘ₗ T).singularValues_of_finrank_le (by omega),
      T.singularValues_of_finrank_le (by omega), mul_zero]

theorem sv_comp_right_le (T S : E →ₗ[𝕜] E) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖S v‖ ≤ C * ‖v‖) (i : ℕ) :
    (T ∘ₗ S).singularValues i ≤ T.singularValues i * C := by
  by_cases hi : i < Module.finrank 𝕜 E
  · refine sv_le_of_forall (T ∘ₗ S) i
      (fun j : Fin i => S.adjoint
        (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨j, hi.trans' j.2⟩))
      (by simp) _ (mul_nonneg (T.singularValues_nonneg i) hC0) fun x hx => ?_
    have h1 := norm_apply_sq_le_of_orth T hi (S x) (fun j hj => by
      rw [← LinearMap.adjoint_inner_left]
      exact hx ⟨j, hj⟩)
    have h2 : ‖S x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
    calc ‖(T ∘ₗ S) x‖ ^ 2 = ‖T (S x)‖ ^ 2 := rfl
      _ ≤ T.singularValues i ^ 2 * ‖S x‖ ^ 2 := h1
      _ ≤ T.singularValues i ^ 2 * (C ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (T.singularValues i * C) ^ 2 * ‖x‖ ^ 2 := by ring
  · rw [(T ∘ₗ S).singularValues_of_finrank_le (by omega),
      T.singularValues_of_finrank_le (by omega), zero_mul]

theorem sv_eq_zero_of_orth (T : E →ₗ[𝕜] E) (i : ℕ) {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Fintype.card ι ≤ i) (h : ∀ x, (∀ k, ⟪u k, x⟫_𝕜 = 0) → T x = 0) :
    T.singularValues i = 0 :=
  le_antisymm (sv_le_of_forall T i u hu 0 le_rfl fun x hx => by simp [h x hx])
    (T.singularValues_nonneg i)

/-! ### The normalized image family `w_a = s_a⁻¹ T b_a` -/

/-- `‖T b_a‖ = s_a` for the eigenbasis of `T†T`. -/
theorem norm_apply_eigenvectorBasis (T : E →ₗ[𝕜] E) (a : Fin (Module.finrank 𝕜 E)) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl a)‖ = T.singularValues a := by
  have h := sv_sq T a.2
  have h2 : ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl a)‖ ^ 2 =
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl a := by
    rw [← re_inner_adjoint_comp_self, T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis,
      inner_smul_right, inner_self_eq_norm_sq_to_K, OrthonormalBasis.norm_eq_one]
    simp
  have := h.trans h2.symm
  exact ((pow_left_inj₀ (T.singularValues_nonneg _) (norm_nonneg _) two_ne_zero).mp this).symm

theorem inner_apply_eigenvectorBasis (T : E →ₗ[𝕜] E) (a b : Fin (Module.finrank 𝕜 E)) :
    ⟪T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl a),
      T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl b)⟫_𝕜 =
      if a = b then ((T.singularValues a ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
    T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis, inner_smul_right,
    orthonormal_iff_ite.mp (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).orthonormal a b]
  split_ifs with h
  · subst h
    rw [sv_sq T a.2, mul_one]
  · rw [mul_zero]

/-- The normalized family `w_a = s_a⁻¹ • T b_a`. -/
noncomputable def wv (T : E →ₗ[𝕜] E) (a : Fin (Module.finrank 𝕜 E)) : E :=
  (((T.singularValues a)⁻¹ : ℝ) : 𝕜) • T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl a)

theorem apply_eigenvectorBasis_eq_smul_wv (T : E →ₗ[𝕜] E) (a : Fin (Module.finrank 𝕜 E)) :
    T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl a) =
      ((T.singularValues a : ℝ) : 𝕜) • wv T a := by
  by_cases h : T.singularValues a = 0
  · have h0 : T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl a) = 0 := by
      rw [← norm_eq_zero, norm_apply_eigenvectorBasis, h]
    rw [h0, h]
    simp
  · rw [wv, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ h, RCLike.ofReal_one, one_smul]

theorem inner_wv (T : E →ₗ[𝕜] E) (a b : Fin (Module.finrank 𝕜 E)) :
    ⟪wv T a, wv T b⟫_𝕜 = if a = b ∧ T.singularValues a ≠ 0 then 1 else 0 := by
  rw [wv, wv, inner_smul_left, inner_smul_right, inner_apply_eigenvectorBasis,
    RCLike.conj_ofReal]
  split_ifs with h1 h2 h2
  · subst h1
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
    field_simp [h2.2]
    simp
  · subst h1
    have : T.singularValues a = 0 := by tauto
    simp [this]
  · exact absurd h2.1 h1
  · simp

theorem norm_wv_le (T : E →ₗ[𝕜] E) (a : Fin (Module.finrank 𝕜 E)) : ‖wv T a‖ ≤ 1 := by
  have h := inner_wv T a a
  rw [inner_self_eq_norm_sq_to_K] at h
  split_ifs at h with h1
  · have : ‖wv T a‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg (wv T a)]
  · have : ‖wv T a‖ ^ 2 = 0 := by exact_mod_cast h
    nlinarith [norm_nonneg (wv T a)]

/-- Bessel's inequality for the family `w`. -/
theorem sum_norm_inner_wv_le (T : E →ₗ[𝕜] E) (v : E) :
    ∑ a, ‖⟪wv T a, v⟫_𝕜‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  classical
  let S := {a : Fin (Module.finrank 𝕜 E) // T.singularValues a ≠ 0}
  have hon : Orthonormal 𝕜 (fun a : S => wv T a) := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [inner_wv]
    by_cases hab : a.1 = b.1
    · have hb := b.2
      simp [hb, Subtype.ext hab]
    · have : a ≠ b := fun h => hab (congrArg Subtype.val h)
      simp [hab, this]
  have hB := hon.sum_inner_products_le v (s := Finset.univ)
  have hsplit : ∑ a, ‖⟪wv T a, v⟫_𝕜‖ ^ 2 =
      ∑ a : S, ‖⟪wv T a, v⟫_𝕜‖ ^ 2 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin (Module.finrank 𝕜 E) => T.singularValues a ≠ 0)]
    have h0 : ∑ a : {a : Fin (Module.finrank 𝕜 E) // ¬ T.singularValues a ≠ 0},
        ‖⟪wv T a, v⟫_𝕜‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have ha : T.singularValues a = 0 := not_not.mp a.2
      simp [wv, ha]
    rw [h0, add_zero]
  rw [hsplit]
  exact hB

end SingularAux

end InfrastructureB

section InfrastructureC

open Finset

namespace SingularAux

/-- Abel summation: decreasing nonnegative weights against sequences with nonnegative partial
sums. -/
theorem abel_nonneg (n : ℕ) (s d : ℕ → ℝ) (hs : ∀ i j, i ≤ j → j < n → s j ≤ s i)
    (hs0 : ∀ i < n, 0 ≤ s i) (hd : ∀ k < n, 0 ≤ ∑ i ∈ range (k + 1), d i) :
    0 ≤ ∑ i ∈ range n, s i * d i := by
  have key : ∀ m, m < n →
      s m * ∑ i ∈ range (m + 1), d i ≤ ∑ i ∈ range (m + 1), s i * d i := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have hD := hd m (by omega)
      have hsm : s (m + 1) ≤ s m := hs m (m + 1) (by omega) hm
      rw [sum_range_succ _ (m + 1), sum_range_succ _ (m + 1), mul_add]
      nlinarith
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (mul_nonneg (hs0 m (by omega)) (hd m (by omega))).trans (key m (by omega))

/-- Greedy bound: weights in `[0,1]` of total mass at most `k+1` against a decreasing
nonnegative sequence. -/
theorem greedy_le (n k : ℕ) (hk : k < n) (t c : ℕ → ℝ) (ht : ∀ i j, i ≤ j → j < n → t j ≤ t i)
    (htk : 0 ≤ t k) (hc0 : ∀ b < n, 0 ≤ c b) (hc1 : ∀ b < n, c b ≤ 1)
    (hsum : ∑ b ∈ range n, c b ≤ k + 1) :
    ∑ b ∈ range n, t b * c b ≤ ∑ b ∈ range (k + 1), t b := by
  have h1 : ∑ b ∈ range (k + 1), t b = ∑ b ∈ range n, t b * (if b ≤ k then 1 else 0) := by
    rw [← sum_range_add_sum_Ico (fun b => t b * (if b ≤ k then 1 else 0))
        (show k + 1 ≤ n by omega)]
    rw [sum_eq_zero (s := Ico (k + 1) n) (fun b hb => by
      rw [mem_Ico] at hb; simp [show ¬ b ≤ k by omega]), add_zero]
    refine sum_congr rfl fun b hb => ?_
    rw [mem_range] at hb
    simp [show b ≤ k by omega]
  have h2 : ∑ b ∈ range n, (if b ≤ k then (1 : ℝ) else 0) = k + 1 := by
    rw [← sum_range_add_sum_Ico _ (show k + 1 ≤ n by omega)]
    rw [sum_congr rfl (g := fun _ => (1 : ℝ)) (fun b hb => by
      rw [mem_range] at hb; simp [show b ≤ k by omega])]
    rw [sum_eq_zero (s := Ico (k + 1) n) (fun b hb => by
      rw [mem_Ico] at hb; simp [show ¬ b ≤ k by omega])]
    simp
  rw [h1, ← sub_nonneg, ← sum_sub_distrib]
  have h3 : ∀ b ∈ range n, t k * ((if b ≤ k then 1 else 0) - c b) ≤
      t b * (if b ≤ k then 1 else 0) - t b * c b := by
    intro b hb
    rw [mem_range] at hb
    by_cases hbk : b ≤ k
    · simp only [hbk, if_true, mul_one]
      have := ht b k hbk hk
      have := hc1 b hb
      nlinarith
    · simp only [hbk, if_false, mul_zero, zero_sub]
      have := ht k b (by omega) hb
      have := hc0 b hb
      nlinarith
  refine le_trans ?_ (sum_le_sum h3)
  rw [← mul_sum, sum_sub_distrib, h2]
  exact mul_nonneg htk (by linarith)

/-- Rearrangement for doubly substochastic weights. -/
theorem rearrangement (n : ℕ) (s t : ℕ → ℝ)
    (hs : ∀ i j, i ≤ j → j < n → s j ≤ s i) (ht : ∀ i j, i ≤ j → j < n → t j ≤ t i)
    (hs0 : ∀ i < n, 0 ≤ s i) (ht0 : ∀ i < n, 0 ≤ t i) (P : ℕ → ℕ → ℝ)
    (hP0 : ∀ a < n, ∀ b < n, 0 ≤ P a b)
    (hrow : ∀ a < n, ∑ b ∈ range n, P a b ≤ 1) (hcol : ∀ b < n, ∑ a ∈ range n, P a b ≤ 1) :
    ∑ a ∈ range n, ∑ b ∈ range n, s a * t b * P a b ≤ ∑ i ∈ range n, s i * t i := by
  let r : ℕ → ℝ := fun a => ∑ b ∈ range n, t b * P a b
  have hr : ∀ a, ∑ b ∈ range n, s a * t b * P a b = s a * r a := by
    intro a
    simp only [r, mul_sum, mul_assoc]
  simp_rw [hr]
  rw [← sub_nonneg, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  refine abel_nonneg n s _ hs hs0 fun k hk => ?_
  rw [sum_sub_distrib, sub_nonneg]
  have hswap : ∑ a ∈ range (k + 1), r a = ∑ b ∈ range n, t b * ∑ a ∈ range (k + 1), P a b := by
    simp only [r, mul_sum]
    exact sum_comm
  rw [hswap]
  refine greedy_le n k hk t _ ht (ht0 k hk) (fun b hb => ?_) (fun b hb => ?_) ?_
  · exact sum_nonneg fun a ha => hP0 a (by rw [mem_range] at ha; omega) b hb
  · refine le_trans ?_ (hcol b hb)
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
      fun a ha _ => hP0 a (by rw [mem_range] at ha; exact ha) b hb
  · rw [sum_comm]
    calc ∑ a ∈ range (k + 1), ∑ b ∈ range n, P a b ≤ ∑ a ∈ range (k + 1), (1 : ℝ) :=
          sum_le_sum fun a ha => hrow a (by rw [mem_range] at ha; omega)
      _ = k + 1 := by simp

/-- The tangent line inequality for `x ↦ x ^ r`, `r ≥ 1`. -/
theorem rpow_tangent (r : ℝ) (hr : 1 ≤ r) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    r * x ^ (r - 1) * (y - x) ≤ y ^ r - x ^ r := by
  rcases hx.eq_or_lt with h | h
  · subst h
    rcases hr.eq_or_lt with h1 | h1
    · subst h1; simp
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
      simp [Real.rpow_nonneg hy]
  · have hb := one_add_mul_self_le_rpow_one_add (s := y / x - 1) (by
      have : 0 ≤ y / x := div_nonneg hy h.le
      linarith) hr
    rw [add_sub_cancel] at hb
    have hxr : 0 < x ^ r := Real.rpow_pos_of_pos h r
    have e1 : (y / x) ^ r = y ^ r / x ^ r := Real.div_rpow hy h.le r
    have e2 : x ^ (r - 1) = x ^ r / x := by
      rw [Real.rpow_sub h, Real.rpow_one]
    rw [e1] at hb
    rw [e2]
    have := mul_le_mul_of_nonneg_left hb hxr.le
    rw [mul_div_cancel₀ _ hxr.ne'] at this
    have e3 : x ^ r * (1 + r * (y / x - 1)) = x ^ r + r * (x ^ r / x) * (y - x) := by
      field_simp
    linarith

/-- Weak majorization implies majorization of `r`-th powers (`r ≥ 1`). -/
theorem sum_rpow_le_of_weak_maj (n : ℕ) (x y : ℕ → ℝ) (hx : ∀ i j, i ≤ j → j < n → x j ≤ x i)
    (hx0 : ∀ i < n, 0 ≤ x i) (hy0 : ∀ i < n, 0 ≤ y i)
    (hmaj : ∀ k < n, ∑ i ∈ range (k + 1), x i ≤ ∑ i ∈ range (k + 1), y i) (r : ℝ) (hr : 1 ≤ r) :
    ∑ i ∈ range n, x i ^ r ≤ ∑ i ∈ range n, y i ^ r := by
  rw [← sub_nonneg, ← sum_sub_distrib]
  have h1 := abel_nonneg n (fun i => r * x i ^ (r - 1)) (fun i => y i - x i)
    (fun i j hij hj => by
      have := hx i j hij hj
      have := hx0 j (by omega)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow this ‹_› (by linarith)) (by linarith))
    (fun i hi => mul_nonneg (by linarith) (Real.rpow_nonneg (hx0 i hi) _))
    (fun k hk => by rw [sum_sub_distrib, sub_nonneg]; exact hmaj k hk)
  refine h1.trans (sum_le_sum fun i hi => ?_)
  rw [mem_range] at hi
  exact rpow_tangent r hr (x i) (y i) (hx0 i hi) (hy0 i hi)

/-- Hölder's inequality in the form needed for Schatten norms. -/
theorem sum_mul_rpow_le (s : Finset ℕ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hrecip : 1 / r = 1 / p + 1 / q) :
    (∑ i ∈ s, (a i * b i) ^ r) ^ (1 / r) ≤
      (∑ i ∈ s, a i ^ p) ^ (1 / p) * (∑ i ∈ s, b i ^ q) ^ (1 / q) := by
  have hP : 1 < p / r := by
    rw [lt_div_iff₀ hr, one_mul]
    have : 1 / p < 1 / r := by rw [hrecip]; linarith [one_div_pos.mpr hq]
    exact (one_div_lt_one_div hp hr).mp this
  have hQ : 1 < q / r := by
    rw [lt_div_iff₀ hr, one_mul]
    have : 1 / q < 1 / r := by rw [hrecip]; linarith [one_div_pos.mpr hp]
    exact (one_div_lt_one_div hq hr).mp this
  have hconj : (p / r).HolderConjugate (q / r) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hP, ?_⟩
    rw [inv_div, inv_div]
    field_simp at hrecip ⊢
    linarith
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg s hconj (f := fun i => a i ^ r)
    (g := fun i => b i ^ r) (fun i _ => Real.rpow_nonneg (ha i) _)
    (fun i _ => Real.rpow_nonneg (hb i) _)
  have e1 : ∀ i, (a i ^ r) ^ (p / r) = a i ^ p := fun i => by
    rw [← Real.rpow_mul (ha i), mul_div_cancel₀ _ hr.ne']
  have e2 : ∀ i, (b i ^ r) ^ (q / r) = b i ^ q := fun i => by
    rw [← Real.rpow_mul (hb i), mul_div_cancel₀ _ hr.ne']
  simp only [e1, e2, ← Real.mul_rpow (ha _) (hb _)] at hH
  have hA : 0 ≤ ∑ i ∈ s, a i ^ p := sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _
  have hB : 0 ≤ ∑ i ∈ s, b i ^ q := sum_nonneg fun i _ => Real.rpow_nonneg (hb i) _
  have hS : 0 ≤ ∑ i ∈ s, (a i * b i) ^ r :=
    sum_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg (ha i) (hb i)) _
  calc (∑ i ∈ s, (a i * b i) ^ r) ^ (1 / r)
      ≤ ((∑ i ∈ s, a i ^ p) ^ (1 / (p / r)) * (∑ i ∈ s, b i ^ q) ^ (1 / (q / r))) ^ (1 / r) :=
        Real.rpow_le_rpow hS hH (by positivity)
    _ = (∑ i ∈ s, a i ^ p) ^ (1 / p) * (∑ i ∈ s, b i ^ q) ^ (1 / q) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _),
          ← Real.rpow_mul hA, ← Real.rpow_mul hB]
        congr 2 <;> field_simp

end SingularAux

end InfrastructureC

section InfrastructureD

open scoped InnerProductSpace
open Finset

namespace SingularAux

/-- Rearrangement, `Fin` version. -/
theorem rearrangement_fin (n : ℕ) (s t : Fin n → ℝ) (hs : Antitone s) (ht : Antitone t)
    (hs0 : ∀ i, 0 ≤ s i) (ht0 : ∀ i, 0 ≤ t i) (P : Fin n → Fin n → ℝ)
    (hP0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b ≤ 1) (hcol : ∀ b, ∑ a, P a b ≤ 1) :
    ∑ a, ∑ b, s a * t b * P a b ≤ ∑ i, s i * t i := by
  let ext : (Fin n → ℝ) → ℕ → ℝ := fun f i => if h : i < n then f ⟨i, h⟩ else 0
  let P' : ℕ → ℕ → ℝ := fun i j => if h : i < n ∧ j < n then P ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  have hsum : ∀ f : ℕ → ℝ, ∑ i ∈ range n, f i = ∑ i : Fin n, f i :=
    fun f => (Fin.sum_univ_eq_sum_range f n).symm
  have key := rearrangement n (ext s) (ext t)
    (fun i j hij hj => by
      simp only [ext, dif_pos hj, dif_pos (show i < n by omega)]
      exact hs (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hj⟩ from hij))
    (fun i j hij hj => by
      simp only [ext, dif_pos hj, dif_pos (show i < n by omega)]
      exact ht (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hj⟩ from hij))
    (fun i hi => by simp only [ext, dif_pos hi]; exact hs0 _)
    (fun i hi => by simp only [ext, dif_pos hi]; exact ht0 _) P'
    (fun a ha b hb => by simp only [P', dif_pos (And.intro ha hb)]; exact hP0 _ _)
    (fun a ha => by
      rw [hsum]
      simpa only [P', dif_pos (And.intro ha (Fin.is_lt _))] using hrow ⟨a, ha⟩)
    (fun b hb => by
      rw [hsum]
      simpa only [P', dif_pos (And.intro (Fin.is_lt _) hb)] using hcol ⟨b, hb⟩)
  simp only [hsum, ext, P', Fin.is_lt, dif_pos, and_true, Fin.eta] at key
  exact key

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

set_option quotPrecheck false in
local notation "bas" T => (LinearMap.isSymmetric_adjoint_comp_self T).eigenvectorBasis rfl

theorem apply_eq_sum_wv (X : E →ₗ[𝕜] E) (u : E) :
    X u = ∑ a, ⟪(bas X) a, u⟫_𝕜 • (((X.singularValues a : ℝ) : 𝕜) • wv X a) := by
  conv_lhs => rw [← (bas X).sum_repr' u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, apply_eigenvectorBasis_eq_smul_wv]

/-- **von Neumann's trace inequality**. -/
theorem norm_trace_comp_le (X Y : E →ₗ[𝕜] E) :
    ‖LinearMap.trace 𝕜 E (X ∘ₗ Y)‖ ≤
      ∑ i ∈ range (Module.finrank 𝕜 E), X.singularValues i * Y.singularValues i := by
  set n := Module.finrank 𝕜 E
  let sX : Fin n → ℝ := fun a => X.singularValues a
  let sY : Fin n → ℝ := fun a => Y.singularValues a
  let P : Fin n → Fin n → ℝ := fun a b => ‖⟪wv Y b, (bas X) a⟫_𝕜‖ ^ 2
  let Q : Fin n → Fin n → ℝ := fun a b => ‖⟪wv X a, (bas Y) b⟫_𝕜‖ ^ 2
  have hterm : ∀ b, ⟪(bas Y) b, (X ∘ₗ Y) ((bas Y) b)⟫_𝕜 =
      ∑ a, ((sX a * sY b : ℝ) : 𝕜) * (⟪(bas X) a, wv Y b⟫_𝕜 * ⟪(bas Y) b, wv X a⟫_𝕜) := by
    intro b
    rw [LinearMap.comp_apply, apply_eigenvectorBasis_eq_smul_wv, map_smul, apply_eq_sum_wv X,
      inner_smul_right, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_right, inner_smul_right, RCLike.ofReal_mul]
    simp only [sX, sY]
    ring
  have hbound : ∀ a b, ‖((sX a * sY b : ℝ) : 𝕜) * (⟪(bas X) a, wv Y b⟫_𝕜 *
      ⟪(bas Y) b, wv X a⟫_𝕜)‖ ≤ sX a * sY b * ((P a b + Q a b) / 2) := by
    intro a b
    have hsX : 0 ≤ sX a := X.singularValues_nonneg _
    have hsY : 0 ≤ sY b := Y.singularValues_nonneg _
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (mul_nonneg hsX hsY)]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hsX hsY)
    have e1 : ‖⟪(bas X) a, wv Y b⟫_𝕜‖ = ‖⟪wv Y b, (bas X) a⟫_𝕜‖ := norm_inner_symm _ _
    have e2 : ‖⟪(bas Y) b, wv X a⟫_𝕜‖ = ‖⟪wv X a, (bas Y) b⟫_𝕜‖ := norm_inner_symm _ _
    rw [e1, e2]
    nlinarith [sq_nonneg (‖⟪wv Y b, (bas X) a⟫_𝕜‖ - ‖⟪wv X a, (bas Y) b⟫_𝕜‖)]
  have hanti_X : Antitone sX := fun i j h => sv_antitone X h
  have hanti_Y : Antitone sY := fun i j h => sv_antitone Y h
  have hP : ∑ a, ∑ b, sX a * sY b * P a b ≤ ∑ i, sX i * sY i :=
    rearrangement_fin n sX sY hanti_X hanti_Y (fun _ => X.singularValues_nonneg _)
      (fun _ => Y.singularValues_nonneg _) P (fun _ _ => by positivity)
      (fun a => by
        simpa [P] using sum_norm_inner_wv_le Y ((bas X) a))
      (fun b => by
        have := (bas X).sum_sq_norm_inner_left (wv Y b)
        have h1 := norm_wv_le Y b
        simp only [P]
        calc ∑ a, ‖⟪wv Y b, (bas X) a⟫_𝕜‖ ^ 2 = ‖wv Y b‖ ^ 2 := this
          _ ≤ 1 := by nlinarith [norm_nonneg (wv Y b)])
  have hQ : ∑ a, ∑ b, sX a * sY b * Q a b ≤ ∑ i, sX i * sY i :=
    rearrangement_fin n sX sY hanti_X hanti_Y (fun _ => X.singularValues_nonneg _)
      (fun _ => Y.singularValues_nonneg _) Q (fun _ _ => by positivity)
      (fun a => by
        have := (bas Y).sum_sq_norm_inner_left (wv X a)
        have h1 := norm_wv_le X a
        simp only [Q]
        calc ∑ b, ‖⟪wv X a, (bas Y) b⟫_𝕜‖ ^ 2 = ‖wv X a‖ ^ 2 := this
          _ ≤ 1 := by nlinarith [norm_nonneg (wv X a)])
      (fun b => by
        simpa [Q] using sum_norm_inner_wv_le X ((bas Y) b))
  rw [LinearMap.trace_eq_sum_inner _ (bas Y), ← Fin.sum_univ_eq_sum_range
    (fun i => X.singularValues i * Y.singularValues i)]
  calc ‖∑ b, ⟪(bas Y) b, (X ∘ₗ Y) ((bas Y) b)⟫_𝕜‖
      ≤ ∑ b, ‖⟪(bas Y) b, (X ∘ₗ Y) ((bas Y) b)⟫_𝕜‖ := norm_sum_le _ _
    _ ≤ ∑ b, ∑ a, sX a * sY b * ((P a b + Q a b) / 2) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [hterm]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hbound a b)
    _ = (∑ a, ∑ b, sX a * sY b * P a b + ∑ a, ∑ b, sX a * sY b * Q a b) / 2 := by
        rw [Finset.sum_comm]
        simp only [mul_add, add_div, Finset.sum_add_distrib, Finset.sum_div, mul_div_assoc]
    _ ≤ ∑ i : Fin n, sX i * sY i := by linarith

end SingularAux

end InfrastructureD

section InfrastructureE

open scoped InnerProductSpace
open Finset

namespace SingularAux

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

set_option quotPrecheck false in
local notation "bas" T => (LinearMap.isSymmetric_adjoint_comp_self T).eigenvectorBasis rfl

/-- The Ky Fan partial isometry `v ↦ ∑_{a<k} ⟪w_a, v⟫ b_a`. -/
noncomputable def kyFan (X : E →ₗ[𝕜] E) (k : ℕ) : E →ₗ[𝕜] E :=
  ∑ a : Fin (Module.finrank 𝕜 E),
    if (a : ℕ) < k then (innerₛₗ 𝕜 (wv X a)).smulRight ((bas X) a) else 0

theorem kyFan_apply (X : E →ₗ[𝕜] E) (k : ℕ) (v : E) :
    kyFan X k v = ∑ a : Fin (Module.finrank 𝕜 E),
      (if (a : ℕ) < k then ⟪wv X a, v⟫_𝕜 else 0) • (bas X) a := by
  simp only [kyFan, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem inner_kyFan (X : E →ₗ[𝕜] E) (k : ℕ) (v : E) (j : Fin (Module.finrank 𝕜 E)) :
    ⟪(bas X) j, kyFan X k v⟫_𝕜 = if (j : ℕ) < k then ⟪wv X j, v⟫_𝕜 else 0 := by
  rw [kyFan_apply, inner_sum]
  simp_rw [inner_smul_right,
    orthonormal_iff_ite.mp (bas X).orthonormal j, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem norm_kyFan_le (X : E →ₗ[𝕜] E) (k : ℕ) (v : E) : ‖kyFan X k v‖ ≤ ‖v‖ := by
  have h1 := (bas X).sum_sq_norm_inner_right (kyFan X k v)
  have h2 := sum_norm_inner_wv_le X v
  simp_rw [inner_kyFan] at h1
  have h3 : ‖kyFan X k v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← h1]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) h2
    split_ifs <;> simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

theorem trace_kyFan_comp (X : E →ₗ[𝕜] E) (k : ℕ) :
    LinearMap.trace 𝕜 E (kyFan X k ∘ₗ X) =
      ∑ j : Fin (Module.finrank 𝕜 E), if (j : ℕ) < k then ((X.singularValues j : ℝ) : 𝕜) else 0 := by
  rw [LinearMap.trace_eq_sum_inner _ (bas X)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, inner_kyFan]
  split_ifs
  · rw [apply_eigenvectorBasis_eq_smul_wv, inner_smul_right, inner_wv]
    split_ifs with h
    · simp
    · have : X.singularValues j = 0 := by tauto
      simp [this]
  · rfl

theorem kyFan_apply_eq_zero (X A : E →ₗ[𝕜] E) (k : ℕ) (v : E)
    (hv : ∀ j : Fin (Module.finrank 𝕜 E), (j : ℕ) < k → ⟪A.adjoint (wv X j), v⟫_𝕜 = 0) :
    kyFan X k (A v) = 0 := by
  rw [kyFan_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · rw [← LinearMap.adjoint_inner_left, hv j h, zero_smul]
  · rw [zero_smul]

/-- Weak majorization `s(TS) ≺_w s(T) s(S)`. -/
theorem sum_sv_comp_le (T S : E →ₗ[𝕜] E) (k : ℕ) (hk : k ≤ Module.finrank 𝕜 E) :
    ∑ i ∈ range k, (T ∘ₗ S).singularValues i ≤
      ∑ i ∈ range k, T.singularValues i * S.singularValues i := by
  set n := Module.finrank 𝕜 E
  let X := T ∘ₗ S
  let W := kyFan X k
  have htr : ∑ i ∈ range k, X.singularValues i =
      RCLike.re (LinearMap.trace 𝕜 E ((W ∘ₗ T) ∘ₗ S)) := by
    rw [LinearMap.comp_assoc, trace_kyFan_comp, map_sum]
    simp only [apply_ite, RCLike.ofReal_re, map_zero]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then X.singularValues i else 0) n,
      ← Finset.sum_range_add_sum_Ico _ hk]
    rw [Finset.sum_eq_zero (s := Ico k n) (fun i hi => by
      rw [mem_Ico] at hi; simp [show ¬ i < k by omega]), add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    simp [hi]
  have hWT : ∀ i, (W ∘ₗ T).singularValues i ≤ if i < k then T.singularValues i else 0 := by
    intro i
    split_ifs with hi
    · simpa using sv_comp_left_le W T 1 zero_le_one (fun v => by simpa using norm_kyFan_le X k v) i
    · refine le_of_eq (sv_eq_zero_of_orth (W ∘ₗ T) i
        (fun j : Fin k => T.adjoint (wv X ⟨j, by omega⟩)) (by simp; omega) fun v hv => ?_)
      exact kyFan_apply_eq_zero X T k v (fun j hj => hv ⟨j, hj⟩)
  rw [htr]
  refine (RCLike.re_le_norm _).trans ((norm_trace_comp_le _ _).trans ?_)
  calc ∑ i ∈ range n, (W ∘ₗ T).singularValues i * S.singularValues i
      ≤ ∑ i ∈ range n, (if i < k then T.singularValues i else 0) * S.singularValues i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hWT i) (S.singularValues_nonneg i)
    _ = ∑ i ∈ range k, T.singularValues i * S.singularValues i := by
        rw [← Finset.sum_range_add_sum_Ico _ hk]
        rw [Finset.sum_eq_zero (s := Ico k n) (fun i hi => by
          rw [mem_Ico] at hi; simp [show ¬ i < k by omega]), add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [mem_range] at hi
        simp [hi]

/-- Schatten–Hölder for singular value sums over `range (finrank)`. -/
theorem schatten_holder (T S : E →ₗ[𝕜] E) {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hrecip : 1 / r = 1 / p + 1 / q) :
    (∑ i ∈ range (Module.finrank 𝕜 E), (T ∘ₗ S).singularValues i ^ r) ^ (1 / r) ≤
      (∑ i ∈ range (Module.finrank 𝕜 E), T.singularValues i ^ p) ^ (1 / p) *
        (∑ i ∈ range (Module.finrank 𝕜 E), S.singularValues i ^ q) ^ (1 / q) := by
  have hmaj := sum_rpow_le_of_weak_maj (Module.finrank 𝕜 E) (fun i => (T ∘ₗ S).singularValues i)
    (fun i => T.singularValues i * S.singularValues i)
    (fun i j hij _ => sv_antitone _ hij) (fun i _ => (T ∘ₗ S).singularValues_nonneg i)
    (fun i _ => mul_nonneg (T.singularValues_nonneg i) (S.singularValues_nonneg i))
    (fun k hk => sum_sv_comp_le T S (k + 1) hk) r hr
  refine (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg ((T ∘ₗ S).singularValues_nonneg i) _) hmaj (by positivity)).trans ?_
  exact sum_mul_rpow_le _ _ _ (fun i => T.singularValues_nonneg i)
    (fun i => S.singularValues_nonneg i) (by linarith) (by linarith) (by linarith) hrecip

theorem sum_rpow_mul_const (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (C : ℝ) (hC : 0 ≤ C)
    {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ s, (f i * C) ^ p) ^ (1 / p) = (∑ i ∈ s, f i ^ p) ^ (1 / p) * C := by
  simp_rw [Real.mul_rpow (hf _) hC]
  rw [← Finset.sum_mul, Real.mul_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _)
    (Real.rpow_nonneg hC _), ← Real.rpow_mul hC, mul_one_div_cancel hp.ne', Real.rpow_one]

theorem schatten_comp_right_le (T S : E →ₗ[𝕜] E) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖S v‖ ≤ C * ‖v‖) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ range (Module.finrank 𝕜 E), (T ∘ₗ S).singularValues i ^ p) ^ (1 / p) ≤
      (∑ i ∈ range (Module.finrank 𝕜 E), T.singularValues i ^ p) ^ (1 / p) * C := by
  rw [← sum_rpow_mul_const _ _ (fun i => T.singularValues_nonneg i) C hC0 hp]
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg ((T ∘ₗ S).singularValues_nonneg i) _)
    (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact Real.rpow_le_rpow ((T ∘ₗ S).singularValues_nonneg i)
    (sv_comp_right_le T S C hC0 hC i) hp.le

theorem schatten_comp_left_le (T S : E →ₗ[𝕜] E) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖T v‖ ≤ C * ‖v‖) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ range (Module.finrank 𝕜 E), (T ∘ₗ S).singularValues i ^ p) ^ (1 / p) ≤
      C * (∑ i ∈ range (Module.finrank 𝕜 E), S.singularValues i ^ p) ^ (1 / p) := by
  rw [mul_comm, ← sum_rpow_mul_const _ _ (fun i => S.singularValues_nonneg i) C hC0 hp]
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg ((T ∘ₗ S).singularValues_nonneg i) _)
    (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact Real.rpow_le_rpow ((T ∘ₗ S).singularValues_nonneg i)
    ((sv_comp_left_le T S C hC0 hC i).trans_eq (mul_comm _ _)) hp.le

end SingularAux

end InfrastructureE

section InfrastructureF

open scoped InnerProductSpace
open Finset

namespace SingularAux

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- For a positive operator, the eigenvalues of `T†T` are the squares of those of `T`. -/
theorem eigenvalues_adjoint_comp_self_of_positive' (T : E →ₗ[𝕜] E) (hT : T.IsPositive) :
    T.isSymmetric_adjoint_comp_self.eigenvalues rfl =
      fun i => (hT.isSymmetric.eigenvalues rfl i) ^ 2 := by
  refine eigenvalues_eq_of_basis _ _ rfl (hT.isSymmetric.eigenvectorBasis rfl) _ ?_ ?_
  · intro i j hij
    have hle := hT.isSymmetric.eigenvalues_antitone rfl hij
    have hj := hT.nonneg_eigenvalues rfl j
    exact pow_le_pow_left₀ hj hle 2
  · intro j
    rw [hT.adjoint_eq, LinearMap.comp_apply, hT.isSymmetric.apply_eigenvectorBasis, map_smul,
      hT.isSymmetric.apply_eigenvectorBasis, smul_smul, ← RCLike.ofReal_mul, sq]

theorem singularValues_of_positive (T : E →ₗ[𝕜] E) (hT : T.IsPositive)
    (i : Fin (Module.finrank 𝕜 E)) :
    T.singularValues i = hT.isSymmetric.eigenvalues rfl i := by
  rw [T.singularValues_fin rfl, eigenvalues_adjoint_comp_self_of_positive' T hT,
    Real.sqrt_sq (hT.nonneg_eigenvalues rfl i)]

/-- Sums of a function of the eigenvalues may be computed in any orthonormal eigenbasis. -/
theorem sum_eigenvalues_eq_of_basis (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {ι : Type*}
    [Fintype ι] (e : OrthonormalBasis ι 𝕜 E) (ν : ι → ℝ) (he : ∀ j, T (e j) = (ν j : 𝕜) • e j)
    (f : ℝ → ℝ) :
    ∑ i, f (hT.eigenvalues rfl i) = ∑ j, f (ν j) := by
  have hcard : Fintype.card ι = Module.finrank 𝕜 E :=
    (Module.finrank_eq_card_basis e.toBasis).symm
  let σ₀ : Fin (Module.finrank 𝕜 E) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let ν' : Fin (Module.finrank 𝕜 E) → ℝ := ν ∘ σ₀
  let τ : Fin (Module.finrank 𝕜 E) ≃ ι := Fin.revPerm.trans ((Tuple.sort ν').trans σ₀)
  have hanti : Antitone (ν ∘ τ) := by
    intro i j hij
    have := Tuple.monotone_sort ν' (Fin.rev_le_rev.mpr hij)
    simpa [τ, ν', Function.comp_apply] using this
  have heig : hT.eigenvalues rfl = ν ∘ τ := by
    refine eigenvalues_eq_of_basis T hT rfl (e.reindex τ.symm) (ν ∘ τ) hanti fun j => ?_
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    exact he (τ j)
  rw [heig]
  exact Equiv.sum_comp τ (fun j => f (ν j))

end SingularAux

namespace SingularAux

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A matrix diagonalized by the eigenvector unitary of a Hermitian matrix acts diagonally on the
corresponding eigenbasis. -/
theorem toEuclideanLin_conj_diagonal_apply (H : Matrix n n 𝕜) (hH : H.IsHermitian)
    (ν : n → ℝ) (j : n) :
    Matrix.toEuclideanLin ((↑hH.eigenvectorUnitary : Matrix n n 𝕜) *
        Matrix.diagonal (fun i => (ν i : 𝕜)) * star (↑hH.eigenvectorUnitary : Matrix n n 𝕜))
      (hH.eigenvectorBasis j) = (ν j : 𝕜) • hH.eigenvectorBasis j := by
  open Matrix in
  have h : ((↑hH.eigenvectorUnitary : Matrix n n 𝕜) *
        Matrix.diagonal (fun i => (ν i : 𝕜)) * star (↑hH.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ
      ⇑(hH.eigenvectorBasis j) = (ν j : 𝕜) • ⇑(hH.eigenvectorBasis j) := by
    rw [← Matrix.mulVec_mulVec, hH.star_eigenvectorUnitary_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.diagonal_mulVec_single, mul_one, ← hH.eigenvectorUnitary_mulVec, ← Matrix.mulVec_smul]
    congr 1
    ext i
    simp [Pi.single_apply]
  rw [Matrix.toLpLin_apply]
  apply PiLp.ext
  intro i
  rw [h]
  rfl

end SingularAux

end InfrastructureF
