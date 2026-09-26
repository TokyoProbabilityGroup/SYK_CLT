import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
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
# Spectral infrastructure

This project's Mathlib version does not provide singular values of operators on finite-dimensional
inner product spaces, nor the Schatten-Hölder inequality. The first part of this file develops
them from the spectral theorem: min-max bounds for eigenvalues, singular values
(`LinearMap.singularValues`), von Neumann's trace inequality, and the Schatten-Hölder inequality.
-/

section InfrastructureA

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The singular values of `T`, in decreasing order, extended by zero. -/
noncomputable def singularValues (T : E →ₗ[𝕜] E) : ℕ →₀ ℝ :=
  Finsupp.onFinset (Finset.range (Module.finrank 𝕜 E))
    (fun i => if h : i < Module.finrank 𝕜 E then
      √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, h⟩) else 0)
    (by
      intro i hi
      rw [Finset.mem_range]
      by_contra h'
      exact hi (dif_neg h'))

theorem singularValues_of_lt (T : E →ₗ[𝕜] E) {n : ℕ} (hn : Module.finrank 𝕜 E = n) {i : ℕ}
    (hi : i < n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩) := by
  subst hn
  simp [singularValues, Finsupp.onFinset_apply, hi]

theorem singularValues_fin (T : E →ₗ[𝕜] E) {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) :=
  T.singularValues_of_lt hn i.2

theorem singularValues_of_finrank_le (T : E →ₗ[𝕜] E) {i : ℕ} (hi : Module.finrank 𝕜 E ≤ i) :
    T.singularValues i = 0 := by
  simp [singularValues, Finsupp.onFinset_apply, Nat.not_lt.mpr hi]

theorem singularValues_nonneg (T : E →ₗ[𝕜] E) (i : ℕ) : 0 ≤ T.singularValues i := by
  unfold singularValues
  rw [Finsupp.onFinset_apply]
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

end LinearMap

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

set_option autoImplicit false

noncomputable section


open scoped BigOperators InnerProductSpace

noncomputable section

namespace MatrixAnalysis.PositiveTrace

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

end MatrixAnalysis.PositiveTrace



open scoped Matrix.Norms.L2Operator

noncomputable section

namespace ExpAux

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

theorem exp_smul_spectral (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
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

theorem charpoly_exp_smul (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).charpoly =
      ∏ j, (Polynomial.X - Polynomial.C (Real.exp (β * hH.eigenvalues j) : 𝕜)) := by
  rw [exp_smul_spectral H hH β, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.charpoly_diagonal]

theorem roots_charpoly_exp_smul (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).charpoly.roots =
      Multiset.map (fun j => (Real.exp (β * hH.eigenvalues j) : 𝕜)) Finset.univ.val := by
  rw [charpoly_exp_smul H hH β]
  rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr (fun j _ =>
    Polynomial.X_sub_C_ne_zero _))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

theorem charpoly_toEuclideanLin (A : Matrix n n 𝕜) :
    (Matrix.toEuclideanLin A).charpoly = A.charpoly := by
  rw [← LinearMap.charpoly_toMatrix (Matrix.toEuclideanLin A)
    (EuclideanSpace.basisFun n 𝕜).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

section
open scoped ComplexOrder

theorem exp_smul_posSemidef (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).PosSemidef := by
  rw [exp_smul_spectral H hH β]
  have hU : IsUnit (↑hH.eigenvectorUnitary : Matrix n n 𝕜) := Unitary.isUnit_coe
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU]
  rw [Matrix.posSemidef_diagonal_iff]
  exact fun i => RCLike.ofReal_nonneg.mpr (Real.exp_pos _).le

theorem exp_smul_posDef (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (β • H)).PosDef := by
  rw [exp_smul_spectral H hH β]
  have hU : IsUnit (↑hH.eigenvectorUnitary : Matrix n n 𝕜) := Unitary.isUnit_coe
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff hU]
  rw [Matrix.posDef_diagonal_iff]
  exact fun i => RCLike.ofReal_pos.mpr (Real.exp_pos _)

end

theorem sum_eigenvalues_exp_smul (H : Matrix n n 𝕜) (hH : H.IsHermitian)
    (β : ℝ) (f : ℝ → ℝ)
    (hT : (Matrix.toEuclideanLin (NormedSpace.exp (β • H))).IsPositive) :
    ∑ i : Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 n)),
      f (hT.isSymmetric.eigenvalues rfl i) =
        ∑ j, f (Real.exp (β * hH.eigenvalues j)) := by
  exact SingularAux.sum_eigenvalues_eq_of_basis _ hT.isSymmetric hH.eigenvectorBasis
    (fun j => Real.exp (β * hH.eigenvalues j)) (fun j => by
      rw [exp_smul_spectral H hH β]
      exact SingularAux.toEuclideanLin_conj_diagonal_apply H hH _ j) f

end ExpAux


namespace SVDAux

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open Polynomial

noncomputable def sv (T : E →ₗ[𝕜] E) (i : Fin (Module.finrank 𝕜 E)) : ℝ :=
  T.singularValues i

theorem sv_nonneg (T : E →ₗ[𝕜] E) (i : Fin (Module.finrank 𝕜 E)) :
    0 ≤ sv T i := T.singularValues_nonneg i

theorem singularValues_sum_rpow (T : E →ₗ[𝕜] E) {p : ℝ} (hp : 0 < p) :
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

theorem charpoly_adjoint_comp_self_of_positive (T : E →ₗ[𝕜] E) (hT : T.IsPositive) :
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

theorem eigenvalues_adjoint_comp_self_of_positive (T : E →ₗ[𝕜] E)
    (hT : T.IsPositive) :
    T.isSymmetric_adjoint_comp_self.eigenvalues rfl =
      fun i => (hT.isSymmetric.eigenvalues rfl i) ^ 2 :=
  SingularAux.eigenvalues_adjoint_comp_self_of_positive' T hT

theorem singularValues_fin_of_positive (T : E →ₗ[𝕜] E) (hT : T.IsPositive)
    (i : Fin (Module.finrank 𝕜 E)) :
    T.singularValues i = hT.isSymmetric.eigenvalues rfl i := by
  rw [T.singularValues_fin rfl,
    eigenvalues_adjoint_comp_self_of_positive T hT,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (hT.nonneg_eigenvalues rfl i)]

end SVDAux

namespace ExpAux

theorem sum_sv_exp {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) (f : ℝ → ℝ) :
    ∑ i : Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 n)),
      f (SVDAux.sv (Matrix.toEuclideanLin (NormedSpace.exp (β • H))) i) =
        ∑ j, f (Real.exp (β * hH.eigenvalues j)) := by
  let T := Matrix.toEuclideanLin (NormedSpace.exp (β • H))
  have hT : T.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (exp_smul_posSemidef H hH β)
  simpa only [SVDAux.sv, T, SVDAux.singularValues_fin_of_positive T hT] using
    sum_eigenvalues_exp_smul H hH β f hT

end ExpAux


open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory

/-!
# Reusable spectral and analytic lemmas for finite-dimensional matrix Gibbs functions

The spectral infrastructure above develops singular values, eigenvalue comparisons, and
Schatten bounds. The sections below turn these tools into estimates for matrix exponentials.

The main reusable pieces are:

* a radial chain rule for scalar rescaling;
* a Banach-algebra Duhamel formula for the derivative of the exponential;
* normalized trace and normalized Schatten norms;
* Schatten Hölder and operator-norm multiplication bounds;
* the exact Schatten norm of an exponential of a Hermitian matrix;
* positive-trace and word bounds, followed by change-of-origin Taylor-coefficient estimates;
* an iterated directional derivative bound for the normalized trace exponential.
-/

namespace MatrixAnalysis

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

/-! ## Duhamel formula -/

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

/-! ## Normalized Schatten norms -/

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
theorem norm_trace_le (T : E →ₗ[𝕜] E) :
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

theorem sum_sv_rpow_eq_sum_range (T : E →ₗ[𝕜] E) (p : ℝ) :
    ∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv T i ^ p =
      ∑ i ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues i ^ p :=
  Fin.sum_univ_eq_sum_range (fun i => T.singularValues i ^ p) _

/-- **Schatten–Hölder inequality** for singular value sums. -/
theorem holder (T S : E →ₗ[𝕜] E) {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hrecip : 1 / r = 1 / p + 1 / q) :
    (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv (T ∘ₗ S) i ^ r) ^ (1 / r) ≤
      (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv T i ^ p) ^ (1 / p) *
        (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv S i ^ q) ^ (1 / q) := by
  simp only [sum_sv_rpow_eq_sum_range]
  exact SingularAux.schatten_holder T S hp hq hr hrecip

/-- Right multiplication by a bounded operator in Schatten norm. -/
theorem mul_opNorm (T S : E →ₗ[𝕜] E) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv (T ∘ₗ S) i ^ p) ^ (1 / p) ≤
      (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv T i ^ p) ^ (1 / p) *
        ‖S.toContinuousLinearMap‖ := by
  simp only [sum_sv_rpow_eq_sum_range]
  exact SingularAux.schatten_comp_right_le T S _ (norm_nonneg _)
    (fun v => S.toContinuousLinearMap.le_opNorm v) (by linarith)

/-- Left multiplication by a bounded operator in Schatten norm. -/
theorem opNorm_mul (T S : E →ₗ[𝕜] E) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv (T ∘ₗ S) i ^ p) ^ (1 / p) ≤
      ‖T.toContinuousLinearMap‖ *
        (∑ i : Fin (Module.finrank 𝕜 E), SVDAux.sv S i ^ p) ^ (1 / p) := by
  simp only [sum_sv_rpow_eq_sum_range]
  exact SingularAux.schatten_comp_left_le T S _ (norm_nonneg _)
    (fun v => T.toContinuousLinearMap.le_opNorm v) (by linarith)

end SchattenAux

namespace ExpAux

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The trace of a Hermitian matrix exponential as a sum over real eigenvalues. -/
theorem trace_exp (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
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

/-- A Hermitian matrix exponential has strictly positive real trace. -/
theorem trace_exp_re_pos [Nonempty n]
    (H : Matrix n n 𝕜) (hH : H.IsHermitian) (β : ℝ) :
    0 < RCLike.re (NormedSpace.exp (β • H)).trace := by
  rw [trace_exp H hH β]
  simp only [map_sum, RCLike.ofReal_re]
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

end ExpAux

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Normalized matrix trace `card(n)⁻¹ * Tr(A)`. -/
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
    refine SingularAux.eigenvalues_eq_of_basis _ hS hn (EuclideanSpace.basisFun (Fin 2) ℝ) _
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
    ExpAux.trace_exp H hH, norm_mul, norm_inv, RCLike.norm_natCast, ← map_sum,
    RCLike.norm_ofReal,
    abs_of_pos (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty), inv_mul_eq_div]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.exp_mul]
  congr 1
  field_simp


/-! ### Trace bounds for words and the Taylor coefficients of `τ ∘ exp` -/

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

theorem sum_sv_conjDiag (H : Matrix n n 𝕜) (hH : H.IsHermitian) (ν : n → ℝ)
    (hν : ∀ j, 0 ≤ ν j) (f : ℝ → ℝ) :
    ∑ i, f (SVDAux.sv (Matrix.toEuclideanLin (conjDiag H hH ν)) i) = ∑ j, f (ν j) := by
  have hT : (Matrix.toEuclideanLin (conjDiag H hH ν)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_conjDiag H hH ν hν)
  simp only [SVDAux.sv, SingularAux.singularValues_of_positive _ hT]
  exact SingularAux.sum_eigenvalues_eq_of_basis _ hT.isSymmetric hH.eigenvectorBasis ν
    (fun j => SingularAux.toEuclideanLin_conj_diagonal_apply H hH ν j) f

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
  have happ := SingularAux.toEuclideanLin_conj_diagonal_apply H hH
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
  rw [FormalMultilinearSeries.changeOriginSeries, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ s : {s : Finset (Fin (k + l)) // s.card = l},
      ‖P.changeOriginSeriesTerm k l s s.2 (fun _ => D) w‖ ≤
        ‖a‖ * ((k + l)! : ℝ)⁻¹ * ((∏ i, ‖w i‖) * ‖normalizedTrace (D ^ l)‖) := by
    intro s
    have hl : (sᶜ : Finset (Fin (k + l))).card = k := by
      rw [Finset.card_compl, Fintype.card_fin, s.2, Nat.add_sub_cancel]
    rw [FormalMultilinearSeries.changeOriginSeriesTerm, ContinuousMultilinearMap.curryFinFinset_apply]
    rw [hP, ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    simp only [NormedSpace.expSeries, ContinuousMultilinearMap.smul_apply,
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

end Matrix

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
