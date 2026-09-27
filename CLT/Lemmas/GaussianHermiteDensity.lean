import SYK.CLT.Lemmas.GaussianHermiteOrthogonality
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Density of Hermite products in Gaussian `L²`

The real probabilists' Hermite polynomials form a basis of `ℝ[X]`.
This module puts multivariate polynomials in the finite Hermite span and
transfers polynomial density to Hermite density. Gaussian polynomial density
is proved in `GaussianPolynomialDensity`.
Entry point: `hermiteOrthonormal_dense_of_mvPolynomialLp_dense`.
-/

namespace SYK.CLT

noncomputable def realHermiteSequence : Polynomial.Sequence ℝ where
  elems' n := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  degree_eq' n := by
    rw [Polynomial.degree_map_eq_of_isUnit_leadingCoeff
      (Int.castRingHom ℝ) (by simp [Polynomial.hermite_monic n])]
    exact Polynomial.degree_hermite n

/-- The real probabilists' Hermite polynomials form an algebraic basis of
the real polynomial ring. -/
noncomputable def realHermiteBasis : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  realHermiteSequence.basis (by
    intro n
    simp [realHermiteSequence, (Polynomial.hermite_monic n).map])

theorem realHermiteBasis_apply (n : ℕ) :
    realHermiteBasis n = (Polynomial.hermite n).map (Int.castRingHom ℝ) := by
  simp [realHermiteBasis, realHermiteSequence]

private noncomputable def polynomialEvalLinear : Polynomial ℝ →ₗ[ℝ] (ℝ → ℝ) :=
  LinearMap.pi fun x => Polynomial.leval x

/-- Every one-variable real polynomial function lies in the finite linear
span of the Hermite functions. -/
theorem polynomial_eval_mem_hermite_span (p : Polynomial ℝ) :
    (fun x : ℝ => p.eval x) ∈
      Submodule.span ℝ (Set.range fun n : ℕ =>
        fun x : ℝ => Polynomial.aeval x (Polynomial.hermite n)) := by
  have hp : p ∈ Submodule.span ℝ (Set.range realHermiteBasis) := by
    rw [realHermiteBasis.span_eq]
    trivial
  change polynomialEvalLinear p ∈ _
  induction hp using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      apply Submodule.subset_span
      refine ⟨n, ?_⟩
      funext x
      simp [polynomialEvalLinear, realHermiteBasis_apply,
        Polynomial.eval_map, Polynomial.aeval_def]
  | zero => simp
  | add p q _ _ hp hq => simpa using Submodule.add_mem _ hp hq
  | smul a p _ hp => simpa using Submodule.smul_mem _ a hp

/-- The product of a family of one-variable polynomial functions. -/
def polynomialProdEval {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℝ) : (ι → ℝ) → ℝ :=
  fun g => ∏ i, (p i).eval (g i)

private theorem polynomialProdEval_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Polynomial ℝ) (i : ι) (q : Polynomial ℝ) :
    polynomialProdEval (Function.update p i q) =
      fun g => q.eval (g i) * ∏ j ∈ Finset.univ.erase i, (p j).eval (g j) := by
  funext g
  have hfun : (fun j => ((Function.update p i q) j).eval (g j)) =
      Function.update (fun j => (p j).eval (g j)) i (q.eval (g i)) := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp [hji]
  simp only [polynomialProdEval, hfun]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]

private noncomputable def polynomialProdEvalCoordLinear {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → Polynomial ℝ) (i : ι) :
    Polynomial ℝ →ₗ[ℝ] ((ι → ℝ) → ℝ) where
  toFun q := polynomialProdEval (Function.update p i q)
  map_add' q₁ q₂ := by
    funext g
    simp [polynomialProdEval_update, Polynomial.eval_add, add_mul]
  map_smul' a q := by
    funext g
    simp [polynomialProdEval_update, Polynomial.eval_smul, smul_eq_mul, mul_assoc]

private theorem polynomialProdEval_hermite {ι : Type*} [Fintype ι]
    (α : ι → ℕ) :
    polynomialProdEval (fun i => realHermiteBasis (α i)) = SYK.hermiteMulti α := by
  funext g
  simp [polynomialProdEval, realHermiteBasis_apply, SYK.hermiteMulti,
    Polynomial.eval_map, Polynomial.aeval_def]

/-- A product of one-variable polynomial functions belongs to the finite
linear span of multivariate Hermite products. -/
theorem polynomialProdEval_mem_hermiteMulti_span {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℝ) :
    polynomialProdEval p ∈
      Submodule.span ℝ (Set.range (fun α : ι → ℕ => SYK.hermiteMulti α)) := by
  classical
  let M : Submodule ℝ ((ι → ℝ) → ℝ) :=
    Submodule.span ℝ (Set.range (fun α : ι → ℕ => SYK.hermiteMulti α))
  have hP : ∀ s : Finset ι, ∀ p : ι → Polynomial ℝ,
      (∀ j, j ∉ s → ∃ n, p j = realHermiteBasis n) →
      polynomialProdEval p ∈ M := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro p hp
        choose α hα using (fun j => hp j (by simp))
        have hpeq : p = fun j => realHermiteBasis (α j) := funext hα
        rw [hpeq, polynomialProdEval_hermite]
        exact Submodule.subset_span ⟨α, rfl⟩
    | @insert i s his ih =>
        intro p hp
        have hspan : p i ∈ Submodule.span ℝ (Set.range realHermiteBasis) := by
          rw [realHermiteBasis.span_eq]
          trivial
        have hmap : ∀ q ∈ Submodule.span ℝ (Set.range realHermiteBasis),
            polynomialProdEvalCoordLinear p i q ∈ M := by
          intro q hq
          induction hq using Submodule.span_induction with
          | mem q hq =>
              obtain ⟨n, rfl⟩ := hq
              change polynomialProdEval (Function.update p i (realHermiteBasis n)) ∈ M
              apply ih
              intro j hjs
              by_cases hji : j = i
              · subst j
                exact ⟨n, by simp⟩
              · obtain ⟨m, hm⟩ := hp j (by simp [hji, hjs])
                exact ⟨m, by simpa [hji] using hm⟩
          | zero => simp
          | add q r _ _ hq hr => simpa using M.add_mem hq hr
          | smul a q _ hq => simpa using M.smul_mem a hq
        have hi := hmap (p i) hspan
        simpa [polynomialProdEvalCoordLinear] using hi
  exact hP Finset.univ p (by simp)

/-- Every multivariate real polynomial function belongs to the finite
linear span of Hermite products. -/
theorem mvPolynomial_eval_mem_hermiteMulti_span {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    (fun g : ι → ℝ => MvPolynomial.aeval g p) ∈
      Submodule.span ℝ (Set.range (fun α : ι → ℕ => SYK.hermiteMulti α)) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      convert Submodule.add_mem _ hp hq using 1
      funext g
      simp
  | monomial s a =>
      have hq := polynomialProdEval_mem_hermiteMulti_span
        (fun i : ι => Polynomial.X ^ s i)
      have heq : (fun g : ι → ℝ => MvPolynomial.aeval g (MvPolynomial.monomial s a)) =
          a • polynomialProdEval (fun i : ι => Polynomial.X ^ s i) := by
        funext g
        have hprod : s.prod (fun i k => g i ^ k) = ∏ i, g i ^ s i := by
          simp only [Finsupp.prod]
          apply Finset.prod_subset (Finset.subset_univ _)
          intro i _ hi
          simp [Finsupp.notMem_support_iff.mp hi]
        simp [MvPolynomial.aeval_monomial, polynomialProdEval, hprod, smul_eq_mul]
      rw [heq]
      exact Submodule.smul_mem _ a hq

/-- A function in the algebraic Hermite span defines an `L²` class in the
corresponding span of Hermite `L²` classes. -/
theorem memLp_and_span_of_mem_hermiteMulti_span {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ}
    (hf : f ∈ Submodule.span ℝ
      (Set.range (fun α : ι → ℕ => SYK.hermiteMulti α))) :
    ∃ h : MeasureTheory.MemLp f 2 (SYK.gaussianCouplings ι),
      h.toLp f ∈ Submodule.span ℝ (Set.range (hermiteLp (ι := ι))) := by
  let M : Submodule ℝ (MeasureTheory.Lp ℝ 2 (SYK.gaussianCouplings ι)) :=
    Submodule.span ℝ (Set.range (hermiteLp (ι := ι)))
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨α, rfl⟩ := hf
      exact ⟨hermiteMulti_memLp_two α, Submodule.subset_span ⟨α, rfl⟩⟩
  | zero =>
      refine ⟨MeasureTheory.MemLp.zero, ?_⟩
      simp
  | add f g _ _ hf hg =>
      obtain ⟨hf, hfm⟩ := hf
      obtain ⟨hg, hgm⟩ := hg
      refine ⟨hf.add hg, ?_⟩
      rw [MeasureTheory.MemLp.toLp_add hf hg]
      exact M.add_mem hfm hgm
  | smul a f _ hf =>
      obtain ⟨hf, hfm⟩ := hf
      refine ⟨hf.const_smul a, ?_⟩
      rw [MeasureTheory.MemLp.toLp_const_smul a hf]
      exact M.smul_mem a hfm

/-- Every real multivariate polynomial gives an `L²` class in the Hermite
span. This is the algebraic input for Gaussian `L²` density. -/
theorem mvPolynomial_eval_memLp_and_hermiteSpan {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    ∃ h : MeasureTheory.MemLp (fun g : ι → ℝ => MvPolynomial.aeval g p) 2
        (SYK.gaussianCouplings ι),
      h.toLp (fun g : ι → ℝ => MvPolynomial.aeval g p) ∈
        Submodule.span ℝ (Set.range (hermiteLp (ι := ι))) :=
  memLp_and_span_of_mem_hermiteMulti_span
    (mvPolynomial_eval_mem_hermiteMulti_span p)

/-- The Gaussian `L²` class of a multivariate polynomial function. -/
noncomputable def mvPolynomialLp {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) : MeasureTheory.Lp ℝ 2 (SYK.gaussianCouplings ι) :=
  (mvPolynomial_eval_memLp_and_hermiteSpan p).choose.toLp
    (fun g : ι → ℝ => MvPolynomial.aeval g p)

theorem mvPolynomialLp_mem_hermiteSpan {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    mvPolynomialLp p ∈ Submodule.span ℝ (Set.range (hermiteLp (ι := ι))) :=
  (mvPolynomial_eval_memLp_and_hermiteSpan p).choose_spec

theorem hermiteLp_mem_hermiteOrthonormal_span {ι : Type*} [Fintype ι]
    (α : ι → ℕ) :
    hermiteLp α ∈
      Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι))) := by
  have hpos := hermiteLp_norm_pos α
  have hrepr : hermiteLp α = ‖hermiteLp α‖ • hermiteOrthonormal α := by
    simp [hermiteOrthonormal, smul_smul, hpos.ne']
  rw [hrepr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/-- Polynomial density in Gaussian `L²` suffices for completeness of the
normalized Hermite products. -/
theorem hermiteOrthonormal_dense_of_mvPolynomialLp_dense
    {ι : Type*} [Fintype ι]
    (hpoly : (Submodule.span ℝ (Set.range (mvPolynomialLp (ι := ι)))).topologicalClosure
      = ⊤) :
    (Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι)))).topologicalClosure
      = ⊤ := by
  have hle : Submodule.span ℝ (Set.range (mvPolynomialLp (ι := ι))) ≤
      Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι))) := by
    have hspan : ∀ x ∈ Submodule.span ℝ (Set.range (hermiteLp (ι := ι))),
        x ∈ Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι))) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem f hf =>
          obtain ⟨α, rfl⟩ := hf
          exact hermiteLp_mem_hermiteOrthonormal_span α
      | zero => simp
      | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
      | smul a f _ hf => exact Submodule.smul_mem _ a hf
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact hspan _ (mvPolynomialLp_mem_hermiteSpan p)
  apply top_unique
  calc
    (⊤ : Submodule ℝ (MeasureTheory.Lp ℝ 2 (SYK.gaussianCouplings ι))) =
        (Submodule.span ℝ (Set.range (mvPolynomialLp (ι := ι)))).topologicalClosure :=
      hpoly.symm
    _ ≤ (Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι)))).topologicalClosure :=
      Submodule.topologicalClosure_mono hle

end SYK.CLT
