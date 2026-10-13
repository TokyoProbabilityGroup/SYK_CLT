import SYK.Probability.GaussianChaos.CoefficientIBP
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Orthogonality of Gaussian Hermite products

The one-coordinate pairing follows from the integration-by-parts theorem in
`Probability/GaussianChaos/HermiteIBP.lean`: differentiating past the degree gives zero,
while differentiation at the degree gives the factorial. Factorization of the finite
product Gaussian integral yields the orthogonality and exact norm in
`eq: chaos` of the CLT manuscript.
Entry points: `hermiteMulti_orthogonality`, `inner_hermiteLp`,
`hermiteFiniteProjection_eq_starProjection`.

The expansions `hasSum_hermiteCoefficients` and `hasSum_hermiteDegreeProjection` assume `L²`
completeness of the Hermite family. The versions that do not assume it are
`hasSum_hermiteCoefficients_unconditional` and `hasSum_hermiteDegreeProjection_unconditional`
in `SYK.Probability.GaussianChaos.PolynomialDensity`.
-/

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace SYK.GaussianChaos

private theorem iterate_derivative_hermite_self (n : ℕ) :
    Polynomial.derivative^[n] (Polynomial.hermite n) =
      Polynomial.C (n.factorial : ℤ) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hk : k = 0
  · subst k
    simp [Polynomial.coeff_hermite_self, Nat.descFactorial_self]
  · have hlt : n < k + n := by omega
    simp [Polynomial.coeff_hermite_of_lt hlt, hk]

private theorem partialList_replicate_aeval {ι : Type*} [DecidableEq ι]
    (i : ι) (n : ℕ) (p : Polynomial ℤ) (g : ι → ℝ) :
    partialList (List.replicate n i)
        (fun h => Polynomial.aeval (h i) p) g =
      Polynomial.aeval (g i) (Polynomial.derivative^[n] p) := by
  induction n generalizing p with
  | zero => simp [partialList]
  | succ n ih =>
      have hfun : coordDeriv i (fun h : ι → ℝ => Polynomial.aeval (h i) p) =
          fun h => Polynomial.aeval (h i) (Polynomial.derivative p) := by
        funext h
        exact coordDeriv_aeval i p h
      simp only [List.replicate_succ, partialList, hfun,
        Function.iterate_succ_apply]
      exact ih (Polynomial.derivative p)

private theorem multiIndexList_unit (n : ℕ) :
    multiIndexList (fun _ : Unit => n) = List.replicate n () := by
  simp [multiIndexList]

private theorem hermiteMulti_unit (n : ℕ) (g : Unit → ℝ) :
    hermiteMulti (fun _ : Unit => n) g =
      Polynomial.aeval (g ()) (Polynomial.hermite n) := by
  simp [hermiteMulti]

private theorem hermite_pair_ibp_unit (n m : ℕ) :
    (∫ g : Unit → ℝ,
      Polynomial.aeval (g ()) (Polynomial.hermite n) *
        Polynomial.aeval (g ()) (Polynomial.hermite m)
        ∂(Measure.pi fun _ : Unit => ProbabilityTheory.gaussianReal 0 1)) =
      ∫ g : Unit → ℝ,
        Polynomial.aeval (g ()) (Polynomial.derivative^[n] (Polynomial.hermite m))
        ∂(Measure.pi fun _ : Unit => ProbabilityTheory.gaussianReal 0 1) := by
  have h := hermiteMulti_pair_ibp (ι := Unit)
    (fun _ => n) (fun _ => m)
  have hfun : hermiteMulti (fun _ : Unit => m) =
      fun g => Polynomial.aeval (g ()) (Polynomial.hermite m) := by
    funext g
    exact hermiteMulti_unit m g
  rw [hfun] at h
  simpa only [hermiteMulti_unit, partialMulti, multiIndexList_unit,
    partialList_replicate_aeval] using h

private theorem hermite_pair_integral_unit (n m : ℕ) :
    (∫ g : Unit → ℝ,
      Polynomial.aeval (g ()) (Polynomial.hermite n) *
        Polynomial.aeval (g ()) (Polynomial.hermite m)
        ∂(Measure.pi fun _ : Unit => ProbabilityTheory.gaussianReal 0 1)) =
      if n = m then (n.factorial : ℝ) else 0 := by
  by_cases hnm : n = m
  · subst m
    rw [if_pos rfl]
    have h := hermite_pair_ibp_unit n n
    rw [iterate_derivative_hermite_self] at h
    simpa using h
  · rw [if_neg hnm]
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have h := hermite_pair_ibp_unit m n
      have hz : Polynomial.derivative^[m] (Polynomial.hermite n) = 0 :=
        Polynomial.iterate_derivative_eq_zero (by simpa using hlt)
      rw [hz] at h
      have hzero : (∫ g : Unit → ℝ,
          Polynomial.aeval (g ()) (Polynomial.hermite m) *
            Polynomial.aeval (g ()) (Polynomial.hermite n)
          ∂(Measure.pi fun _ : Unit => ProbabilityTheory.gaussianReal 0 1)) = 0 := by
        simpa using h
      simpa only [mul_comm] using hzero
    · have h := hermite_pair_ibp_unit n m
      have hz : Polynomial.derivative^[n] (Polynomial.hermite m) = 0 :=
        Polynomial.iterate_derivative_eq_zero (by simpa using hgt)
      rw [hz] at h
      simpa using h

/-- One-dimensional probabilists' Hermite orthogonality under the standard
Gaussian law. This is the coordinate factor of the formula in `eq: chaos`. -/
theorem hermite_pair_integral_real (n m : ℕ) :
    (∫ x : ℝ,
      Polynomial.aeval x (Polynomial.hermite n) *
        Polynomial.aeval x (Polynomial.hermite m)
        ∂ProbabilityTheory.gaussianReal 0 1) =
      if n = m then (n.factorial : ℝ) else 0 := by
  have h := hermite_pair_integral_unit n m
  have hmap := MeasureTheory.integral_comp_eval
    (μ := fun _ : Unit => ProbabilityTheory.gaussianReal 0 1) (i := ())
    (f := fun x : ℝ => Polynomial.aeval x (Polynomial.hermite n) *
      Polynomial.aeval x (Polynomial.hermite m)) (by fun_prop)
  rw [hmap] at h
  exact h

/-- The exact Hermite pairing formula in `eq: chaos`, including an empty
coordinate type and zero multi-indices. -/
theorem hermiteMulti_orthogonality {ι : Type*} [Fintype ι]
    (α β : ι → ℕ) :
    (∫ g, hermiteMulti α g * hermiteMulti β g
      ∂gaussianCouplings ι) =
      if α = β then ∏ i : ι, ((α i).factorial : ℝ) else 0 := by
  classical
  calc
    (∫ g, hermiteMulti α g * hermiteMulti β g
      ∂gaussianCouplings ι) =
        ∫ g, ∏ i : ι,
          (Polynomial.aeval (g i) (Polynomial.hermite (α i)) *
            Polynomial.aeval (g i) (Polynomial.hermite (β i)))
          ∂(Measure.pi fun _ : ι => ProbabilityTheory.gaussianReal 0 1) := by
          simp only [hermiteMulti, gaussianCouplings,
            Finset.prod_mul_distrib]
    _ = ∏ i : ι, ∫ x : ℝ,
          Polynomial.aeval x (Polynomial.hermite (α i)) *
            Polynomial.aeval x (Polynomial.hermite (β i))
          ∂ProbabilityTheory.gaussianReal 0 1 := by
          exact MeasureTheory.integral_fintype_prod_eq_prod
            (μ := fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
            (fun i x => Polynomial.aeval x (Polynomial.hermite (α i)) *
              Polynomial.aeval x (Polynomial.hermite (β i)))
    _ = ∏ i : ι, if α i = β i then ((α i).factorial : ℝ) else 0 := by
          simp_rw [hermite_pair_integral_real]
    _ = if α = β then ∏ i : ι, ((α i).factorial : ℝ) else 0 := by
          by_cases h : α = β
          · subst β
            simp
          · have hi : ∃ i, α i ≠ β i := by
              by_contra hh
              push Not at hh
              exact h (funext hh)
            obtain ⟨i, hi⟩ := hi
            rw [if_neg h]
            exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Each finite-dimensional Hermite product represents an element of Gaussian
`L²`, as required for the chaos projections in `eq: chaos`. -/
theorem hermiteMulti_memLp_two {ι : Type*} [Fintype ι] (α : ι → ℕ) :
    MemLp (hermiteMulti α) 2 (gaussianCouplings ι) := by
  apply (memLp_two_iff_integrable_sq (continuous_hermiteMulti α).aestronglyMeasurable).2
  simpa only [pow_two] using integrable_hermiteMulti_mul α α

/-- The Hermite product as an element of real Gaussian `L²`. -/
noncomputable def hermiteLp {ι : Type*} [Fintype ι] (α : ι → ℕ) :
    Lp ℝ 2 (gaussianCouplings ι) :=
  (hermiteMulti_memLp_two α).toLp (hermiteMulti α)

/-- The exact Gaussian `L²` Gram matrix of the Hermite products. -/
theorem inner_hermiteLp {ι : Type*} [Fintype ι] (α β : ι → ℕ) :
    ⟪hermiteLp α, hermiteLp β⟫_ℝ =
      if α = β then ∏ i : ι, ((α i).factorial : ℝ) else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have ha := (hermiteMulti_memLp_two α).coeFn_toLp
  have hb := (hermiteMulti_memLp_two β).coeFn_toLp
  have h : (∫ a : ι → ℝ, ⟪(hermiteLp α) a, (hermiteLp β) a⟫_ℝ
      ∂gaussianCouplings ι) =
      ∫ a, hermiteMulti α a * hermiteMulti β a
        ∂gaussianCouplings ι := by
    apply integral_congr_ae
    filter_upwards [ha, hb] with a ha' hb'
    change (hermiteLp β) a * (hermiteLp α) a = _
    rw [show (hermiteLp α) a = hermiteMulti α a from ha',
      show (hermiteLp β) a = hermiteMulti β a from hb']
    ring
  rw [h, hermiteMulti_orthogonality]

/-- The factorial in the Gaussian Hermite norm is strictly positive. -/
theorem hermiteFactorial_pos {ι : Type*} [Fintype ι] (α : ι → ℕ) :
    0 < ∏ i : ι, ((α i).factorial : ℝ) := by
  exact Finset.prod_pos fun i hi => Nat.cast_pos.mpr (Nat.factorial_pos _)

/-- The Hermite coefficient sum over any finite set of multi-indices. -/
noncomputable def hermiteFiniteProjection {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    Lp ℝ 2 (gaussianCouplings ι) :=
  ∑ α ∈ s, (⟪hermiteLp α, f⟫_ℝ /
    ∏ i : ι, ((α i).factorial : ℝ)) • hermiteLp α

/-- On the chosen finite set, the coefficient sum preserves every Hermite
coefficient. -/
private theorem inner_hermiteFiniteProjection {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (gaussianCouplings ι))
    (β : ι → ℕ) (hβ : β ∈ s) :
    ⟪hermiteLp β, hermiteFiniteProjection s f⟫_ℝ = ⟪hermiteLp β, f⟫_ℝ := by
  classical
  simp only [hermiteFiniteProjection, inner_sum, inner_smul_right]
  simp_rw [inner_hermiteLp]
  simp [mul_ite, hβ]
  field_simp [ne_of_gt (hermiteFactorial_pos β)]

/-- The error of a finite Hermite coefficient sum is orthogonal to every
Hermite polynomial included in the sum. -/
private theorem inner_hermiteFiniteProjection_error {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (gaussianCouplings ι))
    (β : ι → ℕ) (hβ : β ∈ s) :
    ⟪hermiteLp β, f - hermiteFiniteProjection s f⟫_ℝ = 0 := by
  rw [inner_sub_right, inner_hermiteFiniteProjection s f β hβ]
  exact sub_self _

/-- There are only finitely many multi-indices of bounded total degree. -/
private theorem finite_multiIndices_degree_le {ι : Type*} [Fintype ι] (r : ℕ) :
    {α : ι → ℕ | ∑ i, α i ≤ r}.Finite := by
  classical
  let e : {α : ι → ℕ | ∑ i, α i ≤ r} → (ι → Fin (r + 1)) :=
    fun α i => ⟨α.1 i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun j _ => Nat.zero_le (α.1 j))
        (Finset.mem_univ i)).trans α.2)⟩
  have he : Function.Injective e := by
    intro α β h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  haveI : Finite {α : ι → ℕ | ∑ i, α i ≤ r} := Finite.of_injective e he
  exact Set.finite_coe_iff.mpr this

/-- Multi-indices of a fixed homogeneous Gaussian chaos. -/
noncomputable def multiIndicesOfDegree {ι : Type*} [Fintype ι] (r : ℕ) :
    Finset (ι → ℕ) :=
  ((finite_multiIndices_degree_le (ι := ι) r).subset
    (show {α : ι → ℕ | ∑ i, α i = r} ⊆
      {α : ι → ℕ | ∑ i, α i ≤ r} from fun _ h => h.le)).toFinset

theorem mem_multiIndicesOfDegree {ι : Type*} [Fintype ι]
    (r : ℕ) (α : ι → ℕ) :
    α ∈ multiIndicesOfDegree r ↔ ∑ i, α i = r := by
  simp [multiIndicesOfDegree]

/-- Coefficient formula for the finite sum at one homogeneous degree. -/
noncomputable def hermiteDegreeProjection {ι : Type*} [Fintype ι]
    (r : ℕ) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    Lp ℝ 2 (gaussianCouplings ι) :=
  hermiteFiniteProjection (multiIndicesOfDegree r) f

/-- The finite-dimensional subspace spanned by Hermite products in `s`. -/
noncomputable def hermiteFiniteSpan {ι : Type*} [Fintype ι] (s : Finset (ι → ℕ)) :
    Submodule ℝ (Lp ℝ 2 (gaussianCouplings ι)) :=
  Submodule.span ℝ (hermiteLp '' (s : Set (ι → ℕ)))

noncomputable instance hermiteFiniteSpan_finiteDimensional {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) : FiniteDimensional ℝ (hermiteFiniteSpan s) := by
  unfold hermiteFiniteSpan
  exact FiniteDimensional.span_of_finite ℝ (Set.toFinite _)

private theorem hermiteFiniteProjection_mem {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    hermiteFiniteProjection s f ∈ hermiteFiniteSpan s := by
  classical
  unfold hermiteFiniteProjection
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨α, hα, rfl⟩

private theorem hermiteFiniteProjection_error_orthogonal {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    f - hermiteFiniteProjection s f ∈ (hermiteFiniteSpan s)ᗮ := by
  classical
  apply (Submodule.mem_orthogonal' _ _).2
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨β, hβ, rfl⟩ := hw
      rw [real_inner_comm]
      exact inner_hermiteFiniteProjection_error s f β hβ
  | zero => simp
  | add w z _ _ hw hz => simp [inner_add_right, hw, hz]
  | smul c w _ hw => simp [inner_smul_right, hw]

/-- The coefficient formula is the orthogonal projection onto the finite
Hermite span. -/
theorem hermiteFiniteProjection_eq_starProjection {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    hermiteFiniteProjection s f = (hermiteFiniteSpan s).starProjection f := by
  classical
  exact ((hermiteFiniteSpan s).eq_starProjection_of_mem_orthogonal
    (hermiteFiniteProjection_mem s f)
    (hermiteFiniteProjection_error_orthogonal s f)).symm

/-- Unit-norm Hermite products in real Gaussian `L²`. -/
noncomputable def hermiteOrthonormal {ι : Type*} [Fintype ι] (α : ι → ℕ) :
    Lp ℝ 2 (gaussianCouplings ι) :=
  ‖hermiteLp α‖⁻¹ • hermiteLp α

theorem hermiteLp_norm_pos {ι : Type*} [Fintype ι] (α : ι → ℕ) :
    0 < ‖hermiteLp α‖ := by
  have h : 0 < ⟪hermiteLp α, hermiteLp α⟫_ℝ := by
    rw [inner_hermiteLp]
    simpa using hermiteFactorial_pos α
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (hermiteLp α)]

theorem hermiteOrthonormal_orthonormal {ι : Type*} [Fintype ι] :
    Orthonormal ℝ (hermiteOrthonormal (ι := ι)) := by
  classical
  constructor
  · intro α
    have hpos := hermiteLp_norm_pos α
    simp [hermiteOrthonormal, norm_smul, hpos.ne']
  · intro α β hne
    simp [hermiteOrthonormal, inner_smul_left, inner_smul_right,
      inner_hermiteLp, hne]

/-- The normalized Hermite products give a Hilbert basis under the density
hypothesis, proved by `hermiteOrthonormal_dense` in `PolynomialDensity.lean`. -/
noncomputable def hermiteHilbertBasis {ι : Type*} [Fintype ι]
    (hdense : (Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι)))).topologicalClosure
      = ⊤) :
    HilbertBasis (ι → ℕ) ℝ (Lp ℝ 2 (gaussianCouplings ι)) :=
  HilbertBasis.mk hermiteOrthonormal_orthonormal (by rw [hdense])

theorem hasSum_hermiteOrthonormal {ι : Type*} [Fintype ι]
    (hdense : (Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι)))).topologicalClosure
      = ⊤)
    (f : Lp ℝ 2 (gaussianCouplings ι)) :
    HasSum (fun α : ι → ℕ => ⟪hermiteOrthonormal α, f⟫_ℝ • hermiteOrthonormal α) f := by
  simpa only [hermiteHilbertBasis, HilbertBasis.coe_mk,
    HilbertBasis.repr_apply_apply] using (hermiteHilbertBasis hdense).hasSum_repr f

/-- A normalized basis coefficient is the manuscript's factorial coefficient. -/
theorem hermiteOrthonormal_coefficient {ι : Type*} [Fintype ι]
    (α : ι → ℕ) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    ⟪hermiteOrthonormal α, f⟫_ℝ • hermiteOrthonormal α =
      (⟪hermiteLp α, f⟫_ℝ /
        ∏ i : ι, ((α i).factorial : ℝ)) • hermiteLp α := by
  have hnorm : ‖hermiteLp α‖ ^ 2 =
      ∏ i : ι, ((α i).factorial : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, inner_hermiteLp]
    simp
  have hpos := hermiteLp_norm_pos α
  simp only [hermiteOrthonormal, real_inner_smul_left, smul_smul]
  congr 1
  rw [← hnorm]
  field_simp

/-- The full factorial-coefficient series, conditional only on the analytic
density of Hermite products in Gaussian `L²`. -/
theorem hasSum_hermiteCoefficients {ι : Type*} [Fintype ι]
    (hdense : (Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι)))).topologicalClosure
      = ⊤)
    (f : Lp ℝ 2 (gaussianCouplings ι)) :
    HasSum (fun α : ι → ℕ =>
      (⟪hermiteLp α, f⟫_ℝ /
        ∏ i : ι, ((α i).factorial : ℝ)) • hermiteLp α) f := by
  simpa only [← hermiteOrthonormal_coefficient] using hasSum_hermiteOrthonormal hdense f

/-- Grouping a multi-index by its total degree. -/
private def multiIndexDegreeEquiv {ι : Type*} [Fintype ι] :
    (ι → ℕ) ≃ (Σ r : ℕ, {α : ι → ℕ // ∑ i, α i = r}) where
  toFun α := ⟨∑ i, α i, ⟨α, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨r, α, hα⟩
    dsimp
    cases hα
    rfl

private noncomputable instance finiteDegreeSubtype {ι : Type*} [Fintype ι] (r : ℕ) :
    Finite {α : ι → ℕ // ∑ i, α i = r} := by
  exact Set.finite_coe_iff.mp ((finite_multiIndices_degree_le (ι := ι) r).subset
    (fun _ h => h.le))

private noncomputable instance fintypeDegreeSubtype {ι : Type*} [Fintype ι] (r : ℕ) :
    Fintype {α : ι → ℕ // ∑ i, α i = r} := Fintype.ofFinite _

private theorem sum_multiIndicesOfDegree {ι : Type*} [Fintype ι]
    (r : ℕ) {E : Type*} [AddCommMonoid E] (t : (ι → ℕ) → E) :
    (∑ α : {α : ι → ℕ // ∑ i, α i = r}, t α.1) =
      ∑ α ∈ multiIndicesOfDegree r, t α := by
  classical
  let e : {α : ι → ℕ // ∑ i, α i = r} ≃ (multiIndicesOfDegree r) :=
    Equiv.subtypeEquivRight fun α => (mem_multiIndicesOfDegree r α).symm
  calc
    _ = ∑ α : (multiIndicesOfDegree r), t α.1 := by
      apply Fintype.sum_equiv e
      intro α
      rfl
    _ = ∑ α ∈ multiIndicesOfDegree r, t α := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (multiIndicesOfDegree r) (fun α => t α))

/-- The degree-by-degree chaos sum converges in Gaussian `L²` once Hermite
density is available. -/
theorem hasSum_hermiteDegreeProjection {ι : Type*} [Fintype ι]
    (hdense : (Submodule.span ℝ (Set.range (hermiteOrthonormal (ι := ι)))).topologicalClosure
      = ⊤)
    (f : Lp ℝ 2 (gaussianCouplings ι)) :
    HasSum (fun r : ℕ => hermiteDegreeProjection r f) f := by
  classical
  let t : (ι → ℕ) → Lp ℝ 2 (gaussianCouplings ι) :=
    fun α => (⟪hermiteLp α, f⟫_ℝ /
      ∏ i : ι, ((α i).factorial : ℝ)) • hermiteLp α
  have hall : HasSum t f := hasSum_hermiteCoefficients hdense f
  have hgroup : HasSum (fun p : Σ r : ℕ, {α : ι → ℕ // ∑ i, α i = r} =>
      t p.2.1) f := by
    exact (multiIndexDegreeEquiv (ι := ι)).symm.hasSum_iff.mpr hall
  apply hgroup.sigma
  intro r
  simpa only [hermiteDegreeProjection, hermiteFiniteProjection,
    ← sum_multiIndicesOfDegree, t] using
    (hasSum_fintype (fun α : {α : ι → ℕ // ∑ i, α i = r} => t α.1))

/-- The squared norm of a finite Hermite projection is its factorial-weighted coefficient sum. -/
theorem norm_sq_hermiteFiniteProjection {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    ‖hermiteFiniteProjection s f‖ ^ 2 =
      ∑ α ∈ s, |⟪hermiteLp α, f⟫_ℝ| ^ 2 /
        ∏ i : ι, ((α i).factorial : ℝ) := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [hermiteFiniteProjection, inner_sum, sum_inner,
    real_inner_smul_left, inner_smul_right, inner_hermiteLp]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' s α, if_pos hα]
  have hfac : (∏ i : ι, ((α i).factorial : ℝ)) ≠ 0 :=
    ne_of_gt (hermiteFactorial_pos α)
  rw [sq_abs]
  field_simp

/-- The squared norm of a homogeneous Hermite projection is its coefficient sum. -/
theorem norm_sq_hermiteDegreeProjection {ι : Type*} [Fintype ι]
    (r : ℕ) (f : Lp ℝ 2 (gaussianCouplings ι)) :
    ‖hermiteDegreeProjection r f‖ ^ 2 =
      ∑ α ∈ multiIndicesOfDegree r, |⟪hermiteLp α, f⟫_ℝ| ^ 2 /
        ∏ i : ι, ((α i).factorial : ℝ) := by
  exact norm_sq_hermiteFiniteProjection (multiIndicesOfDegree r) f

/-- Distinct homogeneous Hermite chaoses are orthogonal in Gaussian L². -/
theorem inner_hermiteDegreeProjection_eq_zero {ι : Type*} [Fintype ι]
    (r s : ℕ) (hrs : r ≠ s)
    (f g : Lp ℝ 2 (gaussianCouplings ι)) :
    ⟪hermiteDegreeProjection r f, hermiteDegreeProjection s g⟫_ℝ = 0 := by
  classical
  simp only [hermiteDegreeProjection, hermiteFiniteProjection,
    inner_sum, sum_inner, real_inner_smul_left, inner_smul_right]
  apply Finset.sum_eq_zero
  intro α hα
  suffices hinner :
      (∑ γ ∈ multiIndicesOfDegree r,
        (⟪hermiteLp γ, f⟫_ℝ / ∏ i, ((γ i).factorial : ℝ)) *
          ⟪hermiteLp γ, hermiteLp α⟫_ℝ) = 0 by
    rw [hinner, mul_zero]
  apply Finset.sum_eq_zero
  intro γ hγ
  have hne : γ ≠ α := by
    intro heq
    have hγr := (mem_multiIndicesOfDegree r γ).mp hγ
    have hαs := (mem_multiIndicesOfDegree s α).mp hα
    exact hrs (hγr.symm.trans (heq ▸ hαs))
  rw [inner_hermiteLp, if_neg hne]
  ring

/-- The unique degree-zero multi-index is zero. -/
theorem multiIndicesOfDegree_zero {ι : Type*} [Fintype ι] :
    multiIndicesOfDegree (ι := ι) 0 = {0} := by
  classical
  ext α
  rw [mem_multiIndicesOfDegree, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Nat.zero_le (α j))).mp h i (Finset.mem_univ i)
  · intro h
    subst α
    simp

/-- The degree-zero Hermite product is the constant one in Gaussian L². -/
theorem hermiteLp_zero {ι : Type*} [Fintype ι] :
    (hermiteLp (ι := ι) 0) = Lp.const 2 (gaussianCouplings ι) (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [(hermiteMulti_memLp_two (0 : ι → ℕ)).coeFn_toLp,
    (Lp.coeFn_const (α := ι → ℝ) (μ := gaussianCouplings ι)
      (p := 2) (c := (1 : ℝ)))] with g hg hc
  simp only [hermiteLp]
  rw [hg, hc]
  simp [hermiteMulti, Polynomial.hermite_zero]

end SYK.GaussianChaos
