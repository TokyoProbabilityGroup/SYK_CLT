import SYK.CLT.Lemmas.GaussianPolynomialDensity
import SYK.F04Scratch
import SYK.CLT.Lemmas.Rademacher

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace SYK.CLT

theorem norm_sq_hermiteFiniteProjection {ι : Type*} [Fintype ι]
    (s : Finset (ι → ℕ)) (f : Lp ℝ 2 (SYK.gaussianCouplings ι)) :
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

theorem norm_sq_hermiteDegreeProjection {ι : Type*} [Fintype ι]
    (r : ℕ) (f : Lp ℝ 2 (SYK.gaussianCouplings ι)) :
    ‖hermiteDegreeProjection r f‖ ^ 2 =
      ∑ α ∈ multiIndices_degree r, |⟪hermiteLp α, f⟫_ℝ| ^ 2 /
        ∏ i : ι, ((α i).factorial : ℝ) := by
  exact norm_sq_hermiteFiniteProjection (multiIndices_degree r) f

theorem Setting.inner_hermiteLp_YGaussianLp_eq_zero_of_odd
    {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (α : InteractionIndex (S.N n) q → ℕ) (hα : IsOddMultiIndex α) :
    ⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ = 0 := by
  rw [Setting.YGaussianLp, inner_smul_right,
    S.inner_hermiteLp_ZGaussianLp_eq_zero β n α hα, mul_zero]

theorem Setting.norm_sq_hermiteDegreeProjection_le_even_sum
    {q : ℕ} (S : Setting q) (β : ℝ) (n r : ℕ) :
    ‖hermiteDegreeProjection r (S.YGaussianLp β n)‖ ^ 2 ≤
      (β ^ 2 * couplingScale (S.params n) ^ 2) ^ r *
        ∑ α ∈ (multiIndices_degree
          (ι := InteractionIndex (S.N n) q) r).filter IsEvenMultiIndex,
          (∏ I : InteractionIndex (S.N n) q, ((α I).factorial : ℝ))⁻¹ := by
  classical
  rw [norm_sq_hermiteDegreeProjection]
  let s := multiIndices_degree (ι := InteractionIndex (S.N n) q) r
  have hrestrict :
      (∑ α ∈ s, |⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ| ^ 2 /
          ∏ I, ((α I).factorial : ℝ)) =
        ∑ α ∈ s.filter IsEvenMultiIndex,
          |⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ| ^ 2 /
            ∏ I, ((α I).factorial : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro α hαs hαfilter
    have hodd : IsOddMultiIndex α := by
      simpa only [Finset.mem_filter, hαs, true_and] using hαfilter
    rw [S.inner_hermiteLp_YGaussianLp_eq_zero_of_odd β n α hodd]
    simp
  rw [hrestrict, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α hα
  have hdegree : ∑ I, α I = r :=
    mem_multiIndices_degree r α |>.mp (Finset.mem_of_mem_filter hα)
  have hcoeff := S.abs_inner_hermiteLp_YGaussianLp_le β n α
  rw [hdegree] at hcoeff
  have hnum : |⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ| ^ 2 ≤
      (β ^ 2 * couplingScale (S.params n) ^ 2) ^ r := by
    calc
      _ ≤ ((|β| * couplingScale (S.params n)) ^ r) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcoeff 2
      _ = _ := by
        rw [pow_two, ← mul_pow, sq_abs]
        ring
  have hfac : 0 ≤ ∏ I : InteractionIndex (S.N n) q,
      ((α I).factorial : ℝ) := (hermiteFactorial_pos α).le
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hfac)

end SYK.CLT
