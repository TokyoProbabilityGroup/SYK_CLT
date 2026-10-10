import SYK.CLT.Chaos.HigherChaosRemainder

/-!
# The zeroth chaos and exact relative-partition decomposition

The constant Hermite coefficient of the normalized partition function is one.
Combined with the vanishing first chaos, this separates its quadratic and
higher-degree parts exactly in Gaussian L².
-/

open MeasureTheory Filter
open scoped Topology InnerProductSpace

open SYK.GaussianChaos

namespace SYK.CLT

theorem multiIndices_degree_zero {ι : Type*} [Fintype ι] :
    multiIndices_degree (ι := ι) 0 = {0} := by
  classical
  ext α
  rw [mem_multiIndices_degree, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Nat.zero_le (α j))).mp h i (Finset.mem_univ i)
  · intro h
    subst α
    simp

theorem hermiteLp_zero {ι : Type*} [Fintype ι] :
    (hermiteLp (ι := ι) 0) = Lp.const 2 (gaussianCouplings ι) (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [(hermiteMulti_memLp_two (0 : ι → ℕ)).coeFn_toLp,
    (Lp.coeFn_const (α := ι → ℝ) (μ := gaussianCouplings ι)
      (p := 2) (c := (1 : ℝ)))] with g hg hc
  simp only [hermiteLp]
  rw [hg, hc]
  simp [hermiteMulti, Polynomial.hermite_zero]

theorem integral_Y_pi {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    (∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Y β n (WithLp.toLp 2 g)
      ∂gaussianCouplings (InteractionIndex (S.N n) q)) = 1 := by
  let ι := InteractionIndex (S.N n) q
  have h := S.integral_Y β n
  change (∫ g, S.Y β n g ∂((gaussianCouplings ι).map
    (MeasurableEquiv.toLp 2 (ι → ℝ)))) = 1 at h
  rw [integral_map_equiv (MeasurableEquiv.toLp 2 (ι → ℝ)) (S.Y β n)] at h
  exact h

theorem inner_hermiteLp_zero_Y {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    ⟪hermiteLp (0 : InteractionIndex (S.N n) q → ℕ), S.YGaussianLp β n⟫_ℝ = 1 := by
  rw [MeasureTheory.L2.inner_def]
  have hH := (hermiteMulti_memLp_two (0 : InteractionIndex (S.N n) q → ℕ)).coeFn_toLp
  have hY := S.YGaussianLp_ae β n
  have hconst : (fun g : InteractionIndex (S.N n) q → ℝ =>
      hermiteMulti (0 : InteractionIndex (S.N n) q → ℕ) g) = fun _ => 1 := by
    funext g
    simp [hermiteMulti, Polynomial.hermite_zero]
  have heq : (∫ g, (S.YGaussianLp β n) g *
      (hermiteLp (0 : InteractionIndex (S.N n) q → ℕ)) g
      ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
      ∫ g, S.Y β n (WithLp.toLp 2 g)
      ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
    apply integral_congr_ae
    filter_upwards [hH, hY] with g hgH hgY
    rw [show (hermiteLp (0 : InteractionIndex (S.N n) q → ℕ)) g =
      hermiteMulti 0 g from hgH, hgY]
    simp [hermiteMulti, Polynomial.hermite_zero]
  exact heq.trans (integral_Y_pi S β n)

theorem Setting.Y_zeroChaos {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 0 (S.YGaussianLp β n) =
      Lp.const 2 (gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ) := by
  classical
  simp only [hermiteDegreeProjection, hermiteFiniteProjection,
    multiIndices_degree_zero, Finset.sum_singleton]
  rw [inner_hermiteLp_zero_Y, hermiteLp_zero]
  simp

theorem Setting.Y_decomposition {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    S.YGaussianLp β n =
      Lp.const 2 (gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ) +
      hermiteDegreeProjection 2 (S.YGaussianLp β n) +
      S.higherChaosRemainderLp β n := by
  rw [Setting.higherChaosRemainderLp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, S.Y_firstChaos_eq_zero, S.Y_zeroChaos β n]
  abel

end SYK.CLT
