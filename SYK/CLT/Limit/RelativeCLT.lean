import SYK.CLT.Limit.LpDistributionTransfer

/-!
# Relative partition fluctuation on the product Gaussian space

The exact chaos decomposition and vanishing scaled higher-chaos remainder
give the conditional relative central limit theorem under AnnealedInput.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SYK.CLT

local instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (SYK.gaussianCouplings ι) := by
  unfold SYK.gaussianCouplings
  infer_instance

theorem Setting.scaled_higherChaosRemainderLp_ae {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    (S.fluctuationScale n • S.higherChaosRemainderLp β n :
      (InteractionIndex (S.N n) q → ℝ) → ℝ) =ᵐ[
        SYK.gaussianCouplings (InteractionIndex (S.N n) q)]
      fun g => S.relativeFluctuation β n (WithLp.toLp 2 g) -
        (S.fluctuationScale n *
          (β * deriv (fun b => Real.log (S.meanZ b n)) β /
            Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))) *
          quadraticGaussianLp (InteractionIndex (S.N n) q) g := by
  have hdecomp := S.scaled_Y_decomposition β n
  have hY := S.scaled_YGaussianLp_ae β n
  have hYlp :
      ((S.fluctuationScale n •
        (S.YGaussianLp β n -
          Lp.const 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ)) :
        Lp ℝ 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q))) :
        (InteractionIndex (S.N n) q → ℝ) → ℝ) =ᵐ[
          SYK.gaussianCouplings (InteractionIndex (S.N n) q)]
        fun g => S.relativeFluctuation β n (WithLp.toLp 2 g) := by
    have hsmul := Lp.coeFn_smul (S.fluctuationScale n)
      (S.YGaussianLp β n -
        Lp.const 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ))
    have hsub := Lp.coeFn_sub (S.YGaussianLp β n)
      (Lp.const 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) (1 : ℝ))
    filter_upwards [hY, hsmul, hsub] with g hgY hgsmul hgsub
    rw [hgsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hgsub]
    simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using hgY
  have hfun := congrArg
    (fun f : Lp ℝ 2 (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) =>
      (f : (InteractionIndex (S.N n) q → ℝ) → ℝ)) hdecomp
  rw [hfun] at hYlp
  have hsum := Lp.coeFn_add
    ((S.fluctuationScale n *
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))) •
      quadraticGaussianLp (InteractionIndex (S.N n) q))
    (S.fluctuationScale n • S.higherChaosRemainderLp β n)
  have hcoeff := Lp.coeFn_smul
    (S.fluctuationScale n *
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ))))
    (quadraticGaussianLp (InteractionIndex (S.N n) q))
  have hrem := Lp.coeFn_smul (S.fluctuationScale n)
    (S.higherChaosRemainderLp β n)
  filter_upwards [hYlp, hsum, hcoeff, hrem] with g hgY hgSum hgCoeff hgRem
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hgSum hgCoeff
  rw [hgSum, hgCoeff] at hgY
  simp only [Pi.smul_apply, smul_eq_mul] at hgRem ⊢
  rw [← hgRem]
  linarith

theorem Setting.relativeFluctuation_pi_clt {q : ℕ} (S : Setting q)
    (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧ ∀ β : ℝ, |β| < βq → β ≠ 0 →
      TendstoInDistribution
        (fun n (g : InteractionIndex (S.N n) q → ℝ) =>
          S.relativeFluctuation β n (WithLp.toLp 2 g))
        atTop
        (fun x : ℝ =>
          (β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2)) * x)
        (fun n => SYK.gaussianCouplings (InteractionIndex (S.N n) q))
        (gaussianReal 0 1) := by
  obtain ⟨βq, hβq, hrem⟩ := S.scaled_higherChaosRemainderLp_norm_tendsto_zero
  refine ⟨βq, hβq, ?_⟩
  intro β hβ hβ0
  let X (n : ℕ) (g : InteractionIndex (S.N n) q → ℝ) : ℝ :=
    (S.fluctuationScale n *
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        Real.sqrt (2 * (Nat.choose (S.N n) q : ℝ)))) *
      quadraticGaussianLp (InteractionIndex (S.N n) q) g
  let Y (n : ℕ) (g : InteractionIndex (S.N n) q → ℝ) : ℝ :=
    S.relativeFluctuation β n (WithLp.toLp 2 g)
  let R (n : ℕ) : Lp ℝ 2
      (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) :=
    S.fluctuationScale n • S.higherChaosRemainderLp β n
  have hX : TendstoInDistribution X atTop
      (fun x : ℝ =>
        (β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2)) * x)
      (fun n => SYK.gaussianCouplings (InteractionIndex (S.N n) q))
      (gaussianReal 0 1) := S.scaledQuadraticGaussianLp_clt hFE β hβ0
  have hR (n : ℕ) : (R n : (InteractionIndex (S.N n) q → ℝ) → ℝ) =ᵐ[
      SYK.gaussianCouplings (InteractionIndex (S.N n) q)]
      fun g => Y n g - X n g := by
    have hraw := S.scaled_higherChaosRemainderLp_ae β n
    have hsmul := Lp.coeFn_smul (S.fluctuationScale n)
      (S.higherChaosRemainderLp β n)
    filter_upwards [hraw, hsmul] with g hg hs
    rw [hs]
    exact hg
  have hY (n : ℕ) : AEMeasurable (Y n)
      (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) := by
    have hXR : AEMeasurable (fun g => X n g + R n g)
        (SYK.gaussianCouplings (InteractionIndex (S.N n) q)) :=
      (hX.forall_aemeasurable n).add ((Lp.aestronglyMeasurable (R n)).aemeasurable)
    apply hXR.congr
    filter_upwards [hR n] with g hg
    linarith
  exact varying_l2_perturb_clt
    (fun n => SYK.gaussianCouplings (InteractionIndex (S.N n) q))
    (gaussianReal 0 1) X Y
    (fun x : ℝ =>
      (β * deriv hFE.ℓ β * Real.sqrt ((q.factorial : ℝ) / 2)) * x)
    hX hY R hR (hrem β hβ)

end SYK.CLT
