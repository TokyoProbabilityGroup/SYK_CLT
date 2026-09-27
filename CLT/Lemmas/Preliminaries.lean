import SYK.CLT.Main
import SYK.CLT.Lemmas.CliffordSignParity
import SYK.CLT.Lemmas.GaussianHermiteOrthogonality
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Sign

/-!
# Preliminary tools for the SYK central limit theorem

The gauge symmetry in `lem: parity rule lemma` is specialized here to the
normalized real partition function of a `Setting`.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace SYK.CLT

/-- Signed vertex transpositions preserve the normalized finite partition function. -/
theorem Setting.Z_swap {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (i j : Fin (S.N n)) (hij : i ≠ j) :
    ∃ c : InteractionIndex (S.N n) q → ℝ,
      (∀ I, c I = 1 ∨ c I = -1) ∧
      ∀ g : InteractionIndex (S.N n) q → ℝ,
        S.Z β n (WithLp.toLp 2 fun I =>
          c I * g (MajoranaSystem.swapInteractionIndex i j I)) =
        S.Z β n (WithLp.toLp 2 g) := by
  obtain ⟨c, hc, hZ⟩ := partitionFunction_swap (S.params n) (S.majorana n) i j hij β
  refine ⟨c, hc, fun g => ?_⟩
  have h := hZ (fun I => couplingScale (S.params n) * g I)
  have hscale : (fun I => c I * (couplingScale (S.params n) *
      g (MajoranaSystem.swapInteractionIndex i j I))) =
      (fun I => couplingScale (S.params n) *
        (c I * g (MajoranaSystem.swapInteractionIndex i j I))) := by
    funext I
    ring
  erw [hscale] at h
  exact congrArg (fun z : ℂ => (z / (Fintype.card (S.d n) : ℂ)).re) h

/-- Diagonal quadratic coefficients are unchanged by a vertex transposition. -/
theorem Setting.integral_Y_mul_sq_sub_one_swap {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (i j : Fin (S.N n)) (hij : i ≠ j)
    (I : InteractionIndex (S.N n) q) :
    (∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
        ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
    ∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Y β n (WithLp.toLp 2 g) *
        (g (MajoranaSystem.swapInteractionIndex i j I) ^ 2 - 1)
          ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
  obtain ⟨c, hc, hZ⟩ := S.Z_swap β n i j hij
  have hY (g : InteractionIndex (S.N n) q → ℝ) :
      S.Y β n (WithLp.toLp 2 fun J => c J * g (MajoranaSystem.swapInteractionIndex i j J)) =
        S.Y β n (WithLp.toLp 2 g) := by
    unfold Setting.Y
    rw [hZ]
  have hsq (x : ℝ) : (c I * x) ^ 2 = x ^ 2 := by
    rcases hc I with h | h <;> simp [h]
  have h := integral_gaussianCouplings_signed_perm
    (MajoranaSystem.swapInteractionEquiv i j) c hc
    (fun g => S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1))
  simpa only [MajoranaSystem.swapInteractionEquiv, Equiv.coe_fn_mk, hY, hsq] using h.symm

/-- Transpositions act transitively on interaction subsets of fixed cardinality. -/
theorem interaction_function_constant_of_swap {N q : ℕ}
    (f : InteractionIndex N q → ℝ)
    (hf : ∀ (i j : Fin N), i ≠ j → ∀ I,
      f I = f (MajoranaSystem.swapInteractionIndex i j I))
    (I J : InteractionIndex N q) : f I = f J := by
  classical
  let act (e : Equiv.Perm (Fin N)) (K : InteractionIndex N q) : InteractionIndex N q :=
    ⟨K.1.image e, by rw [Finset.card_image_of_injective _ e.injective, K.2]⟩
  have hinv (e : Equiv.Perm (Fin N)) : ∀ K, f K = f (act e K) := by
    induction e using Equiv.Perm.swap_induction_on with
    | one =>
      intro K
      congr 1
      apply Subtype.ext
      simp [act]
    | swap_mul e i j hij he =>
      intro K
      rw [he K, hf i j hij (act e K)]
      congr 1
      apply Subtype.ext
      simp [act, MajoranaSystem.swapInteractionIndex, Finset.image_image,
        Function.comp_def]
  let e : {x // x ∈ I.1} ≃ {x // x ∈ J.1} :=
    Fintype.equivOfCardEq (by simp [I.2, J.2])
  have himage : act e.extendSubtype I = J := by
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact e.extendSubtype_mem y hy
    · rw [(act e.extendSubtype I).2, J.2]
  simpa only [himage] using hinv e.extendSubtype I

/-- Interaction-index independence of the diagonal second-chaos coefficient.
This supplies the symmetry omitted in the proof of `lem:exact-second-chaos`. -/
theorem Setting.integral_Y_mul_sq_sub_one_eq {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (I J : InteractionIndex (S.N n) q) :
    (∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
        ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
    ∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Y β n (WithLp.toLp 2 g) * (g J ^ 2 - 1)
        ∂gaussianCouplings (InteractionIndex (S.N n) q) :=
  interaction_function_constant_of_swap _
    (fun i j hij K => S.integral_Y_mul_sq_sub_one_swap β n i j hij K) I J

/-- `lem: parity rule lemma` for the normalized, scaled finite model. -/
theorem Setting.Z_sign_gauge {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) (s : Fin (S.N n) → ℝ)
    (hs : ∀ x, s x = 1 ∨ s x = -1) :
    S.Z β n (WithLp.toLp 2 fun I => signCharacter s I * g I) = S.Z β n g := by
  let P := S.params n
  let M := S.majorana n
  have hg := SYK.partitionFunction_sign_gauge P (S.N_even n) M β
    (fun I => couplingScale P * g I) s hs
  have hscale : (fun I => signCharacter s I * (couplingScale P * g I)) =
      (fun I => couplingScale P * (signCharacter s I * g I)) := by
    funext I
    ring
  have hg' : SYK.partitionFunction (β : ℂ)
        (hamiltonian P M (fun I => couplingScale P * g I)) =
      SYK.partitionFunction (β : ℂ)
        (hamiltonian P M (fun I => couplingScale P * (signCharacter s I * g I))) := by
    calc
      _ = SYK.partitionFunction (β : ℂ)
          (hamiltonian P M (fun I => signCharacter s I * (couplingScale P * g I))) := hg
      _ = _ := congrArg (fun J => SYK.partitionFunction (β : ℂ) (hamiltonian P M J)) hscale
  change SYK.partitionFunction (β : ℂ) (normalizedHamiltonian P M g) =
    SYK.partitionFunction (β : ℂ)
      (normalizedHamiltonian P M
        (WithLp.toLp 2 fun I => signCharacter s I * g I)) at hg'
  have hnormalized := congrArg
    (fun z : ℂ => (z / (Fintype.card (S.d n) : ℂ)).re) hg'.symm
  change (SYK.partitionFunction (β : ℂ)
      (normalizedHamiltonian P M (WithLp.toLp 2 fun I => signCharacter s I * g I)) /
      (Fintype.card (S.d n) : ℂ)).re =
    (SYK.partitionFunction (β : ℂ) (normalizedHamiltonian P M g) /
      (Fintype.card (S.d n) : ℂ)).re
  exact hnormalized

/-- The odd Hermite coefficients of the finite normalized partition function
vanish in the product Gaussian coordinates of `lem: parity rule lemma`. -/
theorem Setting.integral_Z_mul_hermite_eq_zero_pi {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (α : InteractionIndex (S.N n) q → ℕ)
    (hα : IsOddMultiIndex α) :
    (∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Z β n (WithLp.toLp 2 g) * hermiteMulti α g
        ∂gaussianCouplings (InteractionIndex (S.N n) q)) = 0 := by
  classical
  have hex : ∃ x : Fin (S.N n),
      Odd (∑ I with x ∈ I.1, α I) := by
    by_contra h
    push Not at h
    exact hα fun x => Nat.not_odd_iff_even.mp (h x)
  obtain ⟨x, hx⟩ := hex
  let s : Fin (S.N n) → ℝ := fun y => if y = x then -1 else 1
  let c : InteractionIndex (S.N n) q → ℝ := fun I => if x ∈ I.1 then -1 else 1
  have hs : ∀ y, s y = 1 ∨ s y = -1 := fun y => by
    by_cases h : y = x <;> simp [s, h]
  have hc : ∀ I, c I = 1 ∨ c I = -1 := fun I => by
    by_cases h : x ∈ I.1 <;> simp [c, h]
  have hsc : ∀ I, signCharacter s I = c I := fun I => by
    simp only [signCharacter, s, c]
    rw [Finset.prod_ite_eq']
  have hZ : ∀ g : InteractionIndex (S.N n) q → ℝ,
      S.Z β n (WithLp.toLp 2 fun I => c I * g I) =
        S.Z β n (WithLp.toLp 2 g) := fun g => by
    simpa only [hsc] using S.Z_sign_gauge β n (WithLp.toLp 2 g) s hs
  have hH : ∀ g : InteractionIndex (S.N n) q → ℝ,
      hermiteMulti α (fun I => c I * g I) = -hermiteMulti α g :=
    fun g => hermiteMulti_vertex_flip α x hx g
  have key := integral_gaussianCouplings_sign c hc
    (fun g => S.Z β n (WithLp.toLp 2 g) * hermiteMulti α g)
  simp only [hZ, hH, mul_neg, integral_neg] at key
  linear_combination -key / 2

/-- The parity rule on the actual Euclidean coupling space of `Setting.Z`. -/
theorem Setting.integral_Z_mul_hermite_eq_zero {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (α : InteractionIndex (S.N n) q → ℕ)
    (hα : IsOddMultiIndex α) :
    (∫ g : CouplingSpace (S.N n) q,
      S.Z β n g * hermiteMulti α (WithLp.ofLp g)
        ∂standardGaussianMeasure (S.N n) q) = 0 := by
  let ι := InteractionIndex (S.N n) q
  let F : CouplingSpace (S.N n) q → ℝ :=
    fun g => S.Z β n g * hermiteMulti α (WithLp.ofLp g)
  change (∫ g, F g ∂((gaussianCouplings ι).map
    (MeasurableEquiv.toLp 2 (ι → ℝ)))) = 0
  rw [integral_map_equiv (MeasurableEquiv.toLp 2 (ι → ℝ)) F]
  exact S.integral_Z_mul_hermite_eq_zero_pi β n α hα

/-- Pullback of the finite partition function to the product Gaussian space
used by the Hermite projection API. -/
theorem Setting.ZGaussian_memLp {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    MemLp (fun g : InteractionIndex (S.N n) q → ℝ =>
      S.Z β n (WithLp.toLp 2 g)) 2
      (gaussianCouplings (InteractionIndex (S.N n) q)) := by
  let ι := InteractionIndex (S.N n) q
  have h := (S.partition_moments β n).1
  change MemLp (S.Z β n) 2
    ((gaussianCouplings ι).map (MeasurableEquiv.toLp 2 (ι → ℝ))) at h
  exact ((MeasurableEquiv.toLp 2 (ι → ℝ)).memLp_map_measure_iff).mp h

noncomputable def Setting.ZGaussianLp {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    Lp ℝ 2 (gaussianCouplings (InteractionIndex (S.N n) q)) :=
  (S.ZGaussian_memLp β n).toLp
    (fun g => S.Z β n (WithLp.toLp 2 g))

/-- Every odd Hermite coefficient of `Setting.Z` vanishes in Gaussian `L²`. -/
theorem Setting.inner_hermiteLp_ZGaussianLp_eq_zero {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (α : InteractionIndex (S.N n) q → ℕ)
    (hα : IsOddMultiIndex α) :
    ⟪hermiteLp α, S.ZGaussianLp β n⟫_ℝ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have ha := (hermiteMulti_memLp_two α).coeFn_toLp
  have hb := (S.ZGaussian_memLp β n).coeFn_toLp
  have h : (∫ g : InteractionIndex (S.N n) q → ℝ,
      ⟪(hermiteLp α) g, (S.ZGaussianLp β n) g⟫_ℝ
        ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
      ∫ g, S.Z β n (WithLp.toLp 2 g) * hermiteMulti α g
        ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
    apply integral_congr_ae
    filter_upwards [ha, hb] with g ha' hb'
    change (S.ZGaussianLp β n) g * (hermiteLp α) g = _
    rw [show (hermiteLp α) g = hermiteMulti α g from ha',
      show (S.ZGaussianLp β n) g = S.Z β n (WithLp.toLp 2 g) from hb']
  rw [h]
  exact S.integral_Z_mul_hermite_eq_zero_pi β n α hα

/-- A natural multi-index of total degree one is supported at one coordinate. -/
theorem multiIndex_eq_single_of_degree_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → ℕ) (hdegree : ∑ I, α I = 1) :
    ∃ I, α = Pi.single I 1 := by
  classical
  let d : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm α
  have hd : d.sum (fun _ n => n) = 1 := by
    calc
      d.sum (fun _ n => n) = ∑ I, d I := by
        rw [Finsupp.sum_fintype _ _ fun _ => rfl]
      _ = ∑ I, α I := by simp [d]
      _ = 1 := hdegree
  obtain ⟨I, hI⟩ := (Finsupp.sum_eq_one_iff d).mp hd
  refine ⟨I, ?_⟩
  funext J
  have h := congrArg (fun e : ι →₀ ℕ => e J) hI
  simpa [d, Finsupp.single_apply, Pi.single_apply, eq_comm] using h

/-- A degree-two multi-index has either one doubled coordinate or two
distinct coordinates of degree one. -/
theorem multiIndex_degree_two_cases {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → ℕ) (hdegree : ∑ I, α I = 2) :
    (∃ I, α = Pi.single I 2) ∨
      (∃ I J, I ≠ J ∧ α = Pi.single I 1 + Pi.single J 1) := by
  classical
  have hex : ∃ I, 0 < α I := by
    by_contra h
    push Not at h
    have hzero : ∀ I, α I = 0 := fun I => Nat.eq_zero_of_le_zero (h I)
    simp [hzero] at hdegree
  obtain ⟨I, hIpos⟩ := hex
  have hsplit : (∑ J ∈ (Finset.univ.erase I), α J) + α I = 2 := by
    simpa only [hdegree] using (Finset.sum_erase_add Finset.univ α (Finset.mem_univ I))
  by_cases hI2 : α I = 2
  · left
    refine ⟨I, ?_⟩
    have hrest : ∀ J, J ≠ I → α J = 0 := by
      intro J hJI
      have hmem : J ∈ Finset.univ.erase I := by simp [hJI]
      have hle := Finset.single_le_sum (fun K _ => Nat.zero_le (α K)) hmem
      omega
    funext J
    by_cases hJI : J = I
    · subst J
      simp [hI2]
    · simp [hJI, hrest J hJI]
  · right
    have hI1 : α I = 1 := by omega
    let δ : ι → ℕ := fun J => if J = I then 0 else α J
    have hδsum : ∑ J, δ J = 1 := by
      calc
        (∑ J, δ J) = (∑ J ∈ Finset.univ.erase I, δ J) + δ I :=
          (Finset.sum_erase_add Finset.univ δ (Finset.mem_univ I)).symm
        _ = (∑ J ∈ Finset.univ.erase I, α J) := by
          simp only [δ, if_pos rfl, add_zero]
          apply Finset.sum_congr rfl
          intro J hJ
          simp [Finset.mem_erase.mp hJ |>.1]
        _ = 1 := by omega
    obtain ⟨J, hδ⟩ := multiIndex_eq_single_of_degree_one δ hδsum
    have hJI : I ≠ J := by
      intro h
      subst J
      have := congrFun hδ I
      simp [δ] at this
    refine ⟨I, J, hJI, ?_⟩
    funext K
    have hδK := congrFun hδ K
    by_cases hKI : K = I
    · subst K
      simp [hI1, hJI, δ] at hδK ⊢
    · simp [δ, hKI] at hδK ⊢
      exact hδK

/-- A degree-one multi-index is odd when interactions are nonempty. -/
theorem odd_multiIndex_of_degree_one {N q : ℕ} (hq : 0 < q)
    (α : InteractionIndex N q → ℕ) (hdegree : ∑ I, α I = 1) :
    IsOddMultiIndex α := by
  classical
  obtain ⟨I, hαI⟩ := multiIndex_eq_single_of_degree_one α hdegree
  obtain ⟨x, hx⟩ : I.1.Nonempty := Finset.card_pos.mp (by rw [I.2]; exact hq)
  intro heven
  have hsum : (∑ J with x ∈ J.1, α J) = 1 := by
    simp [hαI, hx]
  have := heven x
  simp [hsum] at this

/-- The first Gaussian chaos of the finite partition function is zero. -/
theorem Setting.Z_firstChaos_eq_zero {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 1 (S.ZGaussianLp β n) = 0 := by
  classical
  unfold hermiteDegreeProjection hermiteFiniteProjection
  apply Finset.sum_eq_zero
  intro α hα
  have hdegree := (mem_multiIndices_degree 1 α).mp hα
  have hodd := odd_multiIndex_of_degree_one
    (lt_of_lt_of_le (by decide : 0 < 4) S.q_ge_four) α hdegree
  simp [S.inner_hermiteLp_ZGaussianLp_eq_zero β n α hodd]

/-- The relative partition function as a product Gaussian `L²` element. -/
noncomputable def Setting.YGaussianLp {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    Lp ℝ 2 (gaussianCouplings (InteractionIndex (S.N n) q)) :=
  (S.meanZ β n)⁻¹ • S.ZGaussianLp β n

theorem Setting.YGaussianLp_ae {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    (S.YGaussianLp β n : (InteractionIndex (S.N n) q → ℝ) → ℝ) =ᵐ[
      gaussianCouplings (InteractionIndex (S.N n) q)]
      (fun g => S.Y β n (WithLp.toLp 2 g)) := by
  have hZ := (S.ZGaussian_memLp β n).coeFn_toLp
  have hsmul := Lp.coeFn_smul (S.meanZ β n)⁻¹ (S.ZGaussianLp β n)
  filter_upwards [hZ, hsmul] with g hg hsg
  simpa only [Setting.YGaussianLp, Setting.Y, div_eq_mul_inv, mul_comm] using
    (hsg.trans (congrArg (fun z : ℝ => (S.meanZ β n)⁻¹ * z) hg))

/-- The first Gaussian chaos of `Y_N` vanishes exactly. -/
theorem Setting.Y_firstChaos_eq_zero {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 1 (S.YGaussianLp β n) = 0 := by
  classical
  unfold hermiteDegreeProjection hermiteFiniteProjection Setting.YGaussianLp
  apply Finset.sum_eq_zero
  intro α hα
  have hdegree := (mem_multiIndices_degree 1 α).mp hα
  have hodd := odd_multiIndex_of_degree_one
    (lt_of_lt_of_le (by decide : 0 < 4) S.q_ge_four) α hdegree
  simp [inner_smul_right, S.inner_hermiteLp_ZGaussianLp_eq_zero β n α hodd]

/-- Two distinct interactions give an odd second-order Hermite multi-index. -/
theorem odd_multiIndex_two_distinct {N q : ℕ} (I J : InteractionIndex N q)
    (hIJ : I ≠ J) :
    IsOddMultiIndex (Pi.single I 1 + Pi.single J 1) := by
  classical
  have hex : ∃ x, x ∈ I.1 ∧ x ∉ J.1 := by
    by_contra h
    apply hIJ
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      by_contra hxJ
      exact h ⟨x, hx, hxJ⟩
    · rw [I.2, J.2]
  obtain ⟨x, hxI, hxJ⟩ := hex
  let α : InteractionIndex N q → ℕ := Pi.single I 1 + Pi.single J 1
  intro heven
  have hsum : (∑ K with x ∈ K.1, α K) = 1 := by
    simp [α, Finset.sum_add_distrib, hxI, hxJ]
  have := heven x
  change Even (∑ K with x ∈ K.1, α K) at this
  simp [hsum] at this

/-- Off-diagonal second-chaos Hermite coefficients of `Y_N` vanish. -/
theorem Setting.inner_offDiagonal_secondChaos_eq_zero {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (I J : InteractionIndex (S.N n) q) (hIJ : I ≠ J) :
    ⟪hermiteLp (Pi.single I 1 + Pi.single J 1), S.YGaussianLp β n⟫_ℝ = 0 := by
  rw [Setting.YGaussianLp, inner_smul_right,
    S.inner_hermiteLp_ZGaussianLp_eq_zero β n _ (odd_multiIndex_two_distinct I J hIJ)]
  simp

end SYK.CLT
