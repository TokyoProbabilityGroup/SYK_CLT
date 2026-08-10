import SYK.GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Proper
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory ENNReal NNReal Set MeasureTheory AEStronglyMeasurable

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}
  {A B : Set X} {f g : X → ℝ≥0∞} {x₀ : X}

@[mk_iff]
class IsCondExp (π : Kernel[𝓑, 𝓧] X X) (μ : Measure[𝓧] X) : Prop where
  condExp_ae_eq_kernel_apply ⦃A : Set X⦄ : MeasurableSet[𝓧] A →
    μ[A.indicator 1| 𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal

-- Added [IsFiniteMeasure μ] and [IsMarkovKernel π] assumptions.
lemma isCondExp_iff_bind_eq_left_of_finite_markov
    [IsFiniteMeasure μ] [IsMarkovKernel π]
    (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) [SigmaFinite (μ.trim h𝓑𝓧)] :
    IsCondExp π μ ↔ μ.bind π = μ := by
  have h_iff_A (A : Set X) (hA : MeasurableSet[𝓧] A) :
      (μ[A.indicator 1|𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal) ↔
        (∀ t, MeasurableSet[𝓑] t → μ (A ∩ t) = ∫⁻ a in t, π a A ∂μ) := by
    have hgm : AEStronglyMeasurable[𝓑] (fun a ↦ π a A) μ :=
      (Kernel.measurable_coe π hA).aestronglyMeasurable
    have hg_fin : ∀ᵐ a ∂ μ, π a A ≠ ⊤ := by
      filter_upwards with a
      exact measure_ne_top (π a) A
    simpa [Filter.eventuallyEq_comm] using
      (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq
        (m := 𝓑) (m0 := 𝓧) (μ := μ)
        h𝓑𝓧 hA (measure_ne_top μ A) hgm hg_fin)
  rw [isCondExp_iff, Measure.ext_iff]
  constructor
  · intro h A hA
    rw [Measure.bind_apply hA (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable]
    rw [← setLIntegral_univ]
    have hforall := (h_iff_A A hA).mp (h hA)
    have h_univ := hforall Set.univ MeasurableSet.univ
    simpa using h_univ.symm
  · intro h A hA
    refine (h_iff_A A hA).mpr ?_
    intro t ht
    have hAt_meas : MeasurableSet[𝓧] (A ∩ t) := hA.inter (h𝓑𝓧 _ ht)
    have hμ_bind : μ (A ∩ t) = (μ.bind π) (A ∩ t) := by
      simpa [eq_comm] using h (A ∩ t) hAt_meas
    have h_bind_apply :
        (μ.bind π) (A ∩ t)
          = ∫⁻ a, π a (A ∩ t) ∂ μ :=
      Measure.bind_apply hAt_meas (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable
    have h_prop := hπ.inter_eq_indicator_mul h𝓑𝓧 hA ht
    have h_integrand :
        (fun a => t.indicator 1 a * π a A)
          = t.indicator (fun a => π a A) := by
      ext a; by_cases ha : a ∈ t <;> simp [ha]
    have hmeas : Measurable[𝓧] (fun a => π a A) :=
      (Kernel.measurable_coe π hA).mono h𝓑𝓧 le_rfl
    calc
      μ (A ∩ t)
          = (μ.bind π) (A ∩ t) := by simpa using hμ_bind
      _ = ∫⁻ a, π a (A ∩ t) ∂ μ := h_bind_apply
      _ = ∫⁻ a, t.indicator 1 a * π a A ∂ μ := by
            simp_rw [h_prop]
      _ = ∫⁻ a, t.indicator (fun a => π a A) a ∂ μ := by
            simp_rw [h_integrand]
      _ = ∫⁻ a in t, π a A ∂ μ := by rw [lintegral_indicator (h𝓑𝓧 t ht) fun a ↦ (π a) A]

lemma isCondExp_iff_bind_eq_left
    [IsFiniteMeasure μ] [IsMarkovKernel π]
    (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) [SigmaFinite (μ.trim h𝓑𝓧)] :
    IsCondExp π μ ↔ μ.bind π = μ := by
  simpa using
    (isCondExp_iff_bind_eq_left_of_finite_markov (μ := μ) (π := π) hπ h𝓑𝓧)

lemma condExp_ae_eq_kernel_apply [IsFiniteMeasure μ] [IsFiniteKernel π]
    (h : ∀ (f : X → ℝ), Bornology.IsBounded (Set.range f) → Measurable[𝓧] f →
      condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    {A : Set X} (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal) := by
  have ind_bdd : Bornology.IsBounded (Set.range (A.indicator (fun _ ↦ (1 : ℝ)))) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rw [range_subset_iff]
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have ind_mble : Measurable[𝓧] (A.indicator (fun _ ↦ (1 : ℝ))) := by
    exact (measurable_indicator_const_iff 1).mpr A_mble
  specialize h _ ind_bdd ind_mble
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

variable [π.IsCondExp μ]

private lemma condExp_indicator_ae_eq_integral_kernel (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂(π x₀)) := by
  apply (IsCondExp.condExp_ae_eq_kernel_apply (π := π) A_mble).trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

private lemma condExp_const_indicator_ae_eq_integral_kernel (c : ℝ) (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (c : ℝ)) x ∂(π x₀)) := by
  have smul_eq : A.indicator (fun _ ↦ (c : ℝ)) = c • A.indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx, smul_eq_mul]
  have foo : c • condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
     =ᵐ[μ] condExp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ))) := by
    rw [smul_eq]; exact (condExp_smul (μ := μ) c (A.indicator (fun _ ↦ (1 : ℝ))) 𝓑).symm
  apply foo.symm.trans
  have h_smul_integral :
      c • (fun x₀ ↦ ∫ (a : X), A.indicator (fun _ ↦ (1 : ℝ)) a ∂π x₀)
        = (fun x₀ ↦ ∫ (a : X), A.indicator (fun _ ↦ (c : ℝ)) a ∂π x₀) := by
    funext x₀
    have h1 :
        ∫ (a : X), A.indicator (fun _ : X ↦ (1 : ℝ)) a ∂(π x₀) = (π x₀).real A := by
      simpa [Set.inter_univ] using
        (MeasureTheory.setIntegral_indicator_one (μ := π x₀) (s := A)
          (hs := by simpa using A_mble) (t := Set.univ))
    have h2 :
        ∫ (a : X), A.indicator (fun _ : X ↦ (c : ℝ)) a ∂(π x₀) = (π x₀).real A • c := by
      simpa [Set.inter_univ] using
        (MeasureTheory.setIntegral_indicator_const (μ := π x₀) (E := ℝ)
          (s := A) (t := Set.univ) (c := c) (hs := by simpa using A_mble))
    simp [h1, h2, smul_eq_mul, mul_comm]
  rw [← h_smul_integral]
  have h_ind1 := condExp_indicator_ae_eq_integral_kernel (μ := μ) (π := π) A_mble
  exact Filter.EventuallyEq.const_smul h_ind1 c

variable [IsFiniteMeasure μ] [IsFiniteKernel π]

private lemma condExp_simpleFunc_ae_eq_integral_kernel (f : @SimpleFunc X 𝓧 ℝ) :
    condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  classical
  letI : MeasurableSpace X := 𝓧
  refine @SimpleFunc.induction _ _ _ _ (fun f => condExp 𝓑 μ f =ᵐ[μ]
    (fun x₀ => ∫ x, f x ∂(π x₀))) ?_ ?_ f
  · intro c s hs
    simp [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
    change condExp 𝓑 μ (s.indicator (fun _ : X => c)) =ᵐ[μ]
      (fun x₀ => ∫ x, s.indicator (fun _ : X => c) x ∂(π x₀))
    exact condExp_const_indicator_ae_eq_integral_kernel (μ := μ) (π := π) (A := s) c hs
  · intro f g _disj hf hg
    have hf_int : Integrable f μ := SimpleFunc.integrable_of_isFiniteMeasure f
    have hg_int : Integrable g μ := SimpleFunc.integrable_of_isFiniteMeasure g
    have h_add_condExp := condExp_add hf_int hg_int 𝓑
    filter_upwards [h_add_condExp, hf, hg] with x₀ h_add hf_eq hg_eq
    rw [SimpleFunc.coe_add, h_add, Pi.add_apply, hf_eq, hg_eq, ← integral_add, ← SimpleFunc.coe_add]
    · exact rfl
    · exact SimpleFunc.integrable_of_isFiniteMeasure f
    exact SimpleFunc.integrable_of_isFiniteMeasure g

open Filter Topology TopologicalSpace

/-- The conditional expectation `condExp m μ f` is AE strongly measurable with respect to `m`. -/
lemma aestronglyMeasurable_condExp
    {α : Type*} [MeasurableSpace α]
    (m : MeasurableSpace α) (μ : Measure α) (f : α → ℝ)
    (hm : m ≤ ‹MeasurableSpace α›) [SigmaFinite (μ.trim hm)] :
    AEStronglyMeasurable[m] (condExp m μ f) μ :=
  stronglyMeasurable_condExp.aestronglyMeasurable

namespace SimpleFunc

open MeasureTheory Filter Set

/-- Pointwise a.e. convergence of the canonical simple-function approximation `approxOn` on
`range f ∪ {0}`. This packages the standard `tendsto_approxOn` with the trivial membership
assumption `f x ∈ closure (range f ∪ {0})`. -/
lemma tendsto_approxOn_range_ae
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ}
    (fmeas : Measurable f) :
    ∀ᵐ x ∂μ,
      Tendsto (fun n => SimpleFunc.approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x)
        atTop (𝓝 (f x)) := by
  have hmem : ∀ᵐ x ∂μ, f x ∈ closure (range f ∪ {0} : Set ℝ) := by
    filter_upwards with x
    exact subset_closure (Or.inl ⟨x, rfl⟩)
  have h0 : (0 : ℝ) ∈ (range f ∪ {0} : Set ℝ) := by simp
  exact hmem.mono (fun x hx => by
    simpa using SimpleFunc.tendsto_approxOn (f := f) (s := range f ∪ {0}) fmeas h0 hx)

end SimpleFunc
open SimpleFunc
/-! Local Fubini/bind lemmas (simple functions → L¹) -/

section LocalFubini

open MeasureTheory

variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X}
variable (μ : Measure[𝓧] X) (π : Kernel[𝓑, 𝓧] X X)
variable {s : Set X}

/-- The bind of a restricted finite measure by a Markov kernel is finite. -/
private lemma isFiniteMeasure_bind_restrict
    [IsFiniteMeasure μ] [IsMarkovKernel π] (h𝓑𝓧 : 𝓑 ≤ 𝓧) (s : Set X) :
    IsFiniteMeasure (((μ.restrict s).bind π)) := by
  haveI : IsFiniteMeasure (μ.restrict s) := inferInstance
  refine ⟨?_⟩
  have h_bind_univ :
      ((μ.restrict s).bind π) Set.univ
        = ∫⁻ x, (π x) Set.univ ∂(μ.restrict s) := by
    have hκ : AEMeasurable (fun x => π x) (μ.restrict s) :=
      (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable.restrict
    simpa using
      (Measure.bind_apply (s := Set.univ) MeasurableSet.univ hκ)
  have hπ_univ :
      (fun x => (π x) Set.univ) = fun _ => (1 : ℝ≥0∞) := by
    funext x
    have _inst : IsProbabilityMeasure (π x) := inferInstance
    simp [IsProbabilityMeasure.measure_univ (μ := π x)]
  have : ((μ.restrict s).bind π) Set.univ = (μ.restrict s) Set.univ := by
    simp [h_bind_univ]
  have hfin : (μ.restrict s) Set.univ < ∞ := by
    simp
  simp [this]

/-- For a simple function and a Markov kernel, the inner kernel integral is finite a.e. -/
private lemma lintegral_ofReal_simpleFunc_ae_lt_top
    [IsFiniteMeasure μ] [IsMarkovKernel π]
    {φ : @SimpleFunc X 𝓧 ℝ} :
    ∀ᵐ x ∂μ, (∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)) < ∞ := by
  filter_upwards with x
  have : Integrable φ (π x) := SimpleFunc.integrable_of_isFiniteMeasure φ
  calc
    ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)
        ≤ ∫⁻ y, ‖φ y‖ₑ ∂(π x) := by
          exact lintegral_ofReal_le_lintegral_enorm ⇑φ
    _ < ∞ := this.2


/-- The kernel integral of ofReal ∘ φ is a.e.-measurable. -/
private lemma aemeasurable_lintegral_ofReal_simpleFunc
    [IsMarkovKernel π] (h𝓑𝓧 : 𝓑 ≤ 𝓧) {φ : @SimpleFunc X 𝓧 ℝ} :
    AEMeasurable (fun x => ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)) μ := by
  /-
  We expand the lintegral of the simple function (φ.map ENNReal.ofReal) as a finite sum
  of measurable functions x ↦ (π x) (ψ ⁻¹' {r}); each summand is measurable, hence the sum is.
  -/
  classical
  set ψ : SimpleFunc X ℝ≥0∞ := φ.map ENNReal.ofReal
  have h_eq :
      (fun x => ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x))
        = fun x => ∑ r ∈ ψ.range, r * (π x) (ψ ⁻¹' {r}) := by
    funext x
    simpa [ψ, SimpleFunc.lintegral] using
      (MeasureTheory.SimpleFunc.lintegral_eq_lintegral (f := ψ) (μ := π x))
  have h_term :
      ∀ r : ℝ≥0∞, Measurable (fun x => r * (π x) (ψ ⁻¹' {r})) := by
    intro r
    have h_set : MeasurableSet[𝓧] (ψ ⁻¹' {r}) := by
      have : Measurable[𝓧] ψ := SimpleFunc.measurable _
      simpa [ψ] using this (measurableSet_singleton r)
    have h_meas_base :
        Measurable (fun x => (π x) (ψ ⁻¹' {r})) :=
      (Kernel.measurable_coe π h_set).mono h𝓑𝓧 le_rfl
    exact h_meas_base.const_mul _
  have h_meas :
      Measurable (fun x => ∑ r ∈ ψ.range, r * (π x) (ψ ⁻¹' {r})) := by
    classical
    refine Finset.measurable_sum _ ?_
    intro r hr
    exact h_term r
  have h_meas_full :
      Measurable (fun x => ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)) := by
    simpa [h_eq]
  exact h_meas_full.aemeasurable

/-- Converting lintegral to Bochner integral: positive part. -/
private lemma lintegral_ofReal_toReal_eq_setIntegral
    [IsFiniteMeasure μ] [IsMarkovKernel π]
    (h𝓑𝓧 : 𝓑 ≤ 𝓧) {s : Set X} {φ : @SimpleFunc X 𝓧 ℝ} :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x) ∂(μ.restrict s)).toReal
      = ∫ x in s, (∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)).toReal ∂μ := by
  have h_ae_fin : ∀ᵐ x ∂(μ.restrict s), (∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)) < ∞ :=
    ae_restrict_of_ae (lintegral_ofReal_simpleFunc_ae_lt_top (μ := μ) (π := π) (φ := φ))
  have h_meas : AEMeasurable (fun x => ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)) (μ.restrict s) :=
    (aemeasurable_lintegral_ofReal_simpleFunc (μ := μ) (π := π) h𝓑𝓧 (φ := φ)).restrict
  have h_eq := integral_toReal h_meas h_ae_fin
  simpa [lintegral_restrict] using h_eq.symm

/-- The inner integral reconstruction from positive and negative parts. -/
private lemma toReal_sub_toReal_eq_integral_simpleFunc
    [IsMarkovKernel π] {φ : @SimpleFunc X 𝓧 ℝ} (x : X) :
    (∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)).toReal
      - (∫⁻ y, ENNReal.ofReal (- φ y) ∂(π x)).toReal
      = ∫ y, φ y ∂(π x) := by
  have : Integrable φ (π x) := SimpleFunc.integrable_of_isFiniteMeasure φ
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part this).symm

/-- Alias for `integrable_of_lintegral_nnnorm_lt_top`. -/
lemma integrable_of_lintegral_ennnorm_lt_top
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → E}
    (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ x, ‖f x‖ₑ ∂μ < ∞) :
    Integrable f μ :=
  ⟨hf, h⟩

lemma integrable_of_lintegral_ofReal_abs_lt_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ x, ENNReal.ofReal |f x| ∂μ < ∞) :
    Integrable f μ := by
  refine ⟨hf, ?_⟩
  have h' : (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) < ∞ := by
    simpa only [Real.norm_eq_abs] using h
  exact (hasFiniteIntegral_iff_norm f).mpr h'

/-- The bind of a finite measure by a Markov kernel is finite. -/
private lemma isFiniteMeasure_bind
    [IsFiniteMeasure μ] [IsMarkovKernel π] (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    IsFiniteMeasure (μ.bind π) := by
  refine ⟨?_⟩
  have hκ : AEMeasurable (fun x => π x) μ :=
    (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable
  have :
      (μ.bind π) Set.univ = ∫⁻ x, (π x) Set.univ ∂μ := by
    simpa using Measure.bind_apply (s := Set.univ) MeasurableSet.univ hκ
  have hprob : (fun x => (π x) Set.univ) = fun _ => (1 : ℝ≥0∞) := by
    funext x; simp
  simp [this]

/-- Integrability of `x ↦ (∫⁻ y, ofReal (φ y) ∂ (π x)).toReal` for a simple function `φ`. -/
private lemma integrable_toReal_lintegral_ofReal_simpleFunc
    [IsFiniteMeasure μ] [IsMarkovKernel π]
    (h𝓑𝓧 : 𝓑 ≤ 𝓧) {φ : @SimpleFunc X 𝓧 ℝ} :
    Integrable (fun x => (∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)).toReal) μ := by
  classical
  have h_aemeas :
      AEMeasurable (fun x => ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x)) μ :=
    aemeasurable_lintegral_ofReal_simpleFunc (μ := μ) (π := π) h𝓑𝓧 (φ := φ)
  have hκ : AEMeasurable (fun x => π x) μ :=
    (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable
  have h_le :
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x) ∂μ)
        ≤ ∫⁻ x, ∫⁻ y, ‖φ y‖ₑ ∂(π x) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [] with x
    exact lintegral_ofReal_le_lintegral_enorm ⇑φ
  have h_eq :
      (∫⁻ x, ∫⁻ y, ‖φ y‖ₑ ∂(π x) ∂μ)
        = ∫⁻ y, ‖φ y‖ₑ ∂(μ.bind π) := by
    rw [Measure.lintegral_bind hκ (SimpleFunc.measurable φ).enorm.aemeasurable]
  have h_fin :
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x) ∂μ) < ∞ := by
    haveI : IsFiniteMeasure (μ.bind π) :=
      isFiniteMeasure_bind (μ := μ) (π := π) h𝓑𝓧
    have h_intφ : Integrable φ (μ.bind π) := SimpleFunc.integrable_of_isFiniteMeasure φ
    have h_enorm :
        (∫⁻ y, ‖φ y‖ₑ ∂(μ.bind π)) < ∞ := h_intφ.2
    exact lt_of_le_of_lt h_le (by simpa [h_eq] using h_enorm)
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · exact h_aemeas
  · exact (lt_of_le_of_lt le_rfl h_fin).ne

/-- Fubini for the bind of a restricted measure and a kernel: simple functions. -/
private lemma integral_bind_kernel_restrict_simple
    [IsFiniteMeasure μ] [IsMarkovKernel π]
    (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    {s : Set X} {φ : @SimpleFunc X 𝓧 ℝ} :
    ∫ y, (φ y) ∂(((μ.restrict s).bind π))
      = ∫ x in s, ∫ y, (φ y) ∂(π x) ∂ μ := by
  have hκ : AEMeasurable (fun x => π x) (μ.restrict s) :=
    (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable.restrict
  haveI : IsFiniteMeasure (((μ.restrict s).bind π)) :=
    isFiniteMeasure_bind_restrict (μ := μ) (π := π) h𝓑𝓧 s
  have hφ_int : Integrable (fun y => φ y) (((μ.restrict s).bind π)) :=
    SimpleFunc.integrable_of_isFiniteMeasure φ
  have pos_eq : ∫⁻ y, ENNReal.ofReal (φ y) ∂(((μ.restrict s).bind π))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x) ∂(μ.restrict s) := by
    refine Measure.lintegral_bind ?_ ?_
    · exact hκ
    · exact (Measurable.ennreal_ofReal (SimpleFunc.measurable φ)).aemeasurable
  have neg_eq : ∫⁻ y, ENNReal.ofReal (- φ y) ∂(((μ.restrict s).bind π))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (- φ y) ∂(π x) ∂(μ.restrict s) := by
    refine Measure.lintegral_bind ?_ ?_
    · exact hκ
    · exact (Measurable.ennreal_ofReal (SimpleFunc.measurable φ).neg).aemeasurable
  have pos_eq' := congrArg ENNReal.toReal pos_eq
  have neg_eq' := congrArg ENNReal.toReal neg_eq
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ_int, pos_eq', neg_eq']
  rw [lintegral_ofReal_toReal_eq_setIntegral μ π h𝓑𝓧 (s := s) (φ := φ)]
  have neg_rw : (∫⁻ (x : X) in s, ∫⁻ (y : X), ENNReal.ofReal (-φ y) ∂π x ∂μ).toReal =
      ∫ (x : X) in s, (∫⁻ (y : X), ENNReal.ofReal (-φ y) ∂π x).toReal ∂μ := by
    simpa using lintegral_ofReal_toReal_eq_setIntegral μ π h𝓑𝓧 (s := s) (φ := -φ)
  rw [neg_rw]
  rw [← MeasureTheory.integral_sub]
  · congr 1
    ext x
    exact toReal_sub_toReal_eq_integral_simpleFunc π x
  · exact (integrable_toReal_lintegral_ofReal_simpleFunc μ π h𝓑𝓧 (φ := φ)).integrableOn
  · exact (integrable_toReal_lintegral_ofReal_simpleFunc μ π h𝓑𝓧 (φ := -φ)).integrableOn

private lemma norm_approxOn_le_norm
    {f : X → ℝ} (hf : Measurable f) (x : X) (n : ℕ) :
    ‖SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n x‖ ≤ ‖f x‖ + ‖f x‖ := by
  have h0 : (0 : ℝ) ∈ range f ∪ {0} := by simp
  have hmem : f x ∈ range f ∪ {0} := Or.inl ⟨x, rfl⟩
  exact SimpleFunc.norm_approxOn_zero_le hf h0 x n

/-- Pointwise a.e. convergence of inner kernel integrals for simple function approximations. -/
private lemma tendsto_integral_approxOn_ae
    [IsMarkovKernel π] {f : X → ℝ} (hf : Measurable f) (x : X)
    (h_int : Integrable f (π x)) :
    Tendsto (fun n => ∫ y, SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n y ∂(π x))
      atTop (𝓝 (∫ y, f y ∂(π x))) := by
  have h_conv : ∀ᵐ y ∂(π x), Tendsto
      (fun n => SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n y) atTop (𝓝 (f y)) :=
    SimpleFunc.tendsto_approxOn_range_ae hf
  have h_int_φ : ∀ n,
      Integrable (SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n) (π x) := by
    intro n; exact SimpleFunc.integrable_of_isFiniteMeasure _
  have h_bound : ∀ n, ∀ᵐ y ∂(π x),
      ‖SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n y‖ ≤ ‖f y‖ + ‖f y‖ := by
    intro n; filter_upwards with y
    exact norm_approxOn_le_norm hf y n
  have h_dom : Integrable (fun y => ‖f y‖ + ‖f y‖) (π x) := h_int.norm.add h_int.norm
  exact tendsto_integral_of_dominated_convergence (fun y => ‖f y‖ + ‖f y‖)
    (fun n => (h_int_φ n).aestronglyMeasurable) h_dom h_bound h_conv

/-- Integrability of the kernel integral for an integrable function on the bind measure. -/
private lemma integrable_integral_of_integrable_bind
    [IsFiniteMeasure μ] [IsMarkovKernel π] (h𝓑𝓧 : 𝓑 ≤ 𝓧) {s : Set X} {f : X → ℝ}
    (hf_meas : Measurable f) (hf_int : Integrable f ((μ.restrict s).bind π)) :
    Integrable (fun x => ∫ y, f y ∂(π x)) (μ.restrict s) := by
  have hκ : AEMeasurable (fun x => π x) (μ.restrict s) :=
    (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable.restrict
  have h_lintegral_eq :
      ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(π x) ∂(μ.restrict s) = ∫⁻ y, ‖f y‖ₑ ∂((μ.restrict s).bind π) := by
    rw [Measure.lintegral_bind hκ hf_meas.enorm.aemeasurable]
  refine integrable_of_lintegral_ennnorm_lt_top ?_ ?_
  · exact (((hf_meas.stronglyMeasurable.integral_kernel
      (κ := π)).mono h𝓑𝓧).aestronglyMeasurable).restrict
  · have hfin : ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(π x) ∂(μ.restrict s) < ∞ := by
      rw [h_lintegral_eq]; exact hf_int.2
    have hpt :
        ∀ᵐ x ∂(μ.restrict s),
          ‖∫ y, f y ∂(π x)‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ ∂(π x) := by
      filter_upwards with x
      exact enorm_integral_le_lintegral_enorm (f := f) (μ := π x)
    calc
      ∫⁻ x, ‖∫ y, f y ∂(π x)‖ₑ ∂(μ.restrict s)
          ≤ ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(π x) ∂(μ.restrict s) := by
                exact lintegral_mono_ae hpt
      _ < ∞ := hfin

/-- Dominated convergence for nested integrals with simple function approximations. -/
private lemma tendsto_setIntegral_integral_approxOn
    [IsFiniteMeasure μ] [IsMarkovKernel π] (h𝓑𝓧 : 𝓑 ≤ 𝓧) {s : Set X} {f : X → ℝ}
    (hf : Measurable f) (hf_int : Integrable f ((μ.restrict s).bind π)) :
    Tendsto (fun n => ∫ x in s, ∫ y,
      SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n y ∂(π x) ∂μ) atTop
      (𝓝 (∫ x in s, ∫ y, f y ∂(π x) ∂μ)) := by
  classical
  set φ := fun n => SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n
  have hκ : AEMeasurable (fun x => π x) (μ.restrict s) :=
    (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable.restrict
  have h_int_ae : ∀ᵐ x ∂(μ.restrict s), Integrable f (π x) := by
    have h_lintegral : ∫⁻ x in s, ∫⁻ y, ‖f y‖ₑ ∂(π x) ∂μ < ∞ := by
      have h_eq :
          (∫⁻ x in s, ∫⁻ y, ‖f y‖ₑ ∂(π x) ∂μ)
            = ∫⁻ y, ‖f y‖ₑ ∂((μ.restrict s).bind π) := by
        rw [Measure.lintegral_bind hκ hf.enorm.aemeasurable]
      rw [h_eq]
      exact hasFiniteIntegral_iff_enorm.mp hf_int.hasFiniteIntegral
    haveI : IsSFiniteKernel π := inferInstance
    have hf_enorm : Measurable fun y : X => ‖f y‖ₑ := hf.enorm
    have h_meas : Measurable (fun x => ∫⁻ y, ‖f y‖ₑ ∂(π x)) :=
      ((Measurable.lintegral_kernel (κ := π) (f := fun y => ‖f y‖ₑ) hf_enorm).mono h𝓑𝓧 le_rfl)
    have h_fin_ae :
        ∀ᵐ x ∂(μ.restrict s), (∫⁻ y, ‖f y‖ₑ ∂(π x)) < ∞ :=
      ae_lt_top (μ := μ.restrict s) h_meas h_lintegral.ne
    exact h_fin_ae.mono
      (fun x hx => integrable_of_lintegral_ennnorm_lt_top hf.aestronglyMeasurable hx)
  have h_conv : ∀ᵐ x ∂(μ.restrict s),
      Tendsto (fun n => ∫ y, φ n y ∂(π x)) atTop (𝓝 (∫ y, f y ∂(π x))) :=
    h_int_ae.mono (fun x hx => tendsto_integral_approxOn_ae (π := π) hf x hx)
  have h_int_φ : ∀ n, Integrable (fun x => ∫ y, φ n y ∂(π x)) (μ.restrict s) := by
    intro n
    refine integrable_integral_of_integrable_bind (μ := μ) (π := π) h𝓑𝓧
      (s := s) (f := φ n) (hf_meas := (SimpleFunc.measurable _)) ?_
    haveI : IsFiniteMeasure (((μ.restrict s).bind π)) :=
      isFiniteMeasure_bind_restrict (μ := μ) (π := π) h𝓑𝓧 s
    exact SimpleFunc.integrable_of_isFiniteMeasure _
  have h_bound : ∀ n, ∀ᵐ x ∂(μ.restrict s),
      ‖∫ y, φ n y ∂(π x)‖ ≤ ∫ y, ‖f y‖ + ‖f y‖ ∂(π x) := by
    intro n
    have h_int_norm_ae :
        ∀ᵐ x ∂(μ.restrict s), Integrable (fun y => ‖f y‖) (π x) :=
      h_int_ae.mono (fun x hx => hx.norm)
    refine h_int_norm_ae.mono ?_
    intro x hx_int
    have h1 : ‖∫ y, φ n y ∂(π x)‖ ≤ ∫ y, ‖φ n y‖ ∂(π x) :=
      MeasureTheory.norm_integral_le_integral_norm _
    have h2 : ∫ y, ‖φ n y‖ ∂(π x) ≤ ∫ y, ‖f y‖ + ‖f y‖ ∂(π x) := by
      refine MeasureTheory.integral_mono
        ((SimpleFunc.integrable_of_isFiniteMeasure _).norm)
        (hx_int.add hx_int)
        (by
          intro y
          exact norm_approxOn_le_norm hf y n)
    exact h1.trans h2
  have h_dom : Integrable (fun x => ∫ y, ‖f y‖ + ‖f y‖ ∂(π x)) (μ.restrict s) := by
    have h_norm_int : Integrable (fun y => ‖f y‖) ((μ.restrict s).bind π) := hf_int.norm
    exact integrable_integral_of_integrable_bind (μ := μ) (π := π) h𝓑𝓧
      (s := s) (f := fun y => ‖f y‖ + ‖f y‖)
      (hf_meas := (Measurable.add hf.norm hf.norm))
      (hf_int := h_norm_int.add h_norm_int)
  exact
    tendsto_integral_of_dominated_convergence
      (fun x => ∫ y, ‖f y‖ + ‖f y‖ ∂(π x))
      (fun n => (h_int_φ n).aestronglyMeasurable)
      h_dom h_bound h_conv

/-- Fubini for the bind of a restricted measure and a kernel: integrable functions. -/
private lemma integral_bind_kernel_restrict
    [IsFiniteMeasure μ] [IsMarkovKernel π]
    (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    {s : Set X} {f : X → ℝ}
    (hf_int : Integrable f (((μ.restrict s).bind π))) :
    ∫ y, f y ∂(((μ.restrict s).bind π))
      = ∫ x in s, ∫ y, f y ∂(π x) ∂ μ := by
  haveI : IsFiniteMeasure (((μ.restrict s).bind π)) :=
    isFiniteMeasure_bind_restrict (μ := μ) (π := π) h𝓑𝓧 s
  let f₀ := hf_int.aestronglyMeasurable.mk f
  have hf₀_meas : Measurable f₀ := hf_int.aestronglyMeasurable.measurable_mk
  have hf_eq_f₀ : f =ᵐ[((μ.restrict s).bind π)] f₀ := hf_int.aestronglyMeasurable.ae_eq_mk
  set φ_seq := fun n => SimpleFunc.approxOn f₀ hf₀_meas (range f₀ ∪ {0}) 0 (by simp) n
  have h_simple : ∀ n, ∫ y, φ_seq n y ∂(((μ.restrict s).bind π))
      = ∫ x in s, ∫ y, φ_seq n y ∂(π x) ∂μ := by
    intro n
    exact integral_bind_kernel_restrict_simple μ π h𝓑𝓧
  have h_tendsto : ∀ᵐ y ∂(((μ.restrict s).bind π)),
      Tendsto (fun n => φ_seq n y) atTop (𝓝 (f₀ y)) :=
    SimpleFunc.tendsto_approxOn_range_ae hf₀_meas
  have h_int_φ : ∀ n, Integrable (φ_seq n) (((μ.restrict s).bind π)) := by
    intro n; exact SimpleFunc.integrable_of_isFiniteMeasure _
  have h_bound : ∀ n, ∀ᵐ y ∂(((μ.restrict s).bind π)), ‖φ_seq n y‖ ≤ ‖f₀ y‖ + ‖f₀ y‖ := by
    intro n; filter_upwards with y; exact norm_approxOn_le_norm hf₀_meas y n
  have h_dom_int : Integrable (fun y => ‖f₀ y‖ + ‖f₀ y‖) (((μ.restrict s).bind π)) := by
    have : Integrable (fun y => ‖f₀ y‖) (((μ.restrict s).bind π)) :=
      (hf_int.congr hf_eq_f₀).norm
    exact this.add this
  have h_lhs : Tendsto (fun n => ∫ y, φ_seq n y ∂(((μ.restrict s).bind π))) atTop
      (𝓝 (∫ y, f₀ y ∂(((μ.restrict s).bind π)))) :=
    tendsto_integral_of_dominated_convergence
      (fun y => ‖f₀ y‖ + ‖f₀ y‖)
      (fun n => (h_int_φ n).aestronglyMeasurable)
      h_dom_int h_bound h_tendsto
  have h_rhs : Tendsto (fun n => ∫ x in s, ∫ y, φ_seq n y ∂(π x) ∂μ) atTop
      (𝓝 (∫ x in s, ∫ y, f₀ y ∂(π x) ∂μ)) :=
    tendsto_setIntegral_integral_approxOn (μ := μ) (π := π) h𝓑𝓧
      (s := s) (f := f₀) hf₀_meas (hf_int.congr hf_eq_f₀)
  have h_eq_limit : ∫ y, f₀ y ∂((μ.restrict s).bind π) = ∫ x in s, ∫ y, f₀ y ∂(π x) ∂μ := by
    have : (fun n => ∫ y, φ_seq n y ∂((μ.restrict s).bind π))
        = (fun n => ∫ x in s, ∫ y, φ_seq n y ∂(π x) ∂μ) := funext h_simple
    rw [this] at h_lhs
    exact tendsto_nhds_unique h_lhs h_rhs
  calc ∫ y, f y ∂((μ.restrict s).bind π)
      = ∫ y, f₀ y ∂((μ.restrict s).bind π) := integral_congr_ae hf_eq_f₀
    _ = ∫ x in s, ∫ y, f₀ y ∂(π x) ∂μ := h_eq_limit
    _ = ∫ x in s, ∫ y, f y ∂(π x) ∂μ := by
        have h_ae : ∀ᵐ x ∂(μ.restrict s), f =ᵐ[π x] f₀ :=
          Measure.ae_ae_of_ae_bind
            (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable.restrict hf_eq_f₀
        refine integral_congr_ae ?_
        filter_upwards [h_ae] with x hx
        exact integral_congr_ae hx.symm

/-- General version with explicit integrability and measurability hypotheses for the kernel
integral. -/
lemma condExp_ae_eq_integral_kernel
    [π.IsCondExp μ] [IsFiniteMeasure μ] [IsFiniteKernel π]
    (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f : X → ℝ) -- (hf_meas : Measurable[𝓧] f)
    (hf_int : Integrable f μ)
    (hg_int : Integrable (fun x₀ ↦ ∫ x, f x ∂(π x₀)) μ)
    (hg_aesm : AEStronglyMeasurable[𝓑] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) μ)
    [IsMarkovKernel π]
    [SigmaFinite (μ.trim h𝓑𝓧)] :
    condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  let g := fun x₀ ↦ ∫ x, f x ∂(π x₀)
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝓑𝓧 hf_int ?_ ?_ hg_aesm).symm
  · intro s _ _
    exact hg_int.integrableOn
  · intro s hs _
    have h_iff_A
        (A : Set X) (hA : MeasurableSet[𝓧] A) :
        (μ[A.indicator 1|𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal) ↔
          (∀ t, MeasurableSet[𝓑] t → μ (A ∩ t) = ∫⁻ a in t, π a A ∂μ) := by
      have hgm : AEStronglyMeasurable[𝓑] (fun a ↦ π a A) μ :=
        (Kernel.measurable_coe π hA).aestronglyMeasurable
      have hg_fin : ∀ᵐ a ∂ μ, π a A ≠ ⊤ := by
        filter_upwards with a
        exact measure_ne_top (π a) A
      simpa [Filter.eventuallyEq_comm] using
        (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq
          (m := 𝓑) (m0 := 𝓧) (μ := μ)
          h𝓑𝓧 hA (measure_ne_top μ A) hgm hg_fin)
    have h_bind_restrict :
        ((μ.restrict s).bind π) = μ.restrict s := by
      ext A hA
      have hκ : AEMeasurable (fun x => π x) (μ.restrict s) :=
        (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable.restrict
      have hforall := (h_iff_A A hA).mp
        (IsCondExp.condExp_ae_eq_kernel_apply (π := π) (μ := μ) hA)
      have hAs : μ (A ∩ s) = ∫⁻ a in s, π a A ∂μ := hforall s hs
      calc
        ((μ.restrict s).bind π) A
            = ∫⁻ a, π a A ∂(μ.restrict s) := by
              simp [Measure.bind_apply hA hκ]
        _ = ∫⁻ a in s, π a A ∂μ := by
              simp
        _ = μ (A ∩ s) := by
              simpa using hAs.symm
        _ = (μ.restrict s) A := by
              simp [Measure.restrict_apply, hA]
    have hf_int_restrict_bind : Integrable f (((μ.restrict s).bind π)) := by
      simpa [h_bind_restrict] using hf_int.restrict
    simpa [h_bind_restrict, lintegral_restrict] using
      (integral_bind_kernel_restrict (μ := μ) (π := π) h𝓑𝓧 (s := s) (f := f)
        (hf_int := hf_int_restrict_bind)).symm

end LocalFubini
end ProbabilityTheory.Kernel
