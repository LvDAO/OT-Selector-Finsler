import OTSelector.Reconstruction.OriginalCountingActualNodes
import OTSelector.Topology.MetricSpace.CanonicalMcShaneExtension
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftMatching

/-! A canonical jointly Borel rough-momentum extension of actual occupied nodes. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false

variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [PseudoMetricSpace Y]

/-- Literal infimum over the original actual atom code. Missing code slots
repeat one real occupied atom; an empty original measure gives the zero field. -/
def originalCountingRoughField (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ℝ)
    (μ : LocalFiniteMeasure X) (x : Y) : ℝ :=
  if μ ∈ originalCountingSupportActive base then
    roughMcShane L (z ∘ originalCountingCompletedAtom base μ)
      (p ∘ originalCountingCompletedAtom base μ) x
  else 0

/-- The actual field is Borel jointly in the original whole measure and
the physical observation position. -/
theorem measurable_originalCountingRoughField
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ℝ)
    (hz : Measurable z) (hp : Measurable p) :
    Measurable (fun a : LocalFiniteMeasure X × Y ↦
      originalCountingRoughField base L z p a.1 a.2) := by
  apply Measurable.ite ((measurableSet_originalCountingSupportActive base).preimage measurable_fst)
  · exact measurable_roughMcShane L
      (fun n μ ↦ z (originalCountingCompletedAtom base μ n))
      (fun n μ ↦ p (originalCountingCompletedAtom base μ n))
      (fun n ↦ hz.comp (measurable_originalCountingCompletedAtom base n))
      (fun n ↦ hp.comp (measurable_originalCountingCompletedAtom base n))
  · exact measurable_const

/-- The literal actual-node field is genuinely Lipschitz whenever its actual
occupied position/momentum pairs satisfy the produced rough estimate. -/
theorem lipschitzWith_originalCountingRoughField
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ℝ) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) {b : ℝ}
    (hrough : ∀ e ∈ (μ : Measure X).support, ∀ f ∈ (μ : Measure X).support,
      p e ≤ p f + L * dist (z e) (z f) + b) :
    LipschitzWith L (originalCountingRoughField base L z p μ) := by
  by_cases ha : μ ∈ originalCountingSupportActive base
  · have heq : originalCountingRoughField base L z p μ =
        roughMcShane L (z ∘ originalCountingCompletedAtom base μ)
          (p ∘ originalCountingCompletedAtom base μ) := by
      funext x
      exact ite_eq_left ha
    rw [heq]
    apply lipschitzWith_roughMcShane
    intro i j
    exact hrough _ (originalCountingCompletedAtom_mem_support base μ hμ ha i)
      _ (originalCountingCompletedAtom_mem_support base μ hμ ha j)
  · have heq : originalCountingRoughField base L z p μ = fun _ ↦ 0 := by
      funext x
      exact ite_eq_right ha
    rw [heq]
    apply LipschitzWith.of_le_add_mul L
    intro x y
    exact le_add_of_nonneg_right (mul_nonneg L.coe_nonneg dist_nonneg)

/-- At every actual occupied node the field has the original one-sided
rough error, with no condition on absent code positions. -/
theorem originalCountingRoughField_node_bounds
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ℝ) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) {b : ℝ}
    (hrough : ∀ e ∈ (μ : Measure X).support, ∀ f ∈ (μ : Measure X).support,
      p e ≤ p f + L * dist (z e) (z f) + b)
    {e : X} (he : e ∈ (μ : Measure X).support) :
    p e - b ≤ originalCountingRoughField base L z p μ (z e) ∧
      originalCountingRoughField base L z p μ (z e) ≤ p e := by
  have ha := (originalCountingSupportActive_iff base μ hμ).mpr ⟨e, he⟩
  obtain ⟨n, hn⟩ := exists_originalCountingAtom base μ hμ he
  have heq := originalCountingCompletedAtom_eq_of_some base μ hn
  have hr (i j : ℕ) : p (originalCountingCompletedAtom base μ i) ≤
      p (originalCountingCompletedAtom base μ j) +
        L * dist (z (originalCountingCompletedAtom base μ i))
          (z (originalCountingCompletedAtom base μ j)) + b :=
    hrough _ (originalCountingCompletedAtom_mem_support base μ hμ ha i)
      _ (originalCountingCompletedAtom_mem_support base μ hμ ha j)
  have h := roughMcShane_node_bounds L (z ∘ originalCountingCompletedAtom base μ)
    (p ∘ originalCountingCompletedAtom base μ) hr n
  simpa only [originalCountingRoughField, ite_eq_left ha, Function.comp_apply, heq] using h

/-- The field depends only on actual occupied position/momentum pairs.
Different original integer codes and their duplicate padding give the same field. -/
theorem originalCountingRoughField_eq_of_pairImage_eq
    (base base' : X) (L : ℝ≥0) (z z' : X → Y) (p p' : X → ℝ)
    (μ ν : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ)
    (hν : IsLegalCountingMeasure base' ν)
    (hpair : (fun e ↦ (z e, p e)) '' (μ : Measure X).support =
      (fun e ↦ (z' e, p' e)) '' (ν : Measure X).support) :
    originalCountingRoughField base L z p μ = originalCountingRoughField base' L z' p' ν := by
  have hactive : μ ∈ originalCountingSupportActive base ↔
      ν ∈ originalCountingSupportActive base' := by
    rw [originalCountingSupportActive_iff base μ hμ, originalCountingSupportActive_iff base' ν hν]
    constructor
    · rintro ⟨e, he⟩
      have hmem : (z e, p e) ∈ (fun a ↦ (z a, p a)) '' (μ : Measure X).support := ⟨e, he, rfl⟩
      rw [hpair] at hmem
      obtain ⟨f, hf, _⟩ := hmem
      exact ⟨f, hf⟩
    · rintro ⟨f, hf⟩
      have hmem : (z' f, p' f) ∈ (fun a ↦ (z' a, p' a)) '' (ν : Measure X).support := ⟨f, hf, rfl⟩
      rw [← hpair] at hmem
      obtain ⟨e, he, _⟩ := hmem
      exact ⟨e, he⟩
  by_cases ha : μ ∈ originalCountingSupportActive base
  · have hb := hactive.mp ha
    have hr : Set.range (fun n ↦ (z (originalCountingCompletedAtom base μ n),
        p (originalCountingCompletedAtom base μ n))) =
        Set.range (fun n ↦ (z' (originalCountingCompletedAtom base' ν n),
          p' (originalCountingCompletedAtom base' ν n))) := by
      have hr := hpair
      rw [← range_originalCountingCompletedAtom base μ hμ ha,
        ← range_originalCountingCompletedAtom base' ν hν hb] at hr
      simpa only [← range_comp, Function.comp_def] using hr
    funext x
    simp only [originalCountingRoughField, ite_eq_left ha, ite_eq_left hb]
    exact congrFun (roughMcShane_eq_of_range_eq L
      (z ∘ originalCountingCompletedAtom base μ) (p ∘ originalCountingCompletedAtom base μ)
      (z' ∘ originalCountingCompletedAtom base' ν) (p' ∘ originalCountingCompletedAtom base' ν) hr) x
  · have hb := hactive.not.mp ha
    funext x
    simp only [originalCountingRoughField, ite_eq_right ha, ite_eq_right hb]

/-- Literal field covariance under every spatial isometry, including the
empty-measure case. -/
theorem originalCountingRoughField_isometry
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ℝ) (μ : LocalFiniteMeasure X)
    (R : Y → Y) (hR : Isometry R) (x : Y) :
    originalCountingRoughField base L (R ∘ z) p μ (R x) =
      originalCountingRoughField base L z p μ x := by
  by_cases ha : μ ∈ originalCountingSupportActive base
  · simp only [originalCountingRoughField, ite_eq_left ha]
    exact roughMcShane_isometry R hR L
      (z ∘ originalCountingCompletedAtom base μ) (p ∘ originalCountingCompletedAtom base μ) x
  · simp only [originalCountingRoughField, ite_eq_right ha]

/-- Transporting the actual original occupied measure and its physical
nodes transports the canonical field, independently of atom-code changes. -/
theorem originalCountingRoughField_mapHomeomorph
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ℝ) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (T : X ≃ₜ X) (R : Y → Y) (hR : Isometry R)
    (hz : ∀ a, z (T a) = R (z a)) (hp : ∀ a, p (T a) = p a) (x : Y) :
    originalCountingRoughField base L z p (localFiniteMapHomeomorph T μ) (R x) =
      originalCountingRoughField base L z p μ x := by
  let ν := localFiniteMapHomeomorph T μ
  have hν := isLegalCountingMeasure_mapHomeomorph base T μ hμ
  have hsupp : (ν : Measure X).support = T '' (μ : Measure X).support := by
    ext a
    rw [mem_support_mapHomeomorph_iff_of_legalCounting base T μ hμ a]
    constructor
    · intro ha
      exact ⟨T.symm a, ha, T.apply_symm_apply a⟩
    · rintro ⟨d, hd, rfl⟩
      simpa only [T.symm_apply_apply] using hd
  have hpair : (fun a ↦ (z a, p a)) '' (ν : Measure X).support =
      (fun a ↦ ((R ∘ z) a, p a)) '' (μ : Measure X).support := by
    rw [hsupp, Set.image_image]
    congr 1
    funext a
    exact Prod.ext (hz a) (hp a)
  rw [congrFun (originalCountingRoughField_eq_of_pairImage_eq base base L z (R ∘ z)
    p p ν μ hν hμ hpair) (R x)]
  exact originalCountingRoughField_isometry base L z p μ R hR x

end OTSelector.Reconstruction
