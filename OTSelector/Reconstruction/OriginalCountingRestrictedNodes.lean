import OTSelector.Reconstruction.OriginalCountingRoughField

/-! Restricting the original integer code to actual eligible geometric edges. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- The actual original occupied-edge measure restricted to a geometric eligibility set. -/
def originalCountingNodeRestriction (K : Set X) (μ : LocalFiniteMeasure X) :
    LocalFiniteMeasure X := ⟨(μ : Measure X).restrict K, inferInstance⟩

theorem measurable_originalCountingNodeRestriction {K : Set X} (hK : MeasurableSet K) :
    Measurable (originalCountingNodeRestriction K) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  apply Measure.measurable_of_measurable_coe
  intro A hA
  change Measurable (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict K A)
  simp only [Measure.restrict_apply hA]
  exact (Measure.measurable_coe (hA.inter hK)).comp measurable_localFiniteMeasure_coe

theorem isLegalCountingMeasure_originalCountingNodeRestriction
    (base : X) (μ : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ) (K : Set X) :
    IsLegalCountingMeasure base (originalCountingNodeRestriction K μ) :=
  isLegalCountingMeasure_restrict base μ hμ K

/-- Restriction has no spurious boundary support nodes: integer local
finiteness retains exactly the original atoms satisfying the eligibility rule. -/
theorem mem_support_originalCountingNodeRestriction_iff
    (base : X) (μ : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ)
    (K : Set X) (x : X) :
    x ∈ (originalCountingNodeRestriction K μ : Measure X).support ↔
      x ∈ (μ : Measure X).support ∧ x ∈ K := by
  have hcount := isLegalCountingMeasure_originalCountingNodeRestriction base μ hμ K
  constructor
  · intro hx
    refine ⟨Measure.support_mono Measure.restrict_le_self hx, ?_⟩
    by_contra hnot
    have hone := one_le_singleton_of_mem_support_of_legalCounting base
      (originalCountingNodeRestriction K μ) hcount hx
    change 1 ≤ (μ : Measure X).restrict K {x} at hone
    rw [Measure.restrict_apply (measurableSet_singleton x),
      Set.singleton_inter_of_notMem hnot, measure_empty] at hone
    exact not_le_of_gt zero_lt_one hone
  · rintro ⟨hx, hK⟩
    have hone := one_le_singleton_of_mem_support_of_legalCounting base μ hμ hx
    have hmass : 0 < (originalCountingNodeRestriction K μ : Measure X) {x} := by
      change 0 < (μ : Measure X).restrict K {x}
      rw [Measure.restrict_apply (measurableSet_singleton x), Set.singleton_inter_of_mem hK]
      exact zero_lt_one.trans_le hone
    apply (Measure.mem_support_iff_forall x).mpr
    intro U hU
    exact hmass.trans_le (measure_mono (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- Eligibility preserved by a physical translation commutes with the
literal restriction of the same original measure. -/
theorem originalCountingNodeRestriction_mapHomeomorph
    (K : Set X) (hK : MeasurableSet K) (T : X ≃ₜ X)
    (hT : ∀ x, T x ∈ K ↔ x ∈ K) (μ : LocalFiniteMeasure X) :
    originalCountingNodeRestriction K (localFiniteMapHomeomorph T μ) =
      localFiniteMapHomeomorph T (originalCountingNodeRestriction K μ) := by
  apply Subtype.ext
  change ((μ : Measure X).map T).restrict K = ((μ : Measure X).restrict K).map T
  rw [Measure.restrict_map T.measurable hK]
  have heq : T ⁻¹' K = K := Set.ext hT
  rw [heq]

end OTSelector.Reconstruction
