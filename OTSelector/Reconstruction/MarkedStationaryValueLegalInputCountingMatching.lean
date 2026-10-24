import OTSelector.Reconstruction.MarkedStationaryValueLegalInputSimpleScene
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputColorMarginals

/-!
# Unit input atoms force actual one-to-one matching edges

Integer edge atoms and the whole same-input marginal equalities prevent both
multiple edges at a point and duplicated partners. Every occupied input atom
has its unique original edge. The argument uses singleton masses and full
marginals, so no proper projection hypothesis enters.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

section Counting
variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- An occupied point of an actual integer measure has at least unit mass. -/
theorem one_le_singleton_of_mem_support_of_legalCounting (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) {x : X} (hx : x ∈ (μ : Measure X).support) :
    1 ≤ (μ : Measure X) {x} := by
  obtain ⟨c, rfl⟩ := hμ
  change x ∈ (LocalConfiguration.countingMeasure c).support at hx
  rw [LocalConfiguration.support_countingMeasure] at hx
  change LocalConfiguration.multiplicity c x ≠ 0 at hx
  change 1 ≤ LocalConfiguration.countingMeasure c {x}
  rw [LocalConfiguration.countingMeasure_singleton]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx

/-- A projected unit atom cannot receive two distinct original integer edges. -/
theorem injOn_support_of_legalCounting_of_map_singleton_le_one
    (base : X) (μ : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ)
    (f : X → Y) (hf : Measurable f)
    (hunit : ∀ y, (μ : Measure X).map f {y} ≤ 1) :
    Set.InjOn f (μ : Measure X).support := by
  intro x hx y hy hxy
  by_contra hne
  have hx1 := one_le_singleton_of_mem_support_of_legalCounting base μ hμ hx
  have hy1 := one_le_singleton_of_mem_support_of_legalCounting base μ hμ hy
  have hpair : (μ : Measure X) {x} + (μ : Measure X) {y} ≤ (μ : Measure X).map f {f x} := by
    rw [← measure_union (disjoint_singleton.mpr hne) (measurableSet_singleton y),
      Measure.map_apply hf (measurableSet_singleton (f x))]
    apply measure_mono
    intro z hz
    rcases hz with hz | hz
    · simp only [mem_preimage, mem_singleton_iff, mem_singleton_iff.mp hz]
    · simpa only [mem_preimage, mem_singleton_iff, mem_singleton_iff.mp hz] using hxy.symm
  have hbad : (2 : ℝ≥0∞) ≤ 1 := by
    calc
      2 = 1 + 1 := by norm_num
      _ ≤ (μ : Measure X) {x} + (μ : Measure X) {y} := add_le_add hx1 hy1
      _ ≤ 1 := hpair.trans (hunit (f x))
  norm_num at hbad

/-- Every occupied projected input atom has exactly one actual edge above it.
Nonproper projections cause no loss because the whole marginal is retained. -/
theorem existsUnique_support_preimage_of_legalCounting_of_map_singleton_le_one
    (base : X) (μ : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ)
    (f : X → Y) (hf : Measurable f)
    (hunit : ∀ y, (μ : Measure X).map f {y} ≤ 1)
    (y : Y) (hy : (μ : Measure X).map f {y} ≠ 0) :
    ∃! x, x ∈ (μ : Measure X).support ∧ f x = y := by
  have hinj := injOn_support_of_legalCounting_of_map_singleton_le_one base μ hμ f hf hunit
  have hex : ∃ x ∈ (μ : Measure X).support, f x = y := by
    by_contra! hnone
    have hz : (μ : Measure X) (f ⁻¹' {y}) = 0 :=
      measure_mono_null (fun x hx hs ↦ hnone x hs (mem_singleton_iff.mp hx))
        (Measure.measure_compl_support (μ := (μ : Measure X)))
    exact hy (by rwa [Measure.map_apply hf (measurableSet_singleton y)])
  obtain ⟨x, hx, hxy⟩ := hex
  refine ⟨x, ⟨hx, hxy⟩, fun z hz ↦ ?_⟩
  exact hinj hz.1 hx (hz.2.trans hxy.symm)
end Counting

/-- An unchanged color is exactly the original atom with that immutable tag. -/
theorem legalInputColorMeasure_singleton (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2)
    (x : LegalMarkedPhysicalPoint q) :
    legalInputColorMeasure q μ c {x} = (μ : Measure (LegalColoredInputPoint q)) {(x, c)} := by
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst (measurableSet_singleton x),
    Measure.restrict_apply (measurable_fst (measurableSet_singleton x))]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  constructor
  · intro h
    exact Prod.ext h.1 h.2
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

local instance markedStationaryValueLegalInputCountingMatchingColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance markedStationaryValueLegalInputCountingMatchingInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputCountingMatchingPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A genuine one-to-one integer matching of every original input atom,
including the whole same-input marginal equalities. -/
structure IsFullOriginalInputMatching (q : ℕ) (s : LegalMarkedOptimalInputScene q) : Prop where
  simple_edges : IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1
  simple_inputs : IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) s.2
  source_marginal : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0
  target_marginal : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1
  source_injective : Set.InjOn Prod.fst (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support
  target_injective : Set.InjOn Prod.snd (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support
  source_occupied : ∀ x, (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0 →
    ∃! e, e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support ∧ e.1 = x
  target_occupied : ∀ y, (s.2 : Measure (LegalColoredInputPoint q)) {(y, 1)} ≠ 0 →
    ∃! e, e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support ∧ e.2 = y

/-- Integer edges with the exact simple input marginals automatically form
an actual one-to-one full matching, even for nonproper endpoint projections. -/
theorem isFullOriginalInputMatching_of_counting_simple_marginals
    (q : ℕ) (s : LegalMarkedOptimalInputScene q)
    (hc : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1)
    (hs : IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) s.2)
    (hm : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 ∧
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1) :
    IsFullOriginalInputMatching q s := by
  have hsunit := ((isLegalSimpleCountingMeasure_iff _ _).mp hs).2
  have hr (x : LegalMarkedPhysicalPoint q) :
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map Prod.fst {x} ≤ 1 := by
    change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst {x} ≤ 1
    rw [hm.1, legalInputColorMeasure_singleton]
    exact hsunit (x, 0)
  have ht (y : LegalMarkedPhysicalPoint q) :
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map Prod.snd {y} ≤ 1 := by
    change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd {y} ≤ 1
    rw [hm.2, legalInputColorMeasure_singleton]
    exact hsunit (y, 1)
  have he : IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1 := by
    apply (isLegalSimpleCountingMeasure_iff _ _).mpr
    refine ⟨hc, fun e ↦ ?_⟩
    apply le_trans ?_ (hr e.1)
    rw [Measure.map_apply measurable_fst (measurableSet_singleton e.1)]
    exact measure_mono (singleton_subset_iff.mpr rfl)
  refine ⟨he, hs, hm.1, hm.2,
    injOn_support_of_legalCounting_of_map_singleton_le_one _ _ hc Prod.fst measurable_fst hr,
    injOn_support_of_legalCounting_of_map_singleton_le_one _ _ hc Prod.snd measurable_snd ht, ?_, ?_⟩
  · intro x hx
    apply existsUnique_support_preimage_of_legalCounting_of_map_singleton_le_one _ _ hc
      Prod.fst measurable_fst hr x
    change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst {x} ≠ 0
    rwa [hm.1, legalInputColorMeasure_singleton]
  · intro y hy
    apply existsUnique_support_preimage_of_legalCounting_of_map_singleton_le_one _ _ hc
      Prod.snd measurable_snd ht y
    change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd {y} ≠ 0
    rwa [hm.2, legalInputColorMeasure_singleton]

/-- The actual original Poisson weak scene with its internally recovered
whole marginals is almost surely a genuine full integer matching. -/
theorem ae_isFullOriginalInputMatching_of_legalMarkedInputSceneLaw_tendsto
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    (hfull : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)), IsFullOriginalInputMatching q s := by
  filter_upwards [ae_isLegalSimpleCountingMeasure_input_of_legalMarkedInputSceneLaw_tendsto
    q hq α β kin hk g hg t L hL hlarge hweak,
    ae_isLegalCountingMeasure_of_legalMarkedInputSceneLaw_tendsto q α β kin hk g hg t L hL hweak,
    hfull] with s hs hc hm
  exact isFullOriginalInputMatching_of_counting_simple_marginals q s hc.1 hs hm

end OTSelector.Reconstruction
