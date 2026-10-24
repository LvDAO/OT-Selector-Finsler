import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching
import OTSelector.MeasureTheory.MeasurableLocalMeasureEquality

/-!
# A full matching from actual integer edges and simple whole inputs

The generic argument keeps the given edge and input measures. Integer edges,
simple source and target atoms, and complete marginal equalities imply one
positive unit edge at every occupied input atom, with no duplicate partners.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {X Y : Type*}
  [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [MetricSpace Y] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- An actual integer measure has no unoccupied extra points in its support. -/
theorem singleton_ne_zero_iff_mem_support_of_legalCounting
    (base : X) (μ : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ) (x : X) :
    (μ : Measure X) {x} ≠ 0 ↔ x ∈ (μ : Measure X).support := by
  obtain ⟨c, rfl⟩ := hμ
  change LocalConfiguration.countingMeasure c {x} ≠ 0 ↔
    x ∈ (LocalConfiguration.countingMeasure c).support
  rw [LocalConfiguration.countingMeasure_singleton, LocalConfiguration.support_countingMeasure]
  simp only [Nat.cast_ne_zero, Function.mem_support]

/-- The same edge and input measures form a full one-to-one original matching.
The original integer carrier and both simple whole inputs remain accessible. -/
structure IsFullOriginalBipartiteMatching (baseX : X) (baseY : Y)
    (π : LocalFiniteMeasure (X × Y)) (source : LocalFiniteMeasure X)
    (target : LocalFiniteMeasure Y) : Prop where
  integer_edges : IsLegalCountingMeasure (baseX, baseY) π
  simple_edges : IsLegalSimpleCountingMeasure (baseX, baseY) π
  simple_source : IsLegalSimpleCountingMeasure baseX source
  simple_target : IsLegalSimpleCountingMeasure baseY target
  source_marginal : (π : Measure (X × Y)).fst = (source : Measure X)
  target_marginal : (π : Measure (X × Y)).snd = (target : Measure Y)
  source_injective : Set.InjOn Prod.fst (π : Measure (X × Y)).support
  target_injective : Set.InjOn Prod.snd (π : Measure (X × Y)).support
  source_occupied : ∀ x, (source : Measure X) {x} ≠ 0 →
    ∃! e, e ∈ (π : Measure (X × Y)).support ∧ e.1 = x
  target_occupied : ∀ y, (target : Measure Y) {y} ≠ 0 →
    ∃! e, e ∈ (π : Measure (X × Y)).support ∧ e.2 = y

/-- Integer edges with their complete simple input marginals automatically
supply every full-matching field on the same original measures. -/
theorem isFullOriginalBipartiteMatching_of_counting_simple_marginals
    (baseX : X) (baseY : Y) (π : LocalFiniteMeasure (X × Y))
    (source : LocalFiniteMeasure X) (target : LocalFiniteMeasure Y)
    (hc : IsLegalCountingMeasure (baseX, baseY) π)
    (hs : IsLegalSimpleCountingMeasure baseX source)
    (ht : IsLegalSimpleCountingMeasure baseY target)
    (hsrc : (π : Measure (X × Y)).fst = (source : Measure X))
    (htgt : (π : Measure (X × Y)).snd = (target : Measure Y)) :
    IsFullOriginalBipartiteMatching baseX baseY π source target := by
  have hr (x : X) : (π : Measure (X × Y)).map Prod.fst {x} ≤ 1 := by
    change (π : Measure (X × Y)).fst {x} ≤ 1
    rw [hsrc]
    exact ((isLegalSimpleCountingMeasure_iff _ _).mp hs).2 x
  have hu (y : Y) : (π : Measure (X × Y)).map Prod.snd {y} ≤ 1 := by
    change (π : Measure (X × Y)).snd {y} ≤ 1
    rw [htgt]
    exact ((isLegalSimpleCountingMeasure_iff _ _).mp ht).2 y
  have he : IsLegalSimpleCountingMeasure (baseX, baseY) π := by
    apply (isLegalSimpleCountingMeasure_iff _ _).mpr
    refine ⟨hc, fun e ↦ ?_⟩
    apply le_trans ?_ (hr e.1)
    rw [Measure.map_apply measurable_fst (measurableSet_singleton e.1)]
    exact measure_mono (singleton_subset_iff.mpr rfl)
  refine ⟨hc, he, hs, ht, hsrc, htgt,
    injOn_support_of_legalCounting_of_map_singleton_le_one _ _ hc Prod.fst measurable_fst hr,
    injOn_support_of_legalCounting_of_map_singleton_le_one _ _ hc Prod.snd measurable_snd hu,
    ?_, ?_⟩
  · intro x hx
    apply existsUnique_support_preimage_of_legalCounting_of_map_singleton_le_one _ _ hc
      Prod.fst measurable_fst hr x
    change (π : Measure (X × Y)).fst {x} ≠ 0
    rwa [hsrc]
  · intro y hy
    apply existsUnique_support_preimage_of_legalCounting_of_map_singleton_le_one _ _ hc
      Prod.snd measurable_snd hu y
    change (π : Measure (X × Y)).snd {y} ≠ 0
    rwa [htgt]

namespace IsFullOriginalBipartiteMatching
variable {baseX : X} {baseY : Y} {π : LocalFiniteMeasure (X × Y)}
  {source : LocalFiniteMeasure X} {target : LocalFiniteMeasure Y}

/-- The same source input retains its actual integer carrier. -/
theorem source_counting (h : IsFullOriginalBipartiteMatching baseX baseY π source target) :
    IsLegalCountingMeasure baseX source :=
  ((isLegalSimpleCountingMeasure_iff _ _).mp h.simple_source).1

/-- The same target input retains its actual integer carrier. -/
theorem target_counting (h : IsFullOriginalBipartiteMatching baseX baseY π source target) :
    IsLegalCountingMeasure baseY target :=
  ((isLegalSimpleCountingMeasure_iff _ _).mp h.simple_target).1

/-- Every actual occupied matching edge has exactly unit mass. -/
theorem edge_atom_eq_one (h : IsFullOriginalBipartiteMatching baseX baseY π source target)
    {e : X × Y} (he : e ∈ (π : Measure (X × Y)).support) :
    (π : Measure (X × Y)) {e} = 1 :=
  le_antisymm (((isLegalSimpleCountingMeasure_iff _ _).mp h.simple_edges).2 e)
    (one_le_singleton_of_mem_support_of_legalCounting _ _ h.integer_edges he)

/-- Every occupied source atom has exactly one positive actual edge partner. -/
theorem source_partner (h : IsFullOriginalBipartiteMatching baseX baseY π source target)
    (x : X) (hx : (source : Measure X) {x} ≠ 0) :
    ∃! y, 0 < (π : Measure (X × Y)) {(x, y)} := by
  obtain ⟨e, he, huniq⟩ := h.source_occupied x hx
  refine ⟨e.2, ?_, fun y hy ↦ ?_⟩
  · change 0 < (π : Measure (X × Y)) {(x, e.2)}
    have heq : (x, e.2) = e := Prod.ext he.2.symm rfl
    rw [heq, h.edge_atom_eq_one he.1]
    exact zero_lt_one
  · have hsupp := (singleton_ne_zero_iff_mem_support_of_legalCounting
      _ _ h.integer_edges (x, y)).mp (ne_of_gt hy)
    exact congrArg Prod.snd (huniq (x, y) ⟨hsupp, rfl⟩)

/-- Every occupied target atom has exactly one positive actual edge partner. -/
theorem target_partner (h : IsFullOriginalBipartiteMatching baseX baseY π source target)
    (y : Y) (hy : (target : Measure Y) {y} ≠ 0) :
    ∃! x, 0 < (π : Measure (X × Y)) {(x, y)} := by
  obtain ⟨e, he, huniq⟩ := h.target_occupied y hy
  refine ⟨e.1, ?_, fun x hx ↦ ?_⟩
  · change 0 < (π : Measure (X × Y)) {(e.1, y)}
    have heq : (e.1, y) = e := Prod.ext rfl he.2.symm
    rw [heq, h.edge_atom_eq_one he.1]
    exact zero_lt_one
  · have hsupp := (singleton_ne_zero_iff_mem_support_of_legalCounting
      _ _ h.integer_edges (x, y)).mp (ne_of_gt hx)
    exact congrArg Prod.fst (huniq (x, y) ⟨hsupp, rfl⟩)
end IsFullOriginalBipartiteMatching

/-- The full-matching assertion is exactly its integer, simple-input and
whole-marginal data; the quantified partner conclusions follow automatically. -/
theorem isFullOriginalBipartiteMatching_iff_counting_simple_marginals
    (baseX : X) (baseY : Y) (π : LocalFiniteMeasure (X × Y))
    (source : LocalFiniteMeasure X) (target : LocalFiniteMeasure Y) :
    IsFullOriginalBipartiteMatching baseX baseY π source target ↔
      IsLegalCountingMeasure (baseX, baseY) π ∧
      IsLegalSimpleCountingMeasure baseX source ∧
      IsLegalSimpleCountingMeasure baseY target ∧
      (π : Measure (X × Y)).fst = (source : Measure X) ∧
      (π : Measure (X × Y)).snd = (target : Measure Y) := by
  constructor
  · intro h
    exact ⟨h.integer_edges, h.simple_source, h.simple_target,
      h.source_marginal, h.target_marginal⟩
  · rintro ⟨hc, hs, ht, hsrc, htgt⟩
    exact isFullOriginalBipartiteMatching_of_counting_simple_marginals
      baseX baseY π source target hc hs ht hsrc htgt

local instance originalIIDFullMatchingPrimitiveSourcePolish : PolishSpace
    (LocalFiniteMeasure X) := LocalFiniteMeasure.instPolishSpace
local instance originalIIDFullMatchingPrimitiveTargetPolish : PolishSpace
    (LocalFiniteMeasure Y) := LocalFiniteMeasure.instPolishSpace
local instance originalIIDFullMatchingPrimitiveEdgePolish : PolishSpace
    (LocalFiniteMeasure (X × Y)) := LocalFiniteMeasure.instPolishSpace

/-- The complete actual full-matching assertion is measurable on the joint
edge/source/target carrier. Quantified atom fields require no extra event. -/
theorem measurableSet_isFullOriginalBipartiteMatching
    [StandardBorelSpace X] [StandardBorelSpace Y] (baseX : X) (baseY : Y) :
    MeasurableSet {s : LocalFiniteMeasure (X × Y) ×
        (LocalFiniteMeasure X × LocalFiniteMeasure Y) |
      IsFullOriginalBipartiteMatching baseX baseY s.1 s.2.1 s.2.2} := by
  let S := LocalFiniteMeasure (X × Y) × (LocalFiniteMeasure X × LocalFiniteMeasure Y)
  have hsrc : Measurable (fun s : S ↦ (s.1 : Measure (X × Y)).fst) :=
    (Measure.measurable_map Prod.fst measurable_fst).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst)
  have htgt : Measurable (fun s : S ↦ (s.1 : Measure (X × Y)).snd) :=
    (Measure.measurable_map Prod.snd measurable_snd).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst)
  have he : {s : S | IsFullOriginalBipartiteMatching baseX baseY s.1 s.2.1 s.2.2} =
      {s : S | IsLegalCountingMeasure (baseX, baseY) s.1} ∩
      ({s : S | IsLegalSimpleCountingMeasure baseX s.2.1} ∩
      ({s : S | IsLegalSimpleCountingMeasure baseY s.2.2} ∩
      ({s : S | (s.1 : Measure (X × Y)).fst = (s.2.1 : Measure X)} ∩
      {s : S | (s.1 : Measure (X × Y)).snd = (s.2.2 : Measure Y)}))) := by
    ext s
    exact isFullOriginalBipartiteMatching_iff_counting_simple_marginals
      baseX baseY s.1 s.2.1 s.2.2
  rw [he]
  apply ((isClosed_isLegalCountingMeasure (baseX, baseY)).measurableSet.preimage
    measurable_fst).inter
  apply ((measurableSet_isLegalSimpleCountingMeasure baseX).preimage
    measurable_snd.fst).inter
  apply ((measurableSet_isLegalSimpleCountingMeasure baseY).preimage
    measurable_snd.snd).inter
  exact (measurableSet_measure_eq_localFiniteMeasure _ hsrc (fun s : S ↦ s.2.1)
    measurable_snd.fst).inter
    (measurableSet_measure_eq_localFiniteMeasure _ htgt (fun s : S ↦ s.2.2) measurable_snd.snd)

end OTSelector.Reconstruction



