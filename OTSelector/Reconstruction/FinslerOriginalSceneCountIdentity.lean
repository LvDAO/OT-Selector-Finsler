import OTSelector.PointProcess.LocalConfiguration.Support
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching
import OTSelector.Reconstruction.FinslerOriginalSceneCloudBridge

/-!
# Scene counting instantiation and count identity

This module closes the scene transfer of global support atomicity.

1. **sceneEdgeConfig**: the local configuration representing the scene edge
   measure, obtained by unpacking IsFullOriginalInputMatching.simple_edges
   (whose base is the zero edge, as the field literally states).
2. **sceneEdgeConfig_spec**: the represented local finite measure is s.1.1.
3. **scene_edge_support_eq_atomSet**: the scene edge support is the atom set of
   the representing configuration.
4. **scene_edge_multiplicity_pos_of_mem_support** and
   **scene_edge_multiplicity_le_one**: a support edge has multiplicity in
   [1,1], hence multiplicity exactly one: the scene edge measure is simple.
5. **scene_source_atom_ne_zero**: the source input atom of a support edge has
   positive scene input mass, via the source marginal identity and the
   restriction/projection form of the color measure.
6. **originalMatchingEdgeOfSource_surjective_on_support**: the matching edge
   index map hits every support edge; with injectivity from the earlier module
   this is a bijection between occupied source input atoms and the scene support.
7. **scene_support_eq_range_bridge**: the scene support is exactly the range of
   the edge index map over occupied source atoms.

## Exact remaining sub-gap

The CLOUD count identity (scene support cardinality = mSourceCount = mTargetCount)
still needs the scene-to-cloud correspondence: mSourceCount/mTargetCount are
fields of the cloud space TwoMarkedCloudSpace, and the library relates the scene
law to the cloud law only through the Palm constructions; there is no measurable
map identifying scene edges with cloud colour labels.  All scene-side identities
(atom set, multiplicity one, surjectivity, support = range) are proved here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The scene edge counting configuration.** -/
noncomputable def sceneEdgeConfig {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    LocalConfiguration (0 : LegalMarkedPhysicalEdge q) :=
  Classical.choose hs.simple_edges

/-- **The representing configuration gives back the scene edge measure.** -/
theorem sceneEdgeConfig_spec {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    LocalConfiguration.toLocalFiniteMeasure (sceneEdgeConfig hs) = s.1.1 :=
  (Classical.choose_spec hs.simple_edges).1

/-- The coercion of a configuration's local finite measure is its counting
measure. -/
theorem scene_toLocalFiniteMeasure_coe {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    ((LocalConfiguration.toLocalFiniteMeasure (sceneEdgeConfig hs)) :
        Measure (LegalMarkedPhysicalEdge q)) =
      LocalConfiguration.countingMeasure (sceneEdgeConfig hs) :=
  rfl

/-- **The scene edge support is the atom set of the representing
configuration.** -/
theorem scene_edge_support_eq_atomSet {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support =
      {e : LegalMarkedPhysicalEdge q |
        0 < LocalConfiguration.multiplicity (sceneEdgeConfig hs) e} := by
  have hval : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) =
      LocalConfiguration.countingMeasure (sceneEdgeConfig hs) := by
    have h := congrArg
      (fun μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) =>
        (μ : Measure (LegalMarkedPhysicalEdge q))) (sceneEdgeConfig_spec hs)
    rw [scene_toLocalFiniteMeasure_coe hs] at h
    exact h.symm
  rw [hval]
  simpa only [Function.support, Nat.pos_iff_ne_zero] using
    LocalConfiguration.support_countingMeasure (sceneEdgeConfig hs)

/-- **Every support edge has positive multiplicity.** -/
theorem scene_edge_multiplicity_pos_of_mem_support
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) {e : LegalMarkedPhysicalEdge q}
    (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) :
    0 < LocalConfiguration.multiplicity (sceneEdgeConfig hs) e := by
  rw [scene_edge_support_eq_atomSet hs] at he
  exact he

/-- **The representing configuration is simple.** -/
theorem scene_edge_multiplicity_le_one {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (e : LegalMarkedPhysicalEdge q) :
    LocalConfiguration.multiplicity (sceneEdgeConfig hs) e ≤ 1 :=
  (Classical.choose_spec hs.simple_edges).2 e

/-- **Every support edge has multiplicity exactly one.** -/
theorem scene_edge_multiplicity_eq_one
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) {e : LegalMarkedPhysicalEdge q}
    (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) :
    LocalConfiguration.multiplicity (sceneEdgeConfig hs) e = 1 :=
  le_antisymm (scene_edge_multiplicity_le_one hs e)
    (scene_edge_multiplicity_pos_of_mem_support hs he)

/-- **The source input atom of a support edge is occupied.** -/
theorem scene_source_atom_ne_zero {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) {e : LegalMarkedPhysicalEdge q}
    (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) :
    (s.2 : Measure (LegalColoredInputPoint q)) {(e.1, 0)} ≠ 0 := by
  classical
  have hmult := scene_edge_multiplicity_pos_of_mem_support hs he
  have hval : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) =
      LocalConfiguration.countingMeasure (sceneEdgeConfig hs) := by
    have h := congrArg
      (fun μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) =>
        (μ : Measure (LegalMarkedPhysicalEdge q))) (sceneEdgeConfig_spec hs)
    rw [scene_toLocalFiniteMeasure_coe hs] at h
    exact h.symm
  have hsingle : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) {e} ≠ 0 := by
    rw [hval, LocalConfiguration.countingMeasure_singleton]
    intro hzero
    have hzero' : LocalConfiguration.multiplicity (sceneEdgeConfig hs) e = 0 := by
      simpa using hzero
    omega
  have hfst : ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst) {e.1} ≠ 0 := by
    rw [Measure.fst, Measure.map_apply measurable_fst (measurableSet_singleton e.1)]
    intro hzero
    apply hsingle
    apply measure_mono_null ?_ hzero
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact rfl
  have hcolor : (legalInputColorMeasure q s.2 0) {e.1} ≠ 0 := by
    rw [← hs.source_marginal]
    exact hfst
  have hsing : (legalInputColorMeasure q s.2 0) {e.1} =
      (s.2 : Measure (LegalColoredInputPoint q)) {(e.1, (0 : Fin 2))} := by
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst
      (measurableSet_singleton e.1), Measure.restrict_apply
      ((measurableSet_singleton e.1).preimage measurable_fst)]
    congr 1
    ext x
    simp [Prod.ext_iff]
  rw [hsing] at hcolor
  exact hcolor

/-- **Surjectivity of the matching edge index map onto the scene support.** -/
theorem originalMatchingEdgeOfSource_surjective_on_support
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) {e : LegalMarkedPhysicalEdge q}
    (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) :
    originalMatchingEdgeOfSource hs e.1 (scene_source_atom_ne_zero hs he) = e :=
  (eq_originalMatchingEdgeOfSource_of_mem hs e.1 (scene_source_atom_ne_zero hs he)
    he rfl).symm

/-- **The scene support is the range of the edge index map** over occupied
source atoms. -/
theorem scene_support_eq_range_bridge {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support =
      {e : LegalMarkedPhysicalEdge q |
        ∃ (x : LegalMarkedPhysicalPoint q)
          (hx : (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0),
          originalMatchingEdgeOfSource hs x hx = e} := by
  ext e
  constructor
  · intro he
    exact ⟨e.1, scene_source_atom_ne_zero hs he,
      originalMatchingEdgeOfSource_surjective_on_support hs he⟩
  · rintro ⟨x, hx, rfl⟩
    exact originalMatchingEdgeOfSource_mem_support hs x hx

end OTSelector.Reconstruction
