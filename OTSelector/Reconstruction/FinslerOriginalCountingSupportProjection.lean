import OTSelector.Reconstruction.FinslerOriginalSceneCloudBridge

/-!
# Support projection for counting measures

This module proves the support-projection step needed to make the scene edge
index map surjective onto the scene support.

1. **mem_support_fst_of_singleton_pos**: if a point of a product carries
   positive measure, its first coordinate lies in the support of the first
   marginal.  This is the support projection for arbitrary measures on a
   product (using that a neighbourhood contains an open measurable set).

2. **scene_source_mem_support_fst_of_singleton_pos**: for a scene with positive
   single-edge mass, the edge's source lies in the support of the edge-measure
   first marginal.

3. **scene_source_mem_support_colorMeasure_of_singleton_pos**: the same source
   lies in the support of the original colour input measure, by the exact colour
   marginal identity of a full original input matching.

## Exact remaining sub-gap

The hypothesis here is positivity of the SINGLE-EDGE mass
0 < (s.1.1) {e}.  Deriving it from mere support membership
e ∈ (s.1.1).support requires that the scene edge measure is atomic with support
equal to its atom set (support membership = strict positivity on the singleton);
the library has no such support-atomicity lemma for the counting-measure
construction.  With 0 < (s.1.1) {e} the projection is proved, and applying the
marginal identity gives the source support membership.  From there one also
needs that support membership in the colour measure gives positive input atom
mass at (e.1, 0), the same atomicity issue for the coloured input counting
measure.

Measurability of originalMatchingEdgeOfSource additionally needs a measurable
selection: the map is defined by Classical.choose from the unique existence, so
measurability holds if the standard Borel structure on the occupied support
makes the unique selection measurable (a measurable-selection theorem), which is
not available in the current library.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Support projection for a product measure.**  A point of a product with
positive measure has first coordinate in the support of the first marginal. -/
theorem mem_support_fst_of_singleton_pos
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure (α × β)) {e : α × β} (hμ : 0 < μ {e}) :
    e.1 ∈ (μ.map Prod.fst).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨V, hVU, hVopen, heV⟩ := mem_nhds_iff.mp hU
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hpos : 0 < (μ.map Prod.fst) V := by
    rw [Measure.map_apply measurable_fst hVmeas]
    refine lt_of_lt_of_le hμ (measure_mono ?_)
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact heV
  exact lt_of_lt_of_le hpos (measure_mono hVU)

/-- **Support projection onto the scene edge source.**  An edge with positive
scene mass has its source in the support of the edge-measure first marginal. -/
theorem scene_source_mem_support_fst_of_singleton_pos {q : ℕ}
    (s : LegalMarkedOptimalInputScene q) {e : LegalMarkedPhysicalEdge q}
    (he : 0 < (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) {e}) :
    e.1 ∈ ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst).support :=
  mem_support_fst_of_singleton_pos
    (μ := (s.1.1 : Measure (LegalMarkedPhysicalEdge q))) he

/-- **Support projection onto the original colour measure.**  For a full
original input matching, the source of an edge with positive scene mass lies in
the support of the original colour input measure of colour zero. -/
theorem scene_source_mem_support_colorMeasure_of_singleton_pos {q : ℕ}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    {e : LegalMarkedPhysicalEdge q}
    (he : 0 < (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) {e}) :
    e.1 ∈ (legalInputColorMeasure q s.2 0).support := by
  have h := scene_source_mem_support_fst_of_singleton_pos s he
  rwa [hs.source_marginal] at h

end OTSelector.Reconstruction
