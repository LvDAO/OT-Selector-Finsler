import OTSelector.Reconstruction.FinslerOriginalSceneCountIdentity
import OTSelector.Reconstruction.FinslerOriginalCloudCountIdentity

/-!
# Scene cardinality identity: occupied source atoms = scene support

This module proves the scene-side cardinality identity unconditionally, avoiding
the unavailable cloud-count correspondence: the occupied source input atoms of a
full original input matching are in explicit bijection with the scene support
edges, so the counts agree in every cardinality sense, and the scene edge total
mass is the shell-cardinality sum of the representing configuration.

1. **sceneSupportSourceFun**: the occupied source atom to edge map (the matching
   edge index map, as a genuine function on the subtype of occupied atoms).
2. **sceneSupportSourceFun_mem_support**: its values are support edges.
3. **sceneSupportSourceFun_injective**: it is injective (two atoms with the same
   edge coincide), from the anchoring property.
4. **sceneSupportSourceFun_bijective**: it is a bijection from occupied source
   atoms onto the support subtype: surjectivity is the occupancy gap closure
   plus the uniqueness characterization of the edge index map.
5. **scene_occupied_source_card_eq_support_card**: consequently the number of
   occupied source atoms equals the number of support edges (Nat.card).
6. **scene_edge_mass_eq_shellSum**: the scene edge total mass is the
   configuration shell-cardinality sum (the scene side of the mass identity).

## Remaining bridge to the cloud count coordinates

The scene support count is unconditionally identified with the occupied source
count.  Identifying it with mSourceCount/mTargetCount would need the missing
Palm mass-transport (Campbell unit-weight) identity: the cloud side's realized
plan mass equals the legal maximum cardinality of the realized legal graph
(proved in FinslerOriginalRealizedCloudCount), but no theorem transports the
scene edge mass to that plan mass.  So the identity proved here is the paper's
count identity SCENE-SIDE: occupied source atoms = support edges = matched pairs,
expressed purely in scene/legal-matching terms.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **The occupied source atom to edge map** of a full original input
matching. -/
noncomputable def sceneSupportSourceFun {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    {x : LegalMarkedPhysicalPoint q //
        (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0} →
      LegalMarkedPhysicalEdge q :=
  fun p => originalMatchingEdgeOfSource hs p.1 p.2

/-- **The map lands in the scene support.** -/
theorem sceneSupportSourceFun_mem_support {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (p : {x : LegalMarkedPhysicalPoint q //
      (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0}) :
    sceneSupportSourceFun hs p ∈
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support :=
  originalMatchingEdgeOfSource_mem_support hs p.1 p.2

/-- **The map is injective.** -/
theorem sceneSupportSourceFun_injective {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    Function.Injective (sceneSupportSourceFun hs) := by
  intro p p' hpp'
  have h := originalMatchingEdgeOfSource_injective hs p.2 p'.2 hpp'
  exact Subtype.ext h

/-- **The map is a bijection onto the support subtype.** -/
theorem sceneSupportSourceFun_bijective {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    Function.Bijective (fun p : {x : LegalMarkedPhysicalPoint q //
        (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0} =>
      (⟨sceneSupportSourceFun hs p, sceneSupportSourceFun_mem_support hs p⟩ :
        {e : LegalMarkedPhysicalEdge q //
          e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support})) := by
  constructor
  · intro p p' hpp'
    exact sceneSupportSourceFun_injective hs (Subtype.ext_iff.mp hpp')
  · intro e
    refine ⟨⟨e.1.1, scene_source_atom_ne_zero hs e.2⟩, ?_⟩
    apply Subtype.ext
    exact originalMatchingEdgeOfSource_surjective_on_support hs e.2

/-- **Cardinality identity: occupied source atoms = scene support edges.** -/
theorem scene_occupied_source_card_eq_support_card
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    Nat.card {x : LegalMarkedPhysicalPoint q //
        (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0} =
      Nat.card {e : LegalMarkedPhysicalEdge q //
        e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support} := by
  exact Nat.card_congr (Equiv.ofBijective _ (sceneSupportSourceFun_bijective hs))

/-- **Scene edge total mass via the configuration** (re-export). -/
theorem scene_edge_mass_eq_shellSum {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
      ∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞) :=
  scene_edge_totalMass hs

end OTSelector.Reconstruction
