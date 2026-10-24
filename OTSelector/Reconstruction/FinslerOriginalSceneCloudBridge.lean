import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching
import OTSelector.PointProcess.LocalConfiguration.MassBridge

/-!
# Scene-to-cloud bridge: edge index map of a full original input matching

This module builds the bridge from FinslerOriginalCountingMassBridge.  For a
scene that is a full original input matching, the occupancy field
IsFullOriginalInputMatching.source_occupied (and target_occupied) says that
every occupied input atom has a unique support edge anchored at it.  We use that
unique existence to define the edge index map of the scene:

  originalMatchingEdgeOfSource : (occupied source atom) -> support edge,

and prove the three structural properties of the bridge:

1. **originalMatchingEdgeOfSource_fst**: the chosen edge is anchored at the
   source atom;
2. **originalMatchingEdgeOfSource_mem_support**: the chosen edge is a support
   edge (i.e. the map lands in the scene support);
3. **originalMatchingEdgeOfSource_injective**: distinct source atoms give
   distinct support edges.  Together with occupancy this says the map is an
   injection from occupied source atoms onto the scene support.

4. **eq_originalMatchingEdgeOfSource_of_mem**: every support edge that is
   anchored at an occupied source atom is the chosen edge of that atom, i.e. the
   map is surjective onto the support (over occupied anchors).

## Exact remaining sub-gap

Two things remain.  (i) SURJECTIVITY FOR ALL SUPPORT EDGES: to conclude that
every support edge is hit, one needs that the source of every support edge is an
occupied input atom, (s.2) {(e.1, 0)} != 0.  This follows from the marginal
identity IsFullOriginalInputMatching.source_marginal together with the support
of a counting-measure marginal, but the library has no support projection lemma
for fst/snd of counting measures, so it is not derived here.  (ii) THE CLOUD
LABELS: even with (i), the count identity is
  (scene support).ncard = mSourceCount = mTargetCount,
where mSourceCount/mTargetCount are CLOUD quantities of TwoMarkedCloudSpace.
There is no measurable scene-to-cloud map in the library (the scene law and the
cloud law are related only through the Palm/scene constructions), so identifying
the scene support count with the cloud colour counts requires that
scene-to-cloud correspondence.  The edge index map, its anchored value, its
membership in the support, its injectivity and its uniqueness characterization
are proved here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Edge index map of the scene matching.**  The unique support edge anchored
at an occupied source input atom. -/
noncomputable def originalMatchingEdgeOfSource {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (x : LegalMarkedPhysicalPoint q)
    (hx : (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0) :
    LegalMarkedPhysicalEdge q :=
  Classical.choose (hs.source_occupied x hx)

/-- **The chosen edge is anchored at the source atom.** -/
theorem originalMatchingEdgeOfSource_fst {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (x : LegalMarkedPhysicalPoint q)
    (hx : (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0) :
    (originalMatchingEdgeOfSource hs x hx).1 = x :=
  (Classical.choose_spec (hs.source_occupied x hx)).1.2

/-- **The chosen edge lies in the scene support.** -/
theorem originalMatchingEdgeOfSource_mem_support {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (x : LegalMarkedPhysicalPoint q)
    (hx : (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0) :
    originalMatchingEdgeOfSource hs x hx ∈
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support :=
  (Classical.choose_spec (hs.source_occupied x hx)).1.1

/-- **Uniqueness characterization of the chosen edge.**  Any support edge
anchored at x is the chosen edge of x. -/
theorem eq_originalMatchingEdgeOfSource_of_mem {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (x : LegalMarkedPhysicalPoint q)
    (hx : (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0)
    {e : LegalMarkedPhysicalEdge q}
    (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) (hxe : e.1 = x) :
    e = originalMatchingEdgeOfSource hs x hx :=
  (Classical.choose_spec (hs.source_occupied x hx)).2 e ⟨he, hxe⟩

/-- **Injectivity of the edge index map.**  Distinct source atoms are indexed by
distinct support edges, since both edges are anchored at their source atom. -/
theorem originalMatchingEdgeOfSource_injective {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) {x y : LegalMarkedPhysicalPoint q}
    (hx : (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0)
    (hy : (s.2 : Measure (LegalColoredInputPoint q)) {(y, 0)} ≠ 0)
    (hxy : originalMatchingEdgeOfSource hs x hx = originalMatchingEdgeOfSource hs y hy) :
    x = y := by
  rw [← originalMatchingEdgeOfSource_fst hs x hx,
    ← originalMatchingEdgeOfSource_fst hs y hy, hxy]

end OTSelector.Reconstruction
