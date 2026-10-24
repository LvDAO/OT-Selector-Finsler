import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoEdgeSwap
import OTSelector.MeasureTheory.ParameterizedRestriction
import OTSelector.Probability.CavitySemidiscreteGridPhase

/-!
# The literal complete-cell pieces of the original full matching

The existing half-open Haar grid partitions the edges whose two spatial
endpoints lie in one cell. Every crossing edge is kept in the exact complement.
The moving restrictions remain actual measurable integer measures.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

/-- Complete original edges in one existing half-open translated Haar-grid cell. -/
def originalCompleteGridCell (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) : Set (LegalMarkedPhysicalEdge q) :=
  {e | e.1.1 ∈ cavityGridCube (Fin q) ell (g +ᵥ u) ∧
    e.2.1 ∈ cavityGridCube (Fin q) ell (g +ᵥ u)}

/-- Complete-cell membership is Borel jointly in the actual phase and edge. -/
theorem measurableSet_originalCompleteGridCell_joint (q : ℕ) (ell : ℝ)
    (g : CavityGridLattice (Fin q) ell) :
    MeasurableSet {p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q |
      p.2 ∈ originalCompleteGridCell q ell p.1 g} := by
  let b : Fin q → ℝ := fun i ↦ (g i : ℝ)
  change MeasurableSet {p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q |
    p.2.1.1 - (b + p.1) ∈ cavityGridPhaseCell (Fin q) ell ∧
      p.2.2.1 - (b + p.1) ∈ cavityGridPhaseCell (Fin q) ell}
  exact ((measurableSet_cavityGridPhaseCell (Fin q) ell).preimage
    (measurable_snd.fst.fst.sub (measurable_const.add measurable_fst))).inter
      ((measurableSet_cavityGridPhaseCell (Fin q) ell).preimage
        (measurable_snd.snd.fst.sub (measurable_const.add measurable_fst)))

/-- Every individual literal complete cell is Borel. -/
theorem measurableSet_originalCompleteGridCell (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) : MeasurableSet (originalCompleteGridCell q ell u g) :=
  (measurableSet_originalCompleteGridCell_joint q ell g).preimage
    (measurable_const.prodMk measurable_id)

/-- Two different grid cells never select the same original complete edge. -/
theorem pairwise_disjoint_originalCompleteGridCell (q : ℕ) {ell : ℝ} (hell : 0 < ell)
    (u : Fin q → ℝ) :
    Pairwise (fun g h : CavityGridLattice (Fin q) ell ↦
      Disjoint (originalCompleteGridCell q ell u g) (originalCompleteGridCell q ell u h)) := by
  intro g h hne
  apply Set.disjoint_left.mpr
  intro e he hf
  exact Set.disjoint_left.mp (pairwise_disjoint_cavityGridCube (Fin q) ell hell u hne)
    he.1 hf.1

/-- The whole original edge measure is exactly its unchanged crossing piece
plus its actual complete-cell restrictions; no point is sampled or discarded. -/
theorem measure_eq_crossing_add_completeGridPieces (q : ℕ) {ell : ℝ} (hell : 0 < ell)
    (u : Fin q → ℝ) (μ : Measure (LegalMarkedPhysicalEdge q)) :
    μ = μ.restrict (⋃ g, originalCompleteGridCell q ell u g)ᶜ +
      Measure.sum (fun g ↦ μ.restrict (originalCompleteGridCell q ell u g)) := by
  have hm := measurableSet_originalCompleteGridCell q ell u
  calc
    μ = μ.restrict (⋃ g, originalCompleteGridCell q ell u g)ᶜ +
        μ.restrict (⋃ g, originalCompleteGridCell q ell u g) :=
      (Measure.restrict_compl_add_restrict (MeasurableSet.iUnion hm)).symm
    _ = _ := by
      rw [Measure.restrict_iUnion (pairwise_disjoint_originalCompleteGridCell q hell u) hm]

/-- The literal moving complete-cell piece of the same original matching plan. -/
def originalCompleteGridPiece (q : ℕ) (ell : ℝ)
    (g : CavityGridLattice (Fin q) ell)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨(p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    (originalCompleteGridCell q ell p.2 g), inferInstance⟩

/-- The original complete-cell piece is jointly Borel in the actual scene and phase. -/
theorem measurable_originalCompleteGridPiece (q : ℕ) (ell : ℝ)
    (g : CavityGridLattice (Fin q) ell) : Measurable (originalCompleteGridPiece q ell g) := by
  let U : Set ((LegalMarkedOptimalInputScene q × (Fin q → ℝ)) ×
      LegalMarkedPhysicalEdge q) := {p | p.2 ∈ originalCompleteGridCell q ell p.1.2 g}
  have hU : MeasurableSet U := (measurableSet_originalCompleteGridCell_joint q ell g).preimage
    (measurable_fst.snd.prodMk measurable_snd)
  exact measurable_originalParameterizedRestriction (fun p ↦ p.1.1.1)
    measurable_fst.fst.fst U hU

/-- Every complete-cell piece remains the same actual original integer measure. -/
theorem IsFullOriginalInputMatching.counting_completeGridPiece {q : ℕ}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (ell : ℝ) (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell) :
    IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)
      (originalCompleteGridPiece q ell g (s, u)) := by
  exact isLegalCountingMeasure_restrict _ s.1.1
    ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1 _

/-- An occupied selected original edge keeps its unit mass in its literal cell. -/
theorem IsFullOriginalInputMatching.completeGridPiece_singleton_eq_one {q : ℕ}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (ell : ℝ) (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell)
    {e : LegalMarkedPhysicalEdge q} (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support)
    (hcell : e ∈ originalCompleteGridCell q ell u g) :
    (originalCompleteGridPiece q ell g (s, u) : Measure (LegalMarkedPhysicalEdge q)) {e} = 1 := by
  change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    (originalCompleteGridCell q ell u g) {e} = 1
  simpa only [Measure.restrict_apply (measurableSet_singleton e), singleton_inter_of_mem hcell]
    using hs.edge_singleton_eq_one he

end OTSelector.Reconstruction
