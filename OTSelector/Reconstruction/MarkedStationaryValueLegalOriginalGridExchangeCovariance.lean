import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoEdgeSwap
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCompleteGridCells
import OTSelector.Probability.CavityGridPhaseHaar

/-! # Exact transport of literal cells and original two-edge exchanges -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- A physical root translation transports the actual two deleted atoms and
both actual crossed edges exactly. -/
theorem originalTwoEdgeSwapPlan_reroot {q : ℕ} (v : Fin q → ℝ)
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) (e f : LegalMarkedPhysicalEdge q) :
    originalTwoEdgeSwapPlan (localFiniteMapHomeomorph (physicalSceneEdgeReroot v) μ)
      (physicalSceneEdgeReroot v e) (physicalSceneEdgeReroot v f) =
      localFiniteMapHomeomorph (physicalSceneEdgeReroot v) (originalTwoEdgeSwapPlan μ e f) := by
  let T := physicalSceneEdgeReroot v
  have hpre : T ⁻¹' ({T e, T f} : Set (LegalMarkedPhysicalEdge q))ᶜ = {e, f}ᶜ := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_insert_iff, mem_singleton_iff,
      T.injective.eq_iff]
  apply Subtype.ext
  change ((μ : Measure (LegalMarkedPhysicalEdge q)).map T).restrict ({T e, T f} : Set _)ᶜ +
    Measure.dirac ((T e).1, (T f).2) + Measure.dirac ((T f).1, (T e).2) =
      ((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
        Measure.dirac (e.1, f.2) + Measure.dirac (f.1, e.2)).map T
  rw [Measure.map_add _ _ T.measurable, Measure.map_add _ _ T.measurable,
    Measure.restrict_map T.measurable (by measurability), hpre,
    Measure.map_dirac, Measure.map_dirac]
  rfl

/-- A complete-cell predicate is exactly reindexed under the same original
half-open phase action, including all boundary points. -/
theorem originalCompleteGridCell_reroot_iff (q : ℕ) (ell : ℝ) [Fact (0 < ell)]
    (u v : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell) (e : LegalMarkedPhysicalEdge q) :
    physicalSceneEdgeReroot v e ∈ originalCompleteGridCell q ell
      (cavityGridPhaseReroot (Fin q) ell v u)
      (g + cavityGridCanonicalOffset (Fin q) ell (u - v)) ↔
        e ∈ originalCompleteGridCell q ell u g := by
  exact and_congr (mem_cavityGridCube_reroot_iff (Fin q) ell g u v e.1.1)
    (mem_cavityGridCube_reroot_iff (Fin q) ell g u v e.2.1)

/-- Rerooting a literal original complete-cell restriction is the literal
restriction of the rerooted original plan in its reindexed cell. -/
theorem originalCompleteGridPiece_reroot (q : ℕ) (ell : ℝ) [Fact (0 < ell)]
    (u v : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell)
    (s : LegalMarkedOptimalInputScene q) :
    originalCompleteGridPiece q ell
      (g + cavityGridCanonicalOffset (Fin q) ell (u - v))
      (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) =
      localFiniteMapHomeomorph (physicalSceneEdgeReroot v)
        (originalCompleteGridPiece q ell g (s, u)) := by
  apply Subtype.ext
  change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map (physicalSceneEdgeReroot v)).restrict
    (originalCompleteGridCell q ell (cavityGridPhaseReroot (Fin q) ell v u)
      (g + cavityGridCanonicalOffset (Fin q) ell (u - v))) =
    ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
      (originalCompleteGridCell q ell u g)).map (physicalSceneEdgeReroot v)
  rw [Measure.restrict_map (physicalSceneEdgeReroot v).measurable
    (measurableSet_originalCompleteGridCell _ _ _ _)]
  have hpre : physicalSceneEdgeReroot v ⁻¹'
      originalCompleteGridCell q ell (cavityGridPhaseReroot (Fin q) ell v u)
        (g + cavityGridCanonicalOffset (Fin q) ell (u - v)) =
      originalCompleteGridCell q ell u g := by
    ext e
    exact originalCompleteGridCell_reroot_iff q ell u v g e
  rw [hpre]

end OTSelector.Reconstruction
