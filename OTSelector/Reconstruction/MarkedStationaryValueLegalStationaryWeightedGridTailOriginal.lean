import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWeightedGridTail
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalPathMoment

/-!
# The actual original focal kinetic energy and path length survive large grids

Both weights are evaluated on the original stationary matching, its original
source-unit window, and every original target. Original conditional moment
data supply path integrability; a displacement second moment is never assumed.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
local instance markedStationaryValueLegalStationaryWeightedGridTailOriginalInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryWeightedGridTailOriginalPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original focal weighted kinetic energy of a genuine weighted
stationary matching has vanishing random-grid cut energy. -/
theorem tendsto_original_focal_stationary_shiftedGrid_crossing_kinetic_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) {gap : ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ phase, ∫⁻ scene,
        ∫⁻ e in {e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) |
            e.1.1 ∈ palmUnitCube (Fin (finrank ℝ S.covector.ker))},
          (if shiftedGridCells (R n) phase e.1.1 ≠ shiftedGridCells (R n) phase e.2.1
            then ENNReal.ofReal (D.originalFocalKinetic gap e.1.2 e.2.2 (e.2.1 - e.1.1)) else 0)
          ∂(scene.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        ∂(legalMarkedInputPairLaw (finrank ℝ S.covector.ker) Q.law : Measure
          (CavityLocalScene (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
            (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))))
      ∂shiftedGridPhaseLaw (finrank ℝ S.covector.ker) (R n)) atTop (𝓝 0) := by
  exact tendsto_original_stationary_shiftedGrid_crossing_kinetic_zero Q
    (D.measurable_originalFocalKinetic hF hw gap) R hRpos hR

/-- The same genuine original matching loses vanishing total original
compliance-path length when the independent grid spacing grows. Every required
path moment is supplied by the actual original conditional moment witness. -/
theorem tendsto_original_focal_stationary_shiftedGrid_crossing_pathLength_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ phase, ∫⁻ scene,
        ∫⁻ e in {e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) |
            e.1.1 ∈ palmUnitCube (Fin (finrank ℝ S.covector.ker))},
          (if shiftedGridCells (R n) phase e.1.1 ≠ shiftedGridCells (R n) phase e.2.1
            then ENNReal.ofReal (originalSeedPairPathLength S w (physicalPairAnchor e).2) else 0)
          ∂(scene.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        ∂(legalMarkedInputPairLaw (finrank ℝ S.covector.ker) Q.law : Measure
          (CavityLocalScene (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
            (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))))
      ∂shiftedGridPhaseLaw (finrank ℝ S.covector.ker) (R n)) atTop (𝓝 0) := by
  exact tendsto_original_stationary_shiftedGrid_crossing_palm_weight_zero Q
    (originalSeedPairPathLength S w) (measurable_originalSeedPairPathLength S hF hw)
    (D.integrable_pathLength_of_original_weighted_stationary hF hw hbounds Q) R hRpos hR

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
