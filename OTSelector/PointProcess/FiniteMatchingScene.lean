import OTSelector.Basic.EuclideanOptimizer
import OTSelector.PointProcess.LocalConfigurationTuple
import OTSelector.PointProcess.GraphHeightCompactness
import OTSelector.Finite.OptimizerMeasurability
import OTSelector.Feedback.StoppedContinuationGraph
import OTSelector.Feedback.Comparison

/-!
# Actual finite rooted matching scenes

The carrier records two marked point configurations, the marked edge configuration, and the
normalized graph height with its current at the root.  It retains multiplicities and imposes no
perfectness, stationarity, or limiting-environment assumption.
-/

open MeasureTheory Set Function
open scoped BigOperators Classical ENNReal NNReal

set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess

namespace GraphHeight

noncomputable instance instMeasurableSpace : MeasurableSpace GraphHeight := borel GraphHeight
instance instBorelSpace : BorelSpace GraphHeight := ⟨rfl⟩
noncomputable instance instStandardBorelSpace : StandardBorelSpace GraphHeight :=
  inferInstance

end GraphHeight

/-- The common marked point space for finite source and target intersections. -/
abbrev MatchingPoint := ℝ × UnitMark

/-- A fixed base point for the shell coding; the mark is not a chosen root mark. -/
def matchingPointBase : MatchingPoint := (0, ⟨0, by constructor <;> norm_num⟩)

/-- Probability carrier for rooted marked matching scenes, independent of sample size. -/
@[ext]
structure MatchingScene where
  source : LocalConfiguration matchingPointBase
  target : LocalConfiguration matchingPointBase
  edges : LocalConfiguration (matchingPointBase, matchingPointBase)
  path : FeedbackPath

namespace MatchingScene


abbrev Coordinates := LocalConfiguration matchingPointBase ×
  LocalConfiguration matchingPointBase ×
  LocalConfiguration (matchingPointBase, matchingPointBase) × FeedbackPath

def equivCoordinates : MatchingScene ≃ Coordinates where
  toFun scene := (scene.source, scene.target, scene.edges, scene.path)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv scene := by cases scene; rfl
  right_inv p := by cases p; rfl

noncomputable instance instMeasurableSpace : MeasurableSpace MatchingScene :=
  MeasurableSpace.comap equivCoordinates inferInstance

/-- Coordinate encoding is a measurable equivalence, with no limiting properties attached. -/
def measurableEquivCoordinates : MatchingScene ≃ᵐ Coordinates where
  toEquiv := equivCoordinates
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    rw [measurable_comap_iff]
    simpa using (measurable_id : Measurable (id : Coordinates → Coordinates))

noncomputable instance instStandardBorelSpace : StandardBorelSpace MatchingScene :=
  by
    let _ := upgradeStandardBorel Coordinates
    let _ : TopologicalSpace MatchingScene :=
      TopologicalSpace.induced measurableEquivCoordinates inferInstance
    let _ : PolishSpace MatchingScene := measurableEquivCoordinates.toEquiv.polishSpace_induced
    let _ : BorelSpace MatchingScene :=
      measurableEquivCoordinates.measurableEmbedding.borelSpace ⟨rfl⟩
    exact ⟨⟨inferInstance, inferInstance, inferInstance⟩⟩

end MatchingScene

end OTSelector.PointProcess

namespace OTSelector.FeedbackGraph

/-- Normalize the actual feedback graph at a physical observation root. -/
noncomputable def rootedHeight {lam : ℝ} (graph : FeedbackGraph lam) (z : ℝ) :
    PointProcess.GraphHeight where
  toContinuousMap := ⟨fun x ↦ graph.curve (x + z) - graph.curve z, by
    have hLip : LipschitzWith (Real.toNNReal lam) graph.curve := by
      apply LipschitzWith.of_dist_le'
      intro x y
      simpa only [Real.dist_eq, abs_sub_comm] using graph.lipschitz x y
    exact (hLip.continuous.comp (continuous_id.add continuous_const)).sub continuous_const⟩
  map_zero' := by simp

@[simp]
theorem rootedHeight_apply {lam : ℝ} (graph : FeedbackGraph lam) (z x : ℝ) :
    graph.rootedHeight z x = graph.curve (x + z) - graph.curve z := rfl

@[simp]
theorem rootedHeight_reroot {lam : ℝ} (graph : FeedbackGraph lam) (z a : ℝ) :
    (graph.rootedHeight z).reroot a = graph.rootedHeight (z + a) := by
  ext x
  simp only [PointProcess.GraphHeight.reroot_apply, rootedHeight_apply]
  rw [show x + a + z = x + (z + a) by ring, show a + z = z + a by ring]
  ring

end OTSelector.FeedbackGraph

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)

/-- Actual source intersection and its original physical mark, viewed from `z`. -/
noncomputable def rootedSourcePoint (z : ℝ) (i : Fin n) : MatchingPoint :=
  (sample.sourceIntersection graph i - z, sample.sourceMark i)

/-- Actual target intersection and its original physical mark, viewed from `z`. -/
noncomputable def rootedTargetPoint (z : ℝ) (j : Fin n) : MatchingPoint :=
  (sample.targetIntersection graph j - z, sample.targetMark j)

/-- The complete finite scene of a specified assignment on the actual feedback graph. -/
noncomputable def rootedMatchingScene (σ : Assignment n) (z : ℝ) : MatchingScene where
  source := LocalConfiguration.ofTuple matchingPointBase (sample.rootedSourcePoint graph z)
  target := LocalConfiguration.ofTuple matchingPointBase (sample.rootedTargetPoint graph z)
  edges := LocalConfiguration.ofTuple (matchingPointBase, matchingPointBase)
    (fun i ↦ (sample.rootedSourcePoint graph z i, sample.rootedTargetPoint graph z (σ i)))
  path := ⟨graph.rootedHeight z,
    (sample.sourceIntersectionCount graph z : ℤ) - sample.targetIntersectionCount graph z⟩

/-- The scene uses the original Euclidean optimizer selected in the finite model. -/
noncomputable def rootedEuclideanScene (z : ℝ) : MatchingScene :=
  sample.rootedMatchingScene graph sample.euclideanOptimizer z

/-- The scene used by the actual stopped feedback comparison construction. -/
noncomputable def stoppedRootedEuclideanScene
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (eta B : ℝ) (T : ℝ≥0) (z : ℝ) :
    MatchingScene :=
  sample.rootedEuclideanScene
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) z

@[simp]
theorem countingMeasure_rootedMatchingScene_source (σ : Assignment n) (z : ℝ) :
    LocalConfiguration.countingMeasure (sample.rootedMatchingScene graph σ z).source =
      ∑ i, Measure.dirac (sample.rootedSourcePoint graph z i) :=
  LocalConfiguration.countingMeasure_ofTuple _

@[simp]
theorem countingMeasure_rootedMatchingScene_target (σ : Assignment n) (z : ℝ) :
    LocalConfiguration.countingMeasure (sample.rootedMatchingScene graph σ z).target =
      ∑ j, Measure.dirac (sample.rootedTargetPoint graph z j) :=
  LocalConfiguration.countingMeasure_ofTuple _

@[simp]
theorem countingMeasure_rootedMatchingScene_edges (σ : Assignment n) (z : ℝ) :
    LocalConfiguration.countingMeasure (sample.rootedMatchingScene graph σ z).edges =
      ∑ i, Measure.dirac
        (sample.rootedSourcePoint graph z i, sample.rootedTargetPoint graph z (σ i)) :=
  LocalConfiguration.countingMeasure_ofTuple _

/-- The stored root current is the exact finite matching crossing current. -/
theorem rootedMatchingScene_rootCurrent_eq_crossingCurrent (σ : Assignment n) (z : ℝ) :
    (sample.rootedMatchingScene graph σ z).path.rootCurrent =
      assignmentCrossingCurrent (sample.sourceIntersection graph)
        (sample.targetIntersection graph) σ z := by
  rw [assignmentCrossingCurrent_eq_rankDiscrepancy, assignmentRankDiscrepancy,
    target_count_comp_perm]
  simp only [rootedMatchingScene, sourceIntersectionCount, targetIntersectionCount]
  congr 1 <;> exact (Finset.sum_boole _ _).symm

end OTSelector.FiniteSample
