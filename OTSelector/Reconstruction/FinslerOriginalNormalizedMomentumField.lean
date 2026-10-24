import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes
import OTSelector.Reconstruction.OriginalCountingVectorField

/-! The actual canonical original momentum field in an arbitrary phase frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Literal canonical infimum field of the same original nodes, with position
transformed by `T` and momentum by its inverse transpose. -/
def normalizedMomentumPhaseField
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (x : Fin (finrank ℝ S.covector.ker) → ℝ) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalCountingVectorField (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) L
    (normalizedMomentumNodePosition S w T (cut + S.level)) (normalizedMomentumNodeValue S w T)
    (D.normalizedMomentumPhaseNodeMeasure T cut h s) x

/-- The actual normalized field is Borel in the entire original scene and
the normalized physical position. -/
theorem measurable_normalizedMomentumPhaseField
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
        D.normalizedMomentumPhaseField T cut h L a.1 a.2) :=
  (measurable_originalCountingVectorField _ L _ _
    (measurable_normalizedMomentumNodePosition S hF hw T (cut + S.level))
    (measurable_normalizedMomentumNodeValue S hF hw T)).comp
      (((D.measurable_normalizedMomentumPhaseNodeMeasure hF hw T hcut h).comp
        measurable_fst).prodMk measurable_snd)

/-- The same normalized field is globally Lipschitz on every ambient scene. -/
theorem lipschitzWith_normalizedMomentumPhaseField
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LipschitzWith L (D.normalizedMomentumPhaseField T cut h L s) :=
  lipschitzWith_originalCountingVectorField _ L _ _ _

/-- A physical reroot subtracts `T v` from normalized positions and leaves
the actual normalized momentum field value unchanged. -/
theorem normalizedMomentumPhaseField_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s)
    (v x : Fin (finrank ℝ S.covector.ker) → ℝ) :
    D.normalizedMomentumPhaseField T cut h L (legalMarkedInputSceneReroot _ v s) (x - T *ᵥ v) =
      D.normalizedMomentumPhaseField T cut h L s x := by
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hn := isLegalCountingMeasure_originalCountingNodeRestriction
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h)
  have hR : Isometry (fun y : Fin (finrank ℝ S.covector.ker) → ℝ ↦ y - T *ᵥ v) := by
    apply Isometry.of_dist_eq
    intro a b
    rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]
  change originalCountingVectorField _ L _ _
    (D.normalizedMomentumPhaseNodeMeasure T cut h (legalMarkedInputSceneReroot _ v s)) _ = _
  rw [D.normalizedMomentumPhaseNodeMeasure_reroot hF hw T hcut h v s]
  exact originalCountingVectorField_mapHomeomorph _ L _ _ _ hn (physicalSceneEdgeReroot v)
    (fun y ↦ y - T *ᵥ v) hR (normalizedMomentumNodePosition_reroot S w T (cut + S.level) v)
    (normalizedMomentumNodeValue_reroot S w T v) x

/-- At every genuinely occupied eligible edge, the generic vector extension
retains the exact original rough-node error in this same phase frame. -/
theorem normalizedMomentumPhaseField_node_error_of_node_bound
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s) {b : ℝ} (hb : 0 ≤ b)
    (hrough : ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ f ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ‖normalizedMomentumNodeValue S w T e - normalizedMomentumNodeValue S w T f‖ ≤
          L * dist (normalizedMomentumNodePosition S w T (cut + S.level) e)
            (normalizedMomentumNodePosition S w T (cut + S.level) f) + b)
    {e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)}
    (he : e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support) :
    ‖normalizedMomentumNodeValue S w T e - D.normalizedMomentumPhaseField T cut h L s
      (normalizedMomentumNodePosition S w T (cut + S.level) e)‖ ≤ b := by
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hn := isLegalCountingMeasure_originalCountingNodeRestriction
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h)
  exact originalCountingVectorField_node_error _ L _ _ _ hn hb hrough he

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
