import OTSelector.Reconstruction.OriginalCompletePathTrafficSquare
import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes

/-! The same-scene traffic-square bridge for actual normalized general Finsler momenta. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}

/-- The norm of the original paired-mark momentum in the actual internal phase frame. -/
def originalNormalizedMomentumMarkNorm (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) : ℝ :=
  ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖

theorem measurable_originalNormalizedMomentumMarkNorm
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ) :
    Measurable (originalNormalizedMomentumMarkNorm S w T) :=
  (continuous_const.matrix_mulVec continuous_id).norm.measurable.comp
    (measurable_originalSeedPairMomentum S hF hw)

theorem originalNormalizedMomentumMarkNorm_anchor
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    originalNormalizedMomentumMarkNorm S w T (physicalPairAnchor e).2 =
      ‖normalizedMomentumNodeValue S w T e‖ := rfl

/-- Actual complete-path traffic in a phase level is squared using the original scene's
literal contributor count. The actual field/tube producers must supply the count,
per-edge occupation bound and amplitude-to-node comparison appearing here. -/
theorem original_normalized_completePathTraffic_sq_le_of_count_weight
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (V : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
    (hfiniteCount : (s.1.1 : Measure (LegalMarkedPhysicalEdge _)) V < (⊤ : ℝ≥0∞))
    (hfinite : legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s ≠ (⊤ : ℝ≥0∞))
    (hfiniteWeight : legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η
      (fun z ↦ ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1) * f z) s ≠ (⊤ : ℝ≥0∞))
    (hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge _)), e ∉ V →
      legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e = 0)
    {B K W C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge _)).restrict V,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B)
    (hcount : (s.1.1 : Measure (LegalMarkedPhysicalEdge _)).real V ≤ K * W)
    (hweight : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge _)).restrict V,
      W ≤ C * ‖normalizedMomentumNodeValue S w T e‖) :
    (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal ^ 2 ≤
      B * K * C * (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η
        (fun z ↦ ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1) * f z)
          s).toReal := by
  apply legalMarkedCompletePathTraffic_sq_le_of_count_weight _
    ((measurable_originalSeedCompletePath S hF hw).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) hη hf
    (originalNormalizedMomentumMarkNorm S w T)
    (measurable_originalNormalizedMomentumMarkNorm S hF hw T) (fun _ ↦ norm_nonneg _)
    s V hfiniteCount hfinite hfiniteWeight hzero hB hK hbound hcount
  simpa only [originalNormalizedMomentumMarkNorm_anchor] using hweight

end OTSelector.Reconstruction
