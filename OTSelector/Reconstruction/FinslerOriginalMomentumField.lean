import OTSelector.Reconstruction.FinslerOriginalMomentumEligibleNodes

/-! Canonical actual Finsler momentum fields, measurable and translation covariant. -/
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

/-- The canonical coordinatewise infimum momentum field built from the actual
eligible original complete-path nodes. Empty node sets give the zero field. -/
def momentumPhaseField (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (x : Fin (finrank ℝ S.covector.ker) → ℝ) : Fin (finrank ℝ S.covector.ker) → ℝ := fun i ↦
  originalCountingRoughField (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) L
    (originalMomentumNodePosition S w (cut + S.level)) (fun e ↦ originalMomentumNodeValue S w e i)
    (D.momentumPhaseNodeMeasure cut h s) x

/-- The actual whole-scene/physical-position momentum field is jointly Borel. -/
theorem measurable_momentumPhaseField
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ D.momentumPhaseField cut h L a.1 a.2) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_originalCountingRoughField _ L _ _
    (measurable_originalMomentumNodePosition S hF hw (cut + S.level))
    ((measurable_pi_apply i).comp (measurable_originalMomentumNodeValue S hF hw))).comp
      (((D.measurable_momentumPhaseNodeMeasure hF hw hcut h).comp measurable_fst).prodMk
        measurable_snd)

/-- The canonical actual field transforms covariantly under every physical
spatial reroot, even though its original shell atom code changes. -/
theorem momentumPhaseField_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s)
    (v x : Fin (finrank ℝ S.covector.ker) → ℝ) :
    D.momentumPhaseField cut h L (legalMarkedInputSceneReroot _ v s) (x - v) =
      D.momentumPhaseField cut h L s x := by
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hn := isLegalCountingMeasure_originalCountingNodeRestriction
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.momentumPhaseEligibleEdges cut h)
  have hR : Isometry (fun y : Fin (finrank ℝ S.covector.ker) → ℝ ↦ y - v) := by
    apply Isometry.of_dist_eq
    intro a b
    rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]
  funext i
  change originalCountingRoughField _ L _ _
    (D.momentumPhaseNodeMeasure cut h (legalMarkedInputSceneReroot _ v s)) (x - v) = _
  rw [D.momentumPhaseNodeMeasure_reroot hF hw hcut h v s]
  exact originalCountingRoughField_mapHomeomorph _ L _ _ _ hn (physicalSceneEdgeReroot v)
    (fun y ↦ y - v) hR (originalMomentumNodePosition_reroot S w (cut + S.level) v)
    (fun e ↦ congrFun (originalMomentumNodeValue_reroot S w v e) i) x

/-- The already produced rough momentum bound at the actual eligible nodes
gives a genuine Lipschitz field in the same original coordinates. -/
theorem lipschitzWith_momentumPhaseField_of_node_bound
    (cut h : ℝ) (L : ℝ≥0) (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s) {b : ℝ}
    (hrough : ∀ e ∈ (D.momentumPhaseNodeMeasure cut h s : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ f ∈ (D.momentumPhaseNodeMeasure cut h s : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ‖originalMomentumNodeValue S w e - originalMomentumNodeValue S w f‖ ≤
        L * dist (originalMomentumNodePosition S w (cut + S.level) e)
          (originalMomentumNodePosition S w (cut + S.level) f) + b) :
    LipschitzWith L (D.momentumPhaseField cut h L s) := by
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hn := isLegalCountingMeasure_originalCountingNodeRestriction
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.momentumPhaseEligibleEdges cut h)
  have hcoord (i : Fin (finrank ℝ S.covector.ker)) :
      LipschitzWith L (fun x ↦ D.momentumPhaseField cut h L s x i) := by
    apply lipschitzWith_originalCountingRoughField _ L _ _ _ hn
    intro e he f hf
    have h := hrough e he f hf
    have hn := norm_le_pi_norm (originalMomentumNodeValue S w e - originalMomentumNodeValue S w f) i
    have ha := le_abs_self (originalMomentumNodeValue S w e i - originalMomentumNodeValue S w f i)
    simp only [Real.norm_eq_abs, Pi.sub_apply] at hn
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro i
  exact (hcoord i).dist_le_mul x y

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
