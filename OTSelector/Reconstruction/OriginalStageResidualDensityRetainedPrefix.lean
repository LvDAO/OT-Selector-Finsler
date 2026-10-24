import OTSelector.Reconstruction.OriginalStageResidualDensityRetainedCutMass
import OTSelector.Reconstruction.OriginalFullCutOccupation

/-! Exact original retained endpoint prefix counts equal the same retained active-cut mass. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

private theorem originalStage_prefix_difference_eq_crossing {q : ℕ}
    (σ : Measure ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) [IsFiniteMeasure σ]
    (hforward : ∀ᵐ a ∂σ, a.2.1.1 < a.2.1.2) (c : ℝ) :
    σ.real {a | a.2.1.1 < c} - σ.real {a | a.2.1.2 ≤ c} =
      σ.real {a | a.2.1.1 < c ∧ c < a.2.1.2} := by
  let τ := σ.map Prod.snd
  let α := τ.map (fun m ↦ m.1.1)
  let β := τ.map (fun m ↦ m.1.2)
  have hτ : ∀ᵐ m ∂τ, m.1.1 < m.1.2 :=
    (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt measurable_fst.fst measurable_fst.snd)).mpr hforward
  have he := measure_strict_forward_clock_crossing_add_target_prefix q τ α β rfl rfl hτ c
  have hs : α (Iio c) = σ {a | a.2.1.1 < c} := by
    change ((σ.map Prod.snd).map (fun m ↦ m.1.1)) (Iio c) = _
    rw [Measure.map_apply measurable_fst.fst measurableSet_Iio]
    change (σ.map Prod.snd) {m | m.1.1 < c} = _
    rw [Measure.map_apply measurable_snd (show MeasurableSet
      {m : PhysicalPairPalmMark (Fin q) | m.1.1 < c} from
        measurableSet_lt measurable_fst.fst measurable_const)]
    rfl
  have ht : β (Iic c) = σ {a | a.2.1.2 ≤ c} := by
    change ((σ.map Prod.snd).map (fun m ↦ m.1.2)) (Iic c) = _
    rw [Measure.map_apply measurable_fst.snd measurableSet_Iic]
    change (σ.map Prod.snd) {m | m.1.2 ≤ c} = _
    rw [Measure.map_apply measurable_snd (show MeasurableSet
      {m : PhysicalPairPalmMark (Fin q) | m.1.2 ≤ c} from
        measurableSet_le measurable_fst.snd measurable_const)]
    rfl
  have hc : τ {m | m.1.1 < c ∧ c < m.1.2} =
      σ {a | a.2.1.1 < c ∧ c < a.2.1.2} := by
    rw [show τ = σ.map Prod.snd from rfl, Measure.map_apply measurable_snd
      (show MeasurableSet {m : PhysicalPairPalmMark (Fin q) | m.1.1 < c ∧ c < m.1.2} from
        (measurableSet_lt measurable_fst.fst measurable_const).inter
          (measurableSet_lt measurable_const measurable_fst.snd))]
    rfl
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hs, ht, hc] at hr
  change (σ {a | a.2.1.1 < c}).toReal - (σ {a | a.2.1.2 ≤ c}).toReal =
    (σ {a | a.2.1.1 < c ∧ c < a.2.1.2}).toReal
  linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Original anchor restriction is exactly the pushforward of the same actual retained plan. -/
theorem originalPathRetainedPlan_anchorKernel_eq (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    (R ell : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (physicalScenePairKernel scene.1).restrict (originalPathLengthRetained S w R ell) =
      (originalPathRetainedPlan S w R ell scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).map physicalPairAnchor := by
  rw [physicalScenePairKernel_apply, Measure.restrict_map measurable_physicalPairAnchor
    (measurableSet_originalPathLengthRetained S hF hw R ell)]
  rfl

/-- The actual retained source-minus-target endpoint prefix, with unchanged endpoint clocks. -/
def originalStageRetainedEndpointPrefix (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell c : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  (originalPathRetainedPlan S w R ell scene :
    Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst.real {p | p.2 < c} -
  (originalPathRetainedPlan S w R ell scene :
    Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd.real {p | p.2 ≤ c}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Every actual retained edge crossing the cut contributes one to its original endpoint
prefix difference and one to the same positive retained cut occupation measure. -/
theorem ae_originalRetainedEndpointPrefix_eq_cutMass
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (R ell c : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalStageRetainedEndpointPrefix S w R ell c scene =
        (originalRestrictedSceneActiveCutMeasure S w
          (originalPathLengthRetained S w R ell) c scene).real univ := by
  filter_upwards [ae_originalPathRetainedPlan_finite hF hw Q R ell,
    D.ae_ae_original_pairKernel_interior_forward Q] with scene hfinite hlegal
  let A := originalPathLengthRetained S w R ell
  let σ := (physicalScenePairKernel scene.1).restrict A
  let π : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
    originalPathRetainedPlan S w R ell scene
  have hanchor : σ = π.map physicalPairAnchor :=
    originalPathRetainedPlan_anchorKernel_eq S hF hw R ell scene
  have : IsFiniteMeasure σ := ⟨by
    change (physicalScenePairKernel scene.1).restrict A univ < (∞ : ℝ≥0∞)
    rw [Measure.restrict_apply_univ, ← originalPathRetainedPlan_mass_eq_pairKernel hF hw R ell scene]
    exact hfinite⟩
  have hs : π.fst {p | p.2 < c} = σ {a | a.2.1.1 < c} := by
    change (π.map Prod.fst) {p | p.2 < c} = _
    rw [Measure.map_apply measurable_fst (measurableSet_lt measurable_snd measurable_const),
      hanchor, Measure.map_apply measurable_physicalPairAnchor
        (measurableSet_lt measurable_snd.fst.fst measurable_const)]
    rfl
  have ht : π.snd {p | p.2 ≤ c} = σ {a | a.2.1.2 ≤ c} := by
    change (π.map Prod.snd) {p | p.2 ≤ c} = _
    rw [Measure.map_apply measurable_snd (measurableSet_le measurable_snd measurable_const),
      hanchor, Measure.map_apply measurable_physicalPairAnchor
        (measurableSet_le measurable_snd.fst.snd measurable_const)]
    rfl
  have hpos : Measurable (fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      a.1 + originalSeedPathOffset S w c a.2) :=
    measurable_fst.add ((measurable_originalSeedPathOffset S hF hw c).comp measurable_snd)
  have hc : (originalRestrictedSceneActiveCutMeasure S w A c scene).real univ =
      σ.real {a | a.2.1.1 < c ∧ c < a.2.1.2} := by
    unfold originalRestrictedSceneActiveCutMeasure originalRestrictedSceneMarkedPositionMeasure
    rw [measureReal_def, Measure.map_apply hpos MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    rfl
  have hcross := originalStage_prefix_difference_eq_crossing σ
    ((ae_restrict_of_ae hlegal).mono (fun _ h ↦ h.2.2)) c
  unfold originalStageRetainedEndpointPrefix
  change (π.fst {p | p.2 < c}).toReal - (π.snd {p | p.2 ≤ c}).toReal = _
  rw [hs, ht, hc]
  exact hcross

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
