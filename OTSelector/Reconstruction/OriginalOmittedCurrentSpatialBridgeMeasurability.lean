import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridge
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Joint scene/space measurability of actual full and retained clock currents. -/
open Set Function Filter MeasureTheory Module Manifold ProbabilityTheory
open scoped ENNReal BigOperators Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

private theorem stronglyMeasurable_pairRestrictedClockCurrent_joint_spatial
    (q : ℕ) (d v : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (hd : Measurable d) (hv : Measurable v)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    (B : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    (hB : MeasurableSet B) (A : Set ℝ) :
    StronglyMeasurable (fun p : LegalMarkedOptimalInputScene q × (Fin q → ℝ) ↦
      ∫ c in A, ∫ a in B, η (a.1 + d (a.2,c) - p.2) • v (a.2,c)
        ∂physicalScenePairKernel p.1.1) := by
  let κ : Kernel ((LegalMarkedOptimalInputScene q × (Fin q → ℝ)) × ℝ)
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) :=
    ((physicalScenePairKernel (ι := Fin q)).comap
      (fun p : (LegalMarkedOptimalInputScene q × (Fin q → ℝ)) × ℝ ↦ p.1.1.1)
      measurable_fst.fst.fst).restrict hB
  have hmc : Measurable (fun p :
      ((LegalMarkedOptimalInputScene q × (Fin q → ℝ)) × ℝ) ×
        ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) ↦ (p.2.2,p.1.2)) :=
    measurable_snd.snd.prodMk measurable_fst.snd
  have hpos : Measurable (fun p :
      ((LegalMarkedOptimalInputScene q × (Fin q → ℝ)) × ℝ) ×
        ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) ↦
      p.2.1 + d (p.2.2,p.1.2) - p.1.1.2) :=
    (measurable_snd.fst.add (hd.comp hmc)).sub measurable_fst.fst.snd
  have hG : Measurable (fun p :
      ((LegalMarkedOptimalInputScene q × (Fin q → ℝ)) × ℝ) ×
        ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) ↦
      η (p.2.1 + d (p.2.2,p.1.2) - p.1.1.2) • v (p.2.2,p.1.2)) :=
    (hη.comp hpos).smul (hv.comp hmc)
  have hread := hG.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  have hclock := hread.integral_prod_right' (ν := (volume : Measure ℝ).restrict A)
  simpa only [κ, Kernel.restrict_apply, Kernel.comap_apply] using hclock

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The literal clock-outer current of any fixed restriction of unchanged original pairs. -/
def originalPairRestrictedSeedPathClockSetCurrent (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (B : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  ∫ c in A, ∫ a in B,
    η (a.1 + originalSeedPathOffset S w c a.2) • originalSeedClockOccupation S w c a.2
      ∂physicalScenePairKernel scene.1

/-- The actual restricted current is jointly strongly measurable in scene and spatial
translate. No differentiability or finite-traffic premise is used. -/
theorem stronglyMeasurable_originalPairRestrictedCurrent_joint_spatial
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (B) (hB : MeasurableSet B) (A : Set ℝ) :
    StronglyMeasurable (fun p :
      LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
      originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-p.2)) A p.1) :=
  stronglyMeasurable_pairRestrictedClockCurrent_joint_spatial _
    (fun p ↦ originalSeedPathOffset S w p.2 p.1)
    (fun p ↦ originalSeedClockOccupation S w p.2 p.1)
    (measurable_originalSeedPathOffset_joint S hF hw)
    (measurable_originalSeedClockOccupation S hF hw) hη B hB A

/-- The literal full original current is jointly strongly measurable in scene and space. -/
theorem stronglyMeasurable_originalFullCurrent_joint_spatial
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) (A : Set ℝ) :
    StronglyMeasurable (fun p :
      LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
      originalSeedPathClockSetCurrent S w (fun x ↦ η (x-p.2)) A p.1) := by
  simpa only [originalPairRestrictedSeedPathClockSetCurrent, Measure.restrict_univ,
    originalSeedPathClockSetCurrent, legalMarkedPathWindowReadout] using
    stronglyMeasurable_originalPairRestrictedCurrent_joint_spatial S hF hw hη
      univ MeasurableSet.univ A

/-- The actual retained original current is jointly strongly measurable in scene and space. -/
theorem stronglyMeasurable_originalRetainedCurrent_joint_spatial
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) (A : Set ℝ) :
    StronglyMeasurable (fun p :
      LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
      originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-p.2)) A p.1) :=
  stronglyMeasurable_originalPairRestrictedCurrent_joint_spatial S hF hw hη
    (originalPathLengthRetained S w R ell)
    (measurableSet_originalPathLengthRetained S hF hw R ell) A

/-- The same actual full-minus-retained field is a jointly measurable random spatial field. -/
theorem measurable_originalOmittedCurrent_joint_spatial
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) (A : Set ℝ) :
    Measurable (fun p :
      LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
      originalSeedPathClockSetCurrent S w (fun x ↦ η (x-p.2)) A p.1 -
      originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-p.2)) A p.1) :=
  ((stronglyMeasurable_originalFullCurrent_joint_spatial S hF hw hη A).sub
    (stronglyMeasurable_originalRetainedCurrent_joint_spatial S hF hw R ell hη A)).measurable

end OTSelector.Reconstruction
