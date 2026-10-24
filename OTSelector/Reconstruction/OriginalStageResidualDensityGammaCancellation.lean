import OTSelector.Reconstruction.OriginalStageResidualDensityRetainedPrefix

/-! The literal gamma equals the original remaining reserve prefix plus the actual full-cut error. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The full original source-minus-target prefix count in the same original physical cube. -/
def originalStageMainInputPrefix {q : ℕ} (R c : ℝ)
    (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ((legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ haarRootCube (Fin q) R}).real
      {p | p.2 < c} -
  ((legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ haarRootCube (Fin q) R}).real
      {p | p.2 ≤ c}

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The paper's actual delta: full original main prefix count minus the full original
smoothed active-cut occupation mass. No retained path or port is substituted into this definition. -/
def originalStageFullCutError (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R c : ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  originalStageMainInputPrefix R c scene -
    ∫ z in haarRootCube _ R, ∫ x, η (x - z) ∂originalSceneActiveCutMeasure S w c scene

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Retained endpoint prefixes cancel exactly against their genuine smoothed cut occupation.
Thus the actual gamma is `(remainingReservePrefix + actual full-main delta) / actualVolume`,
without assuming the cancellation, delta formula, good event, floor, or class ancestry. -/
theorem ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) (c : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (hηI : Integrable η volume)
    (hηone : ∫ x, η x = 1) (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalStageResidualDensityData S w R ell η :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      A.gamma c = (A.reservePrefix c + originalStageFullCutError S w R c η scene) / A.cubeVolume := by
  have hell0 : 0 ≤ ell := by linarith
  have hR0 : 0 ≤ R := by linarith
  filter_upwards [D.ae_original_windows_eq_retained_add_ports hF hw Q hell0 hR,
    D.ae_originalStagePortMeasures_finite hF hw Q hell0 hR,
    ae_originalPathRetainedPlan_finite hF hw Q R ell,
    D.ae_originalRetainedCut_finite_inner hF hw Q hell0 hR c,
    D.ae_originalRetainedCut_rawSmoothing_mass hF hw Q hell hR c hη.measurable hηI
      hηone hηsupport hηeven hηM,
    D.ae_originalRetainedEndpointPrefix_eq_cutMass hF hw Q R ell c,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q hR0 ell c hη.measurable hηM hηsupport,
    ae_all_integrable_originalOmittedCutDensity S hF hw Q R ell c]
    with scene hwindows hportFinite hretFinite hretCut hretMass hretPrefix hνI hνTests
  intro sourceReserve targetReserve sourceKept targetKept
  let A : OriginalStageResidualDensityData S w R ell η :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  have : IsFiniteMeasure (originalPathRetainedPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := ⟨hretFinite⟩
  have : IsFiniteMeasure (originalPathSourcePortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst := hportFinite.1
  have : IsFiniteMeasure (originalPathTargetPortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd := hportFinite.2
  have hmain : originalStageMainInputPrefix R c scene =
      originalStageRetainedEndpointPrefix S w R ell c scene + A.portPrefix c := by
    dsimp only [originalStageMainInputPrefix, originalStageRetainedEndpointPrefix,
      OriginalStageResidualDensityData.portPrefix, A]
    rw [hwindows.1, hwindows.2, measureReal_add_apply, measureReal_add_apply]
    ring
  let κ := originalRestrictedSceneActiveCutMeasure S w
    (originalPathLengthRetained S w R ell) c scene
  have : IsFiniteMeasure κ := hretCut.1
  have hκI : Integrable (fun z ↦ ∫ x, η (x - z) ∂κ)
      (volume.restrict (haarRootCube _ R)) :=
    integrable_cube_compactKernel_smoothing κ hη.measurable hηM hηsupport hR0
  have hpoint (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
      (∫ x, η (x - z) ∂originalSceneActiveCutMeasure S w c scene) =
        (∫ x, η (x - z) ∂κ) + originalOmittedCutDensity S w R ell c η z scene := by
    have hiκ : Integrable (fun x ↦ η (x - z)) κ := by
      have hm : Measurable (fun x ↦ η (x - z)) :=
        hη.measurable.comp (measurable_id.sub_const z)
      apply Integrable.of_bound hm.aestronglyMeasurable M
      exact Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using hηM (x - z))
    rw [originalSceneActiveCut_eq_retained_add_omitted S hF hw R ell c scene,
      integral_add_measure hiκ (hνTests η hη hcη z)]
    rfl
  have hfullMass : (∫ z in haarRootCube _ R,
      ∫ x, η (x - z) ∂originalSceneActiveCutMeasure S w c scene) =
      (∫ z in haarRootCube _ R, ∫ x, η (x - z) ∂κ) +
        ∫ z in haarRootCube _ R, originalOmittedCutDensity S w R ell c η z scene := by
    simp_rw [hpoint]
    exact integral_add hκI hνI
  have hcancel : A.portPrefix c -
      (∫ z in haarRootCube _ R, originalOmittedCutDensity S w R ell c η z scene) =
      originalStageFullCutError S w R c η scene := by
    unfold originalStageFullCutError
    rw [hmain, hfullMass]
    change originalStageRetainedEndpointPrefix S w R ell c scene = κ.real univ at hretPrefix
    change (∫ z in haarRootCube _ R, ∫ x, η (x - z) ∂κ) = κ.real univ at hretMass
    linarith
  change (A.portPrefix c + A.reservePrefix c -
    (∫ z in haarRootCube _ R, originalOmittedCutDensity S w R ell c η z scene)) / A.cubeVolume = _
  apply congrArg (fun v : ℝ ↦ v / A.cubeVolume)
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
