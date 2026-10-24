import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedRetainedCut
import OTSelector.Reconstruction.OriginalStageResidualDensityRestrictedPrefix

/-! Exact actual retained cancellation gives gamma in the chosen physical frame. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The original retained cut mass and original endpoint prefix cancel internally, in the
same chosen physical cube. The literal gamma is the real surviving reserve prefix plus
that same full-main delta divided by actual volume, uniformly over all reserve indices. -/
theorem ae_all_originalOrientedStageGamma_eq_reservePrefix_add_fullCutError
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    (hRone : 1 ≤ R) (c : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalOrientedStageResidualDensityData S w b R ell :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      A.gamma c = (A.reservePrefix c + originalOrientedStageFullCutError S w b R c scene) / A.cubeVolume := by
  have hell0 : 0 ≤ ell := by linarith
  filter_upwards [D.ae_originalOriented_windows_eq_retained_add_ports hF hw Q b hell0 hR,
    D.ae_originalOrientedStagePlans_finite hF hw Q b hell0 hR,
    D.ae_originalOrientedRetainedCut_finite_inner hF hw Q b hell0 hR c,
    D.ae_ae_original_pairKernel_interior_forward Q,
    ae_originalOrientedOmittedCutDensity_integrable S hF hw Q b R ell c,
    ae_originalRestrictedSceneSlabCharges_finiteOnCompacts S hF hw Q
      (originalOrientedPathLengthRetained S w b R ell)ᶜ c c]
    with scene hwindows hfinite hcut hlegal hνI hloc
  intro sourceReserve targetReserve sourceKept targetKept
  let A : OriginalOrientedStageResidualDensityData S w b R ell :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  let B := originalOrientedPathLengthRetained S w b R ell
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  let π : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := originalStageRestrictedPathPlan B scene
  let πs : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := originalStageWindowSourcePortPlan B K scene
  let πt : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := originalStageWindowTargetPortPlan B K scene
  let : IsFiniteMeasure π := hfinite.1
  let : IsFiniteMeasure πs := hfinite.2.1
  let : IsFiniteMeasure πt := hfinite.2.2
  let : IsFiniteMeasure π.fst := by change IsFiniteMeasure (π.map Prod.fst); infer_instance
  let : IsFiniteMeasure π.snd := by change IsFiniteMeasure (π.map Prod.snd); infer_instance
  let : IsFiniteMeasure πs.fst := by change IsFiniteMeasure (πs.map Prod.fst); infer_instance
  let : IsFiniteMeasure πt.snd := by change IsFiniteMeasure (πt.map Prod.snd); infer_instance
  let κ := originalRestrictedSceneActiveCutMeasure S w B c scene
  let ρ := originalOrientedOmittedSceneActiveCutMeasure S w b R ell c scene
  let : IsFiniteMeasure κ := hcut.1
  let : IsFiniteMeasureOnCompacts ρ := hloc.2.2.1
  have hdeep : ∀ᵐ x ∂κ, x ∈ originalCenteredPhysicalCubeRegion b (2 * (R - 1)) := by
    filter_upwards [hcut.2] with x hx
    have hc : 1 ≤ originalStageFrameCollarFactor b * ell := by
      nlinarith [one_le_originalStageFrameCollarFactor b]
    exact originalCenteredPhysicalCubeRegion_mono b (by linarith) hx
  obtain ⟨hκI, hretMass⟩ := originalOrientedStageRawSmoothing_integrable_mass_of_deep κ b hRone hdeep
  have hretPrefix : π.fst.real {p | p.2 < c} - π.snd.real {p | p.2 ≤ c} = κ.real univ :=
    originalStageRestrictedEndpointPrefix_eq_cutMass S hF hw
      (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell) scene
      (hlegal.mono (fun _ h ↦ h.2.2)) c
  have hmain : originalStageMainInputWindowPrefix K c scene =
      (π.fst.real {p | p.2 < c} - π.snd.real {p | p.2 ≤ c}) + A.portPrefix c := by
    dsimp only [originalStageMainInputWindowPrefix, OriginalOrientedStageResidualDensityData.portPrefix,
      OriginalOrientedStageResidualDensityData.sourcePortMeasure, OriginalOrientedStageResidualDensityData.targetPortMeasure, A]
    rw [hwindows.1, hwindows.2, measureReal_add_apply, measureReal_add_apply]
    ring
  have hνpoint (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
      Integrable (fun x ↦ originalEuclideanMollifier _ (x - z)) ρ := by
    have hc : HasCompactSupport (fun x ↦ originalEuclideanMollifier (finrank ℝ S.covector.ker) (x - z)) := by
      simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
        (hasCompactSupport_originalEuclideanMollifier (finrank ℝ S.covector.ker)).comp_homeomorph (Homeomorph.addRight (-z))
    exact ((contDiff_originalEuclideanMollifier _).continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport hc
  have hpoint (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
      (∫ x, originalEuclideanMollifier _ (x - z) ∂originalSceneActiveCutMeasure S w c scene) =
        (∫ x, originalEuclideanMollifier _ (x - z) ∂κ) + originalOrientedOmittedCutDensity S w b R ell c scene z := by
    have hsum : originalSceneActiveCutMeasure S w c scene = κ + ρ :=
      (originalRestrictedSceneMarkedPositionMeasure_add_compl
        (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell)
        (measurable_originalSeedPathOffset S hF hw c) _ scene).symm
    rw [hsum, integral_add_measure]
    · rfl
    · apply Integrable.of_bound
        (((contDiff_originalEuclideanMollifier _).continuous.measurable.comp (measurable_id.sub_const z)).aestronglyMeasurable)
        (originalEuclideanMollifierBound _)
      exact Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using abs_originalEuclideanMollifier_le _ (x - z))
    · exact hνpoint z
  have hfullMass : (∫ z in K, ∫ x, originalEuclideanMollifier _ (x - z) ∂originalSceneActiveCutMeasure S w c scene) =
      (∫ z in K, ∫ x, originalEuclideanMollifier _ (x - z) ∂κ) +
        ∫ z in K, originalOrientedOmittedCutDensity S w b R ell c scene z := by
    simp_rw [hpoint]
    exact integral_add hκI hνI
  have hcancel : A.portPrefix c - (∫ z, originalOrientedOmittedCutDensity S w b R ell c scene z ∂A.cubeMeasure) =
      originalOrientedStageFullCutError S w b R c scene := by
    change A.portPrefix c - (∫ z in K, originalOrientedOmittedCutDensity S w b R ell c scene z) = _
    unfold originalOrientedStageFullCutError
    change (∫ z in K, ∫ x, originalEuclideanMollifier _ (x - z) ∂κ) = κ.real univ at hretMass
    rw [hmain, hfullMass, hretMass, hretPrefix]
    ring
  change (A.portPrefix c + A.reservePrefix c -
    (∫ z, originalOrientedOmittedCutDensity S w b R ell c scene z ∂A.cubeMeasure)) / A.cubeVolume = _
  apply congrArg (fun v : ℝ ↦ v / A.cubeVolume)
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
