import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedSlabReadout
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedInputMass
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedOmittedCut

/-! The literal full cut/count slab error is the actual complete-current flux plus input masses. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The genuine original full-input half-slab count difference plus incoming-minus-outgoing
full cut mass. This keeps the same original input, without replacing it by selected ports. -/
def originalScreeningOrientedFullSlabCutError (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}).real {p | p.2 ∈ Ico s t} -
  ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}).real {p | p.2 ∈ Ioc s t} +
  (∫ z in originalCenteredPhysicalCubeRegion b (2*R), ∫ x, originalEuclideanMollifier _ (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
  (∫ z in originalCenteredPhysicalCubeRegion b (2*R), ∫ x, originalEuclideanMollifier _ (x-z) ∂originalSceneActiveCutMeasure S w t scene)

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual positive-slab FTC, reflection mass preservation and true current Gauss-Green
identify the unchanged full cut/count error with the literal full-current face flux and
both same-scene full-input boundary masses. There is no supplied flux identity. -/
theorem ae_originalScreening_orientedFullSlabCutError_eq_flux_add_inputMasses
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R : ℝ} (hR : 1 ≤ R) {s t : ℝ} (hst : s ≤ t) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalScreeningOrientedFullSlabCutError S w b R s t scene =
        originalScreeningPhysicalCurrentBoundaryPairing b
          (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene) (2*R) (fun _ ↦ 1) +
        originalScreeningOrientedReflectedInputMass b R (Ico s t) 0 scene -
        originalScreeningOrientedReflectedInputMass b R (Ioc s t) 1 scene := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  have hη : ContDiff ℝ 1 η := (contDiff_originalEuclideanMollifier q).of_le (by norm_num)
  have hcη : HasCompactSupport η := hasCompactSupport_originalEuclideanMollifier q
  have hmη := hη.continuous.measurable
  have hsupport := raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)
  have hM := originalEuclideanMollifierBound_nonneg q
  have hbound := abs_originalEuclideanMollifier_le q
  filter_upwards [D.ae_all_originalScreening_orientedFullReflectedSlab_eq_divergence_add_inputErrors hF hw hbounds Q b hR hst,
    ae_originalSceneSlabCharges_finiteOnCompacts S hF hw Q s t,
    Q.ae_finite_orientedReflectedInputOuterWindow b (2*R) 0, Q.ae_finite_orientedReflectedInputOuterWindow b (2*R) 1,
    D.ae_all_originalClockSetCurrent_spatially_contDiff hF hw hbounds Q]
      with scene hread hcharges hfinS hfinT hcurrent
  let σS := (legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}
  let σT := (legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}
  have hW : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)} :=
    (isCompact_originalStagePhysicalCube b (2*R)).measurableSet.preimage measurable_fst
  have hwindow : {p : LegalMarkedPhysicalPoint q | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)} ⊆
      originalCenteredPhysicalCubeRegion b (2*R+2) ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨originalCenteredPhysicalCubeRegion_mono b (by linarith) hp, mem_univ _⟩
  let : IsFiniteMeasure σS := ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hwindow).trans_lt hfinS⟩
  let : IsFiniteMeasure σT := ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hwindow).trans_lt hfinT⟩
  have hs := originalOrientedStageReflectedClassDensity_integrable_mass b hR σS (ae_restrict_mem hW) (Ico s t)
  have ht := originalOrientedStageReflectedClassDensity_integrable_mass b hR σT (ae_restrict_mem hW) (Ioc s t)
  let : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w s scene) := hcharges.2.2.1
  let : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w t scene) := hcharges.2.2.2
  obtain ⟨T, hT, hsub⟩ := originalStagePhysicalCube_subset_rawCube b R
  have hcs := (integrable_cube_compactKernel_smoothing (originalSceneActiveCutMeasure S w s scene)
    hmη hbound hsupport hT).mono_measure (Measure.restrict_mono_set volume hsub)
  have hct := (integrable_cube_compactKernel_smoothing (originalSceneActiveCutMeasure S w t scene)
    hmη hbound hsupport hT).mono_measure (Measure.restrict_mono_set volume hsub)
  have hzs := integrable_originalOrientedClassReflectedInputScalarField_mul (C := Ico s t) b hmη
    (originalEuclideanMollifier_radial q) hM hbound (originalEuclideanMollifier_unit_range q)
    (show 2 ≤ 2*R by linarith) measurableSet_Ico (legalInputColorMeasure q scene.2 0) hfinS
    (u := fun _ ↦ (1:ℝ)) continuous_const
  have hzt := integrable_originalOrientedClassReflectedInputScalarField_mul (C := Ioc s t) b hmη
    (originalEuclideanMollifier_radial q) hM hbound (originalEuclideanMollifier_unit_range q)
    (show 2 ≤ 2*R by linarith) measurableSet_Ioc (legalInputColorMeasure q scene.2 1) hfinT
    (u := fun _ ↦ (1:ℝ)) continuous_const
  simp only [mul_one] at hzs hzt
  let J := fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene
  have hJ : ContDiff ℝ 1 J := hcurrent (Ioc s t) η hη hcη
  have hdivc : Continuous (fun z ↦ originalStageCurrentDivergence J z) := by
    unfold originalStageCurrentDivergence
    fun_prop (disch := exact hJ.continuous_fderiv (by norm_num))
  have hdi : IntegrableOn (fun z ↦ originalStageCurrentDivergence J z) (originalCenteredPhysicalCubeRegion b (2*R)) :=
    hdivc.continuousOn.integrableOn_compact (isCompact_originalStagePhysicalCube b (2*R))
  have heq := setIntegral_congr_fun (μ := volume) (s := originalCenteredPhysicalCubeRegion b (2*R))
    (isCompact_originalStagePhysicalCube b (2*R)).measurableSet (fun z hz ↦ hread z hz)
  have hGG := originalScreeningPhysicalCurrent_gauss_green b hJ (show 0 ≤ 2*R by linarith)
    (show ContDiff ℝ 1 (fun _ : Fin q → ℝ ↦ (1:ℝ)) from contDiff_const)
  have hconst : originalScreeningPhysicalCurrentGradientPairing b J (2*R) (fun _ ↦ (1:ℝ)) = 0 := by
    simp [originalScreeningPhysicalCurrentGradientPairing]
  simp only [mul_one] at hGG
  unfold originalScreeningOrientedFullReflectedSlabDensity at heq
  change (∫ z in originalCenteredPhysicalCubeRegion b (2*R),
    (((fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
      (fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene)) +
      originalOrientedStageReflectedClassDensity b R (Ico s t) σS -
      originalOrientedStageReflectedClassDensity b R (Ioc s t) σT) z) =
    (∫ z in originalCenteredPhysicalCubeRegion b (2*R),
      ((fun z ↦ originalStageCurrentDivergence J z) +
        originalOrientedClassReflectedInputScalarField b η (2*R) (Ico s t) (legalInputColorMeasure q scene.2 0) -
        originalOrientedClassReflectedInputScalarField b η (2*R) (Ioc s t) (legalInputColorMeasure q scene.2 1)) z) at heq
  simp only [Pi.sub_apply, Pi.add_apply] at heq
  rw [integral_sub
      (f := fun z ↦ (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
        (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene) +
        originalOrientedStageReflectedClassDensity b R (Ico s t) σS z)
      (g := originalOrientedStageReflectedClassDensity b R (Ioc s t) σT)
      ((hcs.sub hct).add hs.1) ht.1,
    integral_add
      (f := fun z ↦ (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
        (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene))
      (g := originalOrientedStageReflectedClassDensity b R (Ico s t) σS) (hcs.sub hct) hs.1,
    integral_sub
      (f := fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene)
      (g := fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene) hcs hct,
    hs.2, ht.2,
    integral_sub
      (f := fun z ↦ originalStageCurrentDivergence J z +
        originalOrientedClassReflectedInputScalarField b η (2*R) (Ico s t) (legalInputColorMeasure q scene.2 0) z)
      (g := originalOrientedClassReflectedInputScalarField b η (2*R) (Ioc s t) (legalInputColorMeasure q scene.2 1))
      (hdi.add hzs) hzt,
    integral_add
      (f := fun z ↦ originalStageCurrentDivergence J z)
      (g := originalOrientedClassReflectedInputScalarField b η (2*R) (Ico s t) (legalInputColorMeasure q scene.2 0))
      hdi hzs, hGG] at heq
  unfold originalScreeningOrientedFullSlabCutError originalScreeningOrientedReflectedInputMass
  change _ = originalScreeningPhysicalCurrentBoundaryPairing b J (2*R) (fun _ ↦ 1) + _ - _
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
