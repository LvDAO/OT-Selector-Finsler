import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetFullSlabReadout
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetInputMassVariance
import OTSelector.Reconstruction.OriginalStageResidualDensityCutIntegrability

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
def originalScreeningFullSlabCutError (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}).real {p | p.2 ∈ Ico s t} -
  ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}).real {p | p.2 ∈ Ioc s t} +
  (∫ z in haarRootCube _ R, ∫ x, originalEuclideanMollifier _ (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
  (∫ z in haarRootCube _ R, ∫ x, originalEuclideanMollifier _ (x-z) ∂originalSceneActiveCutMeasure S w t scene)

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual positive-slab FTC, reflection mass preservation and true current Gauss-Green
identify the unchanged full cut/count error with the literal full-current face flux and
both same-scene full-input boundary masses. There is no supplied flux identity. -/
theorem ae_originalScreening_fullSlabCutError_eq_flux_add_inputMasses
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {R : ℝ} (hR : 1 ≤ R) {s t : ℝ} (hst : s ≤ t) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalScreeningFullSlabCutError S w R s t scene =
        originalStageAxisBoundaryPairing
          (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene) R (fun _ ↦ 1) +
        originalScreeningReflectedInputMass R (Ico s t) 0 scene -
        originalScreeningReflectedInputMass R (Ioc s t) 1 scene := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  have hη : ContDiff ℝ 1 η := (contDiff_originalEuclideanMollifier q).of_le (by norm_num)
  have hcη : HasCompactSupport η := hasCompactSupport_originalEuclideanMollifier q
  have hmη := hη.continuous.measurable
  have hsupport := raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)
  have hηI := integrable_originalEuclideanMollifier q
  have hmass := integral_originalEuclideanMollifier_eq_one q
  have heven := coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q)
  have hM := originalEuclideanMollifierBound_nonneg q
  have hbound := abs_originalEuclideanMollifier_le q
  filter_upwards [D.ae_all_originalScreening_fullReflectedSlab_eq_divergence_add_inputErrors hF hw hbounds Q hR hst,
    ae_originalSceneSlabCharges_finiteOnCompacts S hF hw Q s t,
    Q.ae_finite_reflectedInputOuterWindow R 0, Q.ae_finite_reflectedInputOuterWindow R 1,
    D.ae_all_originalClockSetCurrent_spatially_contDiff hF hw hbounds Q]
      with scene hread hcharges hfinS hfinT hcurrent
  let σS := (legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ haarRootCube (Fin q) R}
  let σT := (legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ haarRootCube (Fin q) R}
  have hW : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} :=
    measurableSet_Icc.preimage measurable_fst
  have hwindow : {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} ⊆
      haarRootCube (Fin q) (R+1) ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨⟨fun i ↦ by linarith [hp.1 i], fun i ↦ by linarith [hp.2 i]⟩, mem_univ _⟩
  let : IsFiniteMeasure σS := ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hwindow).trans_lt hfinS⟩
  let : IsFiniteMeasure σT := ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hwindow).trans_lt hfinT⟩
  have hs := originalStageReflectedClassDensity_integrable_mass hmη hηI hmass hsupport heven hbound hR σS
    (ae_restrict_mem hW) (Ico s t)
  have ht := originalStageReflectedClassDensity_integrable_mass hmη hηI hmass hsupport heven hbound hR σT
    (ae_restrict_mem hW) (Ioc s t)
  let : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w s scene) := hcharges.2.2.1
  let : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w t scene) := hcharges.2.2.2
  have hcs := integrable_cube_compactKernel_smoothing (originalSceneActiveCutMeasure S w s scene)
    hmη hbound hsupport (show 0 ≤ R by linarith)
  have hct := integrable_cube_compactKernel_smoothing (originalSceneActiveCutMeasure S w t scene)
    hmη hbound hsupport (show 0 ≤ R by linarith)
  have hzs := integrable_originalClassReflectedInputScalarField_mul_of_finite_outer (C := Ico s t) hmη hM hbound
    hsupport hR measurableSet_Ico (legalInputColorMeasure q scene.2 0) hfinS (u := fun _ ↦ (1:ℝ)) continuous_const
  have hzt := integrable_originalClassReflectedInputScalarField_mul_of_finite_outer (C := Ioc s t) hmη hM hbound
    hsupport hR measurableSet_Ioc (legalInputColorMeasure q scene.2 1) hfinT (u := fun _ ↦ (1:ℝ)) continuous_const
  simp only [mul_one] at hzs hzt
  let J := fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene
  have hJ : ContDiff ℝ 1 J := hcurrent (Ioc s t) η hη hcη
  have hdivc : Continuous (fun z ↦ originalStageCurrentDivergence J z) := by
    unfold originalStageCurrentDivergence
    fun_prop (disch := exact hJ.continuous_fderiv (by norm_num))
  have hdi : IntegrableOn (fun z ↦ originalStageCurrentDivergence J z) (haarRootCube (Fin q) R) :=
    hdivc.continuousOn.integrableOn_Icc
  have heq := setIntegral_congr_fun (μ := volume) (s := haarRootCube (Fin q) R) measurableSet_Icc (fun z hz ↦ hread z hz)
  have hGG := originalStageCurrent_gauss_green hJ (show 0 ≤ R by linarith)
    (show ContDiff ℝ 1 (fun _ : Fin q → ℝ ↦ (1:ℝ)) from contDiff_const)
  have hconst : originalStageCurrentGradientPairing J R (fun _ ↦ (1:ℝ)) = 0 := by
    simp [originalStageCurrentGradientPairing]
  simp only [mul_one, hconst, sub_zero] at hGG
  unfold originalScreeningFullReflectedSlabDensity at heq
  change (∫ z in haarRootCube (Fin q) R,
    (((fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
      (fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene)) +
      originalStageReflectedClassDensity η R (Ico s t) σS -
      originalStageReflectedClassDensity η R (Ioc s t) σT) z) =
    (∫ z in haarRootCube (Fin q) R,
      ((fun z ↦ originalStageCurrentDivergence J z) +
        originalClassReflectedInputScalarField η R (Ico s t) (legalInputColorMeasure q scene.2 0) -
        originalClassReflectedInputScalarField η R (Ioc s t) (legalInputColorMeasure q scene.2 1)) z) at heq
  simp only [Pi.sub_apply, Pi.add_apply] at heq
  rw [integral_sub
      (f := fun z ↦ (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
        (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene) +
        originalStageReflectedClassDensity η R (Ico s t) σS z)
      (g := originalStageReflectedClassDensity η R (Ioc s t) σT)
      ((hcs.sub hct).add hs.1) ht.1,
    integral_add
      (f := fun z ↦ (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
        (∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene))
      (g := originalStageReflectedClassDensity η R (Ico s t) σS) (hcs.sub hct) hs.1,
    integral_sub
      (f := fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w s scene)
      (g := fun z ↦ ∫ x, η (x-z) ∂originalSceneActiveCutMeasure S w t scene) hcs hct,
    hs.2, ht.2,
    integral_sub
      (f := fun z ↦ originalStageCurrentDivergence J z +
        originalClassReflectedInputScalarField η R (Ico s t) (legalInputColorMeasure q scene.2 0) z)
      (g := originalClassReflectedInputScalarField η R (Ioc s t) (legalInputColorMeasure q scene.2 1))
      (hdi.add hzs) hzt,
    integral_add
      (f := fun z ↦ originalStageCurrentDivergence J z)
      (g := originalClassReflectedInputScalarField η R (Ico s t) (legalInputColorMeasure q scene.2 0))
      hdi hzs, hGG] at heq
  unfold originalScreeningFullSlabCutError originalScreeningReflectedInputMass
  change _ = originalStageAxisBoundaryPairing J R (fun _ ↦ 1) + _ - _
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
