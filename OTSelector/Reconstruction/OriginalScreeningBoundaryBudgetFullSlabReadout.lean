import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetFullInputs
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetGaussGreen

/-! The actual complete current and full Poisson reflected inputs give the original cut residual. -/
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

/-- The literal full-input reflected slab density, including both actual incoming and
outgoing full cut occupations. Its original endpoints use [s,t) and (s,t]. -/
def originalScreeningFullReflectedSlabDensity (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  (∫ x, originalEuclideanMollifier _ (x-z) ∂originalSceneActiveCutMeasure S w s scene) -
  (∫ x, originalEuclideanMollifier _ (x-z) ∂originalSceneActiveCutMeasure S w t scene) +
  originalStageReflectedClassDensity (originalEuclideanMollifier _) R (Ico s t)
    ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}) z -
  originalStageReflectedClassDensity (originalEuclideanMollifier _) R (Ioc s t)
    ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}) z

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The same actual complete current divergence plus its two actual full-input reflected
errors is the literal full reflected slab density. The endpoint marginal identities and
positive-cut FTC are internal, including both physical half-slab conventions. -/
theorem ae_all_originalScreening_fullReflectedSlab_eq_divergence_add_inputErrors
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {R : ℝ} (hR : 1 ≤ R) {s t : ℝ} (hst : s ≤ t) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ z ∈ haarRootCube _ R,
      originalScreeningFullReflectedSlabDensity S w R s t scene z =
        originalStageCurrentDivergence
          (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene) z +
        originalClassReflectedInputScalarField η R (Ico s t)
          (legalInputColorMeasure _ scene.2 0) z -
        originalClassReflectedInputScalarField η R (Ioc s t)
          (legalInputColorMeasure _ scene.2 1) z := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
  have hη : ContDiff ℝ 1 η := (contDiff_originalEuclideanMollifier _).of_le (by norm_num)
  have hcη : HasCompactSupport η := hasCompactSupport_originalEuclideanMollifier _
  have hηm : Measurable η := hη.continuous.measurable
  have hsupport := raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range
    (finrank ℝ S.covector.ker))
  have heven (x y : Fin (finrank ℝ S.covector.ker) → ℝ) : η (x-y) = η (y-x) := by
    apply coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial _)
    intro i
    simp only [Pi.sub_apply, abs_sub_comm]
  filter_upwards [Q.full_matching,
    Q.ae_finite_reflectedInputOuterWindow R 0, Q.ae_finite_reflectedInputOuterWindow R 1,
    D.ae_all_smoothedClockSlab_divergence_eq_weakSlab hF hw hbounds Q,
    D.ae_all_originalWeakSlab_positiveCharge_balance hF hw Q hst]
      with scene hfull hfinS hfinT hdiv hbalance
  intro z hz
  have hψ : ContDiff ℝ 1 (fun x ↦ η (x-z)) := hη.comp (contDiff_id.sub contDiff_const)
  have hcψ : HasCompactSupport (fun x ↦ η (x-z)) := by
    simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hcη.comp_homeomorph (Homeomorph.addRight (-z))
  have hd := (hdiv η hη hcη s t hst z).trans (hbalance _ hψ hcψ)
  have hsrc : (∫ x, η (x-z) ∂originalSceneSlabSourceMeasure s t scene) =
      ∫ p in {p | p.2 ∈ Ico s t}, η (z-p.1) ∂legalInputColorMeasure _ scene.2 0 := by
    rw [originalSceneSlabSourceMeasure_eq_fullInput hfull]
    rw [integral_map_of_stronglyMeasurable (f := fun x ↦ η (x-z)) measurable_fst
      (show StronglyMeasurable (fun x ↦ η (x-z)) from
        (hηm.comp (measurable_id.sub_const z)).stronglyMeasurable)]
    exact integral_congr_ae (Eventually.of_forall (fun p ↦ heven p.1 z))
  have htgt : (∫ x, η (x-z) ∂originalSceneSlabTargetMeasure s t scene) =
      ∫ p in {p | p.2 ∈ Ioc s t}, η (z-p.1) ∂legalInputColorMeasure _ scene.2 1 := by
    rw [originalSceneSlabTargetMeasure_eq_fullInput hfull]
    rw [integral_map_of_stronglyMeasurable (f := fun x ↦ η (x-z)) measurable_fst
      (show StronglyMeasurable (fun x ↦ η (x-z)) from
        (hηm.comp (measurable_id.sub_const z)).stronglyMeasurable)]
    exact integral_congr_ae (Eventually.of_forall (fun p ↦ heven p.1 z))
  have hS := originalFullInputReflectedClassDensity_eq_raw_add_response (C := Ico s t) hηm
    (originalEuclideanMollifierBound_nonneg _) (abs_originalEuclideanMollifier_le _)
    hsupport hR measurableSet_Ico (legalInputColorMeasure _ scene.2 0) hfinS hz
  have hT := originalFullInputReflectedClassDensity_eq_raw_add_response (C := Ioc s t) hηm
    (originalEuclideanMollifierBound_nonneg _) (abs_originalEuclideanMollifier_le _)
    hsupport hR measurableSet_Ioc (legalInputColorMeasure _ scene.2 1) hfinT hz
  rw [hsrc, htgt] at hd
  unfold originalScreeningFullReflectedSlabDensity
  change _ = (∑ i, fderiv ℝ
    (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene) z
      (Pi.single i 1) i) + _ - _
  rw [hS, hT]
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
