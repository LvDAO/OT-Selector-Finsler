import OTSelector.Reconstruction.OriginalRetainedSlabResidualOmitted

/-! Measurability and genuine local integrability of the actual omitted-cut density. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A measurable test of a literal selected original positive position measure is a
measurable function of the unchanged original scene. -/
theorem measurable_integral_originalRestrictedPositionMeasure {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    {φ : (Fin q → ℝ) → ℝ} (hφ : Measurable φ) :
    Measurable (fun scene : LegalMarkedOptimalInputScene q ↦
      ∫ x, φ x ∂originalRestrictedSceneMarkedPositionMeasure A d B scene) := by
  let H : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) → ℝ :=
    {a | a.2 ∈ B}.indicator (fun a ↦ φ (a.1 + d a.2))
  have hH : Measurable H :=
    (hφ.comp (measurable_fst.add (hd.comp measurable_snd))).indicator
      (hB.preimage measurable_snd)
  have hread := (hH.indicator hA).stronglyMeasurable.integral_kernel
    (κ := physicalScenePairKernel)
  convert hread.measurable.comp measurable_fst using 1
  funext scene
  rw [integral_originalRestrictedPositionMeasure_eq_readout A hd hB scene
    hφ.stronglyMeasurable]
  exact (integral_indicator hA).symm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual raw omitted-cut density is a Borel readout of the original scene. -/
theorem measurable_originalOmittedCutDensity (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    (R ell c : ℝ) {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    Measurable (originalOmittedCutDensity S w R ell c η z) := by
  exact measurable_integral_originalRestrictedPositionMeasure
    (measurableSet_originalPathLengthRetained S hF hw R ell).compl
    (measurable_originalSeedPathOffset S hF hw c)
    ((measurableSet_lt measurable_fst.fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_fst.snd))
    (hη.comp (measurable_id.sub_const z))

/-- On one original-scene event all continuous compact kernels defining this positive
omitted-cut density are genuinely integrable, simultaneously at every spatial observation. -/
theorem ae_all_integrable_originalOmittedCutDensity (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (R ell c : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        Continuous η → HasCompactSupport η →
        ∀ z, Integrable (fun x ↦ η (x - z))
          (originalOmittedSceneActiveCutMeasure S w R ell c scene) := by
  filter_upwards [Q.ae_originalRestrictedPositionMeasure_finiteOnCompacts
    (originalPathLengthRetained S w R ell)ᶜ (measurable_originalSeedPathOffset S hF hw c)
    ((measurableSet_lt measurable_fst.fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_fst.snd))] with scene hscene
  intro η hη hcη z
  have : IsFiniteMeasureOnCompacts (originalOmittedSceneActiveCutMeasure S w R ell c scene) :=
    hscene
  have hc : HasCompactSupport (fun x ↦ η (x - z)) := by
    simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hcη.comp_homeomorph (Homeomorph.addRight (-z))
  exact (hη.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport hc

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The restricted weak slab is exactly the literal original clock-occupation derivative
readout. Retained and omitted paths keep the same actual clocks, velocities and positions. -/
theorem ae_all_originalRestrictedClockSlab_testDerivative_eq_weakSlab
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
          PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
        (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (s t : ℝ), s ≤ t →
        (∫ a in A, (∫ c in Ioc s t,
          fderiv ℝ φ (a.1 + originalSeedPathOffset S w c a.2)
            (originalSeedClockOccupation S w c a.2) ∂volume)
          ∂physicalScenePairKernel scene.1) =
          originalRestrictedSeedPathWeakSlabReadout S w A φ s t scene := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hscene
  intro A φ s t hst
  unfold originalRestrictedSeedPathWeakSlabReadout originalSeedSlabPairDerivativeIntegral
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hscene] with a ha
  simpa only [originalSeedCompletePath_eq_anchor_add_offset] using
    integral_originalClockOccupation_testDerivative_eq_clipped S w a.1 a.2 ha.2.2.le hst φ

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
