import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridge
import OTSelector.Reconstruction.OriginalRetainedPathTraffic

/-! The same actual omitted current is bounded by its original omitted absolute traffic. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual complete-clock product norm integral is exactly restricted absolute traffic. -/
theorem lintegral_originalPairRestrictedClockOccupation_spatialKernel_norm_eq_traffic
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) (B)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (∫⁻ p : OriginalClockOccupationPoint S,
      ‖η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p‖ₑ
      ∂originalPairRestrictedClockOccupationMeasure S B univ scene) =
    originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) B scene := by
  have hm : Measurable (fun p : OriginalClockOccupationPoint S ↦
      ENNReal.ofReal (η (originalClockOccupationPosition S w p - z)) *
        ENNReal.ofReal ‖originalClockOccupationVelocity S w p‖) :=
    (hη.comp ((measurable_originalClockOccupationPosition S hF hw).sub measurable_const)).ennreal_ofReal.mul
      (measurable_originalClockOccupationVelocity S hF hw).norm.ennreal_ofReal
  calc
    _ = ∫⁻ p : OriginalClockOccupationPoint S,
        ENNReal.ofReal (η (originalClockOccupationPosition S w p - z)) *
          ENNReal.ofReal ‖originalClockOccupationVelocity S w p‖
        ∂originalPairRestrictedClockOccupationMeasure S B univ scene := by
      apply lintegral_congr_ae
      filter_upwards with p
      rw [← ofReal_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (hη0 _), ENNReal.ofReal_mul (hη0 _)]
    _ = _ := by
      rw [originalPairRestrictedClockOccupationMeasure, Measure.restrict_univ,
        lintegral_prod _ hm.aemeasurable]
      rfl

/-- Every clock restriction of the actual restricted current is dominated by its unchanged
complete-path absolute traffic. This extended-real estimate requires no integrability oracle. -/
theorem originalPairRestrictedClockOccupation_spatialKernel_enorm_le_traffic
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) (B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    ‖∫ p : OriginalClockOccupationPoint S,
      η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
      ∂originalPairRestrictedClockOccupationMeasure S B A scene‖ₑ ≤
    originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) B scene := by
  calc
    _ ≤ ∫⁻ p : OriginalClockOccupationPoint S,
        ‖η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p‖ₑ
        ∂originalPairRestrictedClockOccupationMeasure S B A scene :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ p : OriginalClockOccupationPoint S,
        ‖η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p‖ₑ
        ∂originalPairRestrictedClockOccupationMeasure S B univ scene := by
      apply lintegral_mono' ?_ le_rfl
      unfold originalPairRestrictedClockOccupationMeasure
      rw [Measure.restrict_univ]
      exact Measure.prod_mono le_rfl Measure.restrict_le_self
    _ = _ := lintegral_originalPairRestrictedClockOccupation_spatialKernel_norm_eq_traffic
      S hF hw hη hη0 B scene z

/-- Original compact local traffic makes actual restricted traffic finite, internally. -/
theorem originalPairRestrictedClockOccupation_spatialKernel_traffic_lt_top
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) (B)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S univ scene))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) B scene < ⊤ := by
  rw [← lintegral_originalPairRestrictedClockOccupation_spatialKernel_norm_eq_traffic
    S hF hw hη.measurable hη0 B scene z]
  exact hasFiniteIntegral_iff_enorm.mp
    (integrable_originalPairRestrictedClockOccupation_spatialKernel S hF hw hη hcη
      B univ scene htraffic z).hasFiniteIntegral

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- On the same original local-traffic event, every actual omitted current is bounded by
the genuine omitted complete-path traffic, whose finiteness is also derived internally. -/
theorem ae_all_originalOmittedCurrent_norm_le_traffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (R ell : ℝ) (A : Set ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        Continuous η → HasCompactSupport η → (∀ x, 0 ≤ η x) → ∀ z,
        originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z))
            (originalPathLengthRetained S w R ell)ᶜ scene < ⊤ ∧
        ‖originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) A scene -
          originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-z)) A scene‖ ≤
          (originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z))
            (originalPathLengthRetained S w R ell)ᶜ scene).toReal := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q]
    with scene hs
  intro R ell A η hη hcη hη0 z
  have ht := originalPairRestrictedClockOccupation_spatialKernel_traffic_lt_top S hF hw
    hη hcη hη0 (originalPathLengthRetained S w R ell)ᶜ scene (hs univ) z
  refine ⟨ht, ?_⟩
  rw [originalFull_sub_retainedCurrent_eq_omittedOccupation S hF hw R ell hη hcη A scene (hs A) z]
  simpa only [toReal_enorm] using ENNReal.toReal_mono ht.ne
    (originalPairRestrictedClockOccupation_spatialKernel_enorm_le_traffic S hF hw
      hη.measurable hη0 (originalPathLengthRetained S w R ell)ᶜ A scene z)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
