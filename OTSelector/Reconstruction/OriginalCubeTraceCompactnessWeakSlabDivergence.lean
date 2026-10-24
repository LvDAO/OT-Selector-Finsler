import OTSelector.Reconstruction.OriginalCurrentSmoothedDivergence
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessClockSlabFTC

/-! True smoothed divergence equals the original infinite-scene weak slab and path cuts. -/
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
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The true integrable kernel-gradient pairing over original pair-times-clock occupation
is the old weak slab readout of the same infinite original plan, by actual Fubini and clock
occupation. No weak divergence or finite-edge formula is supplied as an assumption. -/
theorem ae_all_originalClockOccupation_gradientPairing_eq_weakSlab
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ (s t : ℝ), s ≤ t → ∀ z,
        (∫ p : OriginalClockOccupationPoint S,
          fderiv ℝ η (originalClockOccupationPosition S w p - z)
            (originalClockOccupationVelocity S w p)
            ∂originalClockOccupationMeasure S (Ioc s t) scene) =
          originalSeedPathWeakSlabReadout S w (fun x ↦ η (x - z)) s t scene := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q,
    D.ae_all_originalClockSlab_testDerivative_eq_weakSlab Q] with scene htraffic hweak
  intro η hη hcη s t hst z
  have hi := integrable_compact_kernel_gradientPairing hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (σ := originalClockOccupationMeasure S (Ioc s t) scene)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
    (htraffic (Ioc s t)) z
  calc
    _ = ∫ a, (∫ c in Ioc s t,
        fderiv ℝ η (a.1 + originalSeedPathOffset S w c a.2 - z)
          (originalSeedClockOccupation S w c a.2) ∂volume)
        ∂physicalScenePairKernel scene.1 := integral_prod _ hi
    _ = _ := by simpa only [fderiv_comp_sub] using hweak (fun x ↦ η (x - z)) s t hst

/-- The genuine derivative of the same smoothed original current has exactly the negative
original weak-slab readout. This identifies the actual spatial divergence and path residual. -/
theorem ae_all_smoothedClockSlab_divergence_eq_weakSlab
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ (s t : ℝ), s ≤ t → ∀ z,
        (∑ i : Fin (finrank ℝ S.covector.ker),
          fderiv ℝ (fun z ↦ originalSeedPathClockSetCurrent S w
            (fun x ↦ η (x - z)) (Ioc s t) scene) z (Pi.single i 1) i) =
          -originalSeedPathWeakSlabReadout S w (fun x ↦ η (x - z)) s t scene := by
  filter_upwards [D.ae_all_divergence_originalClockSetCurrent_spatial hF hw hbounds Q,
    D.ae_all_originalClockOccupation_gradientPairing_eq_weakSlab hF hw hbounds Q]
    with scene hdiv hweak
  intro η hη hcη s t hst z
  rw [hdiv (Ioc s t) η hη hcη z, hweak η hη hcη s t hst z]

/-- Actual original smoothed divergence equals the negative signed difference of the two
true original path cut evaluations under the unchanged infinite scene pair kernel. -/
theorem ae_all_smoothedClockSlab_divergence_eq_endpoints
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ (s t : ℝ), s ≤ t → ∀ z,
        (∑ i : Fin (finrank ℝ S.covector.ker),
          fderiv ℝ (fun z ↦ originalSeedPathClockSetCurrent S w
            (fun x ↦ η (x - z)) (Ioc s t) scene) z (Pi.single i 1) i) =
          -(∫ a, (η (originalSeedCompletePath S w a.1 a.2
              (max a.2.1.1 (min t a.2.1.2)) - z) -
            η (originalSeedCompletePath S w a.1 a.2
              (max a.2.1.1 (min s a.2.1.2)) - z)) ∂physicalScenePairKernel scene.1) := by
  filter_upwards [D.ae_all_smoothedClockSlab_divergence_eq_weakSlab hF hw hbounds Q,
    D.ae_all_originalClockSlab_testDerivative_eq_weakSlab Q,
    D.ae_all_originalClockSlab_testDerivative_eq_endpoints hF hw Q] with scene hdiv hweak hFTC
  intro η hη hcη s t hst z
  have hφ : ContDiff ℝ 1 (fun x ↦ η (x - z)) := hη.comp (contDiff_id.sub contDiff_const)
  rw [hdiv η hη hcη s t hst z,
    ← hweak (fun x ↦ η (x - z)) s t hst, hFTC _ hφ s t hst]

/-- The actual signed two-cut evaluation is genuinely L1 under the original infinite pair
kernel. Its integrability comes from differentiated compact-kernel local traffic and FTC. -/
theorem ae_all_integrable_originalClockSlab_endpointDifference
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ (s t : ℝ), s ≤ t → ∀ z,
        Integrable (fun a ↦
          η (originalSeedCompletePath S w a.1 a.2 (max a.2.1.1 (min t a.2.1.2)) - z) -
            η (originalSeedCompletePath S w a.1 a.2 (max a.2.1.1 (min s a.2.1.2)) - z))
          (physicalScenePairKernel scene.1) := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q,
    D.ae_ae_original_pairKernel_interior_forward Q] with scene htraffic hlegal
  intro η hη hcη s t hst z
  have hi := integrable_compact_kernel_gradientPairing hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (σ := originalClockOccupationMeasure S (Ioc s t) scene)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
    (htraffic (Ioc s t)) z
  have hφ : ContDiff ℝ 1 (fun x ↦ η (x - z)) := hη.comp (contDiff_id.sub contDiff_const)
  refine hi.integral_prod_left.congr ?_
  filter_upwards [hlegal] with a ha
  simpa only [originalClockOccupationPosition, originalClockOccupationVelocity,
    originalSeedCompletePath_eq_anchor_add_offset, fderiv_comp_sub] using
    D.integral_originalClockOccupation_testDerivative_eq_endpoints hF hw a.1 a.2
      ha.1 ha.2.1 ha.2.2.le hst hφ

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
