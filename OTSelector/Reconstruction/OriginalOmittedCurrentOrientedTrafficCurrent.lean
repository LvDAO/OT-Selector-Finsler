import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeRestricted
import OTSelector.Reconstruction.OriginalOmittedCurrentEnergyComparison
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficDensityLimit

/-! Actual oriented omitted fields and their genuine restricted-current energy comparison. -/
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

/-- For every measurable actual pair restriction, full minus that literal restricted
current equals the complementary literal current. Integrability comes from full traffic. -/
theorem originalFull_sub_pairRestrictedCurrent_eq_compl
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (B) (hB : MeasurableSet B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) A scene -
        originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene =
      originalPairRestrictedSeedPathClockSetCurrent S w Bᶜ (fun x ↦ η (x-z)) A scene := by
  have hi := integrable_originalPairRestrictedClockOccupation_spatialKernel S hF hw hη hcη
    B A scene htraffic z
  have hic := integrable_originalPairRestrictedClockOccupation_spatialKernel S hF hw hη hcη
    Bᶜ A scene htraffic z
  have hsum := integral_add_measure hi hic
  rw [originalPairRestrictedClockOccupationMeasure_add_compl S B hB] at hsum
  rw [← integral_originalClockOccupation_spatialKernel_eq_current S hF hw hη hcη A scene htraffic z,
    ← integral_originalPairRestrictedClockOccupation_spatialKernel_eq_current S hF hw hη hcη
      B A scene htraffic z,
    ← integral_originalPairRestrictedClockOccupation_spatialKernel_eq_current S hF hw hη hcη
      Bᶜ A scene htraffic z, hsum, add_sub_cancel_left]

/-- The actual same-frame omitted clock current is literally the original full current
minus the current of the same-frame retained original pairs. -/
def originalOrientedOmittedSeedPathClockSetCurrent (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedPathClockSetCurrent S w η A scene -
    originalPairRestrictedSeedPathClockSetCurrent S w
      (originalOrientedPathLengthRetained S w b R ell) η A scene

/-- The same-frame actual omitted field is jointly measurable in scene and spatial position. -/
theorem measurable_originalOrientedOmittedCurrent_joint_spatial
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) (A : Set ℝ) :
    Measurable (fun p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
      originalOrientedOmittedSeedPathClockSetCurrent S w b R ell (fun x ↦ η (x-p.2)) A p.1) :=
  ((stronglyMeasurable_originalFullCurrent_joint_spatial S hF hw hη A).sub
    (stronglyMeasurable_originalPairRestrictedCurrent_joint_spatial S hF hw hη
      (originalOrientedPathLengthRetained S w b R ell)
      (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell) A)).measurable

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual complementary-current Euclidean energy on any spatial region is bounded
by dimension times genuine complementary complete-path square traffic. -/
theorem lintegral_originalPairComplementCurrent_euclidean_sq_le_traffic_sq
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (B) (hB : MeasurableSet B) (A : Set ℝ)
    (W : Set (Fin (finrank ℝ S.covector.ker) → ℝ)) :
    let q := finrank ℝ S.covector.ker
    let η := originalEuclideanMollifier q
    (∫⁻ scene, ∫⁻ z in W, ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin q) ℝ).symm
      (originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) A scene -
        originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene)‖^2)
      ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
    ENNReal.ofReal (q:ℝ) * (∫⁻ scene, ∫⁻ z in W,
      originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) Bᶜ scene ^ 2
      ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) := by
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  calc
    _ ≤ ∫⁻ scene, ∫⁻ z in W, ENNReal.ofReal (q:ℝ) *
        originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) Bᶜ scene ^ 2
        ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_all_originalPairRestrictedCurrent_norm_le_traffic hF hw hbounds Q,
        D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q] with scene hs ht
      apply lintegral_mono
      intro z
      change ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin q) ℝ).symm
        (originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) A scene -
          originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene)‖^2) ≤
        ENNReal.ofReal (q:ℝ) *
          originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) Bᶜ scene ^ 2
      rw [originalFull_sub_pairRestrictedCurrent_eq_compl S hF hw
        (contDiff_originalEuclideanMollifier q).continuous
        (hasCompactSupport_originalEuclideanMollifier q) B hB A scene (ht A) z]
      have hb := hs Bᶜ A η (contDiff_originalEuclideanMollifier q).continuous
        (hasCompactSupport_originalEuclideanMollifier q) (originalEuclideanMollifier_nonneg q) z
      have hn := originalEuclidean_norm_sq_le_dim_mul_raw_norm_sq
        (originalPairRestrictedSeedPathClockSetCurrent S w Bᶜ (fun x ↦ η (x-z)) A scene)
      have ht := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hb.2 2) (Nat.cast_nonneg q)
      apply (ENNReal.ofReal_le_ofReal (hn.trans ht)).trans_eq
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg q), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hb.1.ne]
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
