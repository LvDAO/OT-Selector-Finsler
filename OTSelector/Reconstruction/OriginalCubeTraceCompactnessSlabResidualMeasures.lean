import OTSelector.Reconstruction.OriginalCubeTraceCompactnessPositiveSlabCharges
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessWeakSlabDivergence

/-! Genuine two positive residual measures of the original infinite-scene smoothed slab. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual original slab's nonnegative source charge plus incoming physical cut. -/
def originalSceneSlabResidualSource (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (s t : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalSceneSlabSourceMeasure s t scene + originalSceneActiveCutMeasure S w s scene

/-- The actual original slab's nonnegative target charge plus outgoing physical cut. -/
def originalSceneSlabResidualTarget (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (s t : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalSceneSlabTargetMeasure s t scene + originalSceneActiveCutMeasure S w t scene

/-- Both actual positive residual measures are locally finite under the original law,
using their proved source, target and active-cut Campbell local finiteness. -/
theorem ae_originalSceneSlabResidualMeasures_finiteOnCompacts
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasureOnCompacts (originalSceneSlabResidualSource S w s t scene) ∧
      IsFiniteMeasureOnCompacts (originalSceneSlabResidualTarget S w s t scene) := by
  filter_upwards [ae_originalSceneSlabCharges_finiteOnCompacts S hF hw Q s t]
    with scene hscene
  rcases hscene with ⟨hsrc, htgt, hs, ht⟩
  constructor
  · refine ⟨fun {K} hK ↦ ?_⟩
    change (originalSceneSlabSourceMeasure s t scene + originalSceneActiveCutMeasure S w s scene) K < _
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2
      ⟨hsrc.lt_top_of_isCompact hK, hs.lt_top_of_isCompact hK⟩
  · refine ⟨fun {K} hK ↦ ?_⟩
    change (originalSceneSlabTargetMeasure s t scene + originalSceneActiveCutMeasure S w t scene) K < _
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2
      ⟨htgt.lt_top_of_isCompact hK, ht.lt_top_of_isCompact hK⟩

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual original weak slab is exactly the difference of the two genuine nonnegative
locally finite residual measures, tested against every compact C¹ function. -/
theorem ae_all_originalWeakSlab_residualMeasure_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        ContDiff ℝ 1 φ → HasCompactSupport φ →
        -originalSeedPathWeakSlabReadout S w φ s t scene =
          (∫ x, φ x ∂originalSceneSlabResidualSource S w s t scene) -
            ∫ x, φ x ∂originalSceneSlabResidualTarget S w s t scene := by
  filter_upwards [ae_originalSceneSlabCharges_finiteOnCompacts S hF hw Q s t,
    D.ae_all_originalWeakSlab_positiveCharge_balance hF hw Q hst] with scene hfinite hbalance
  intro φ hφ hcφ
  have : IsFiniteMeasureOnCompacts (originalSceneSlabSourceMeasure s t scene) := hfinite.1
  have : IsFiniteMeasureOnCompacts (originalSceneSlabTargetMeasure s t scene) := hfinite.2.1
  have : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w s scene) := hfinite.2.2.1
  have : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w t scene) := hfinite.2.2.2
  have hsrc : Integrable φ (originalSceneSlabSourceMeasure s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have htgt : Integrable φ (originalSceneSlabTargetMeasure s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcuts : Integrable φ (originalSceneActiveCutMeasure S w s scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcutt : Integrable φ (originalSceneActiveCutMeasure S w t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  rw [originalSceneSlabResidualSource, originalSceneSlabResidualTarget,
    integral_add_measure hsrc hcuts, integral_add_measure htgt hcutt]
  linarith [hbalance φ hφ hcφ]

/-- The true original compact-kernel spatial divergence is the convolution readout of its
actual two positive residual measures. Local finiteness, path FTC, original slab balance and
current C¹ regularity are proved upstream, with no residual identity supplied as a premise. -/
theorem ae_all_smoothedClockSlab_divergence_eq_residualMeasures
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ z,
        (∑ i : Fin (finrank ℝ S.covector.ker),
          fderiv ℝ (fun z ↦ originalSeedPathClockSetCurrent S w
            (fun x ↦ η (x - z)) (Ioc s t) scene) z (Pi.single i 1) i) =
          (∫ x, η (x - z) ∂originalSceneSlabResidualSource S w s t scene) -
            ∫ x, η (x - z) ∂originalSceneSlabResidualTarget S w s t scene := by
  filter_upwards [D.ae_all_smoothedClockSlab_divergence_eq_weakSlab hF hw hbounds Q,
    D.ae_all_originalWeakSlab_residualMeasure_balance hF hw Q hst] with scene hdiv hbalance
  intro η hη hcη z
  have hφ : ContDiff ℝ 1 (fun x ↦ η (x - z)) := hη.comp (contDiff_id.sub contDiff_const)
  have hcφ : HasCompactSupport (fun x ↦ η (x - z)) := by
    simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hcη.comp_homeomorph (Homeomorph.addRight (-z))
  rw [hdiv η hη hcη s t hst z, hbalance _ hφ hcφ]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
