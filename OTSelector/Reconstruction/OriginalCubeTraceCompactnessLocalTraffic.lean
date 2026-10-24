import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! Actual locally finite absolute occupation of the same original complete paths. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm Module Manifold OTSelector.Probability
open scoped ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual original pair-anchor, unchanged paired mark, and physical clock. -/
abbrev OriginalClockOccupationPoint (S : CalibratedLevelSeedPatch F u) :=
  (((Fin (finrank ℝ S.covector.ker) → ℝ) ×
    PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) × ℝ)

/-- The actual original path position at the original physical clock. -/
def originalClockOccupationPosition (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (p : OriginalClockOccupationPoint S) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  p.1.1 + originalSeedPathOffset S w p.2 p.1.2

/-- The actual original clock-restricted velocity, before spatial smoothing. -/
def originalClockOccupationVelocity (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (p : OriginalClockOccupationPoint S) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedClockOccupation S w p.2 p.1.2

/-- The unchanged first physical plan's pair measure times the actual
restricted original clock measure. No source or target is spatially filtered. -/
def originalClockOccupationMeasure (S : CalibratedLevelSeedPatch F u) (A : Set ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (OriginalClockOccupationPoint S) :=
  (physicalScenePairKernel s.1).prod (volume.restrict A)

/-- Original positions and velocities remain measurable on the true occupation space. -/
theorem measurable_originalClockOccupationPosition
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (originalClockOccupationPosition S w) := by
  change Measurable (fun p : OriginalClockOccupationPoint S ↦
    p.1.1 + originalSeedPathOffset S w p.2 p.1.2)
  have hmc : Measurable (fun p : OriginalClockOccupationPoint S ↦ (p.1.2, p.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hd : Measurable (fun p : OriginalClockOccupationPoint S ↦
      originalSeedPathOffset S w p.2 p.1.2) := by
    change Measurable
      ((fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        originalSeedPathOffset S w z.2 z.1) ∘ (fun p : OriginalClockOccupationPoint S ↦ (p.1.2, p.2)))
    exact (measurable_originalSeedPathOffset_joint S hF hw).comp hmc
  exact measurable_fst.fst.add hd

theorem measurable_originalClockOccupationVelocity
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (originalClockOccupationVelocity S w) := by
  change Measurable (fun p : OriginalClockOccupationPoint S ↦
    originalSeedClockOccupation S w p.2 p.1.2)
  have hmc : Measurable (fun p : OriginalClockOccupationPoint S ↦ (p.1.2, p.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  change Measurable
    ((fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedClockOccupation S w z.2 z.1) ∘ (fun p : OriginalClockOccupationPoint S ↦ (p.1.2, p.2)))
  exact (measurable_originalSeedClockOccupation S hF hw).comp hmc

/-- The literal compact local absolute occupation is measurable. -/
theorem measurable_originalClockOccupation_compact_weight
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {B : Set (Fin (finrank ℝ S.covector.ker) → ℝ)} (hB : MeasurableSet B) :
    Measurable (fun p : OriginalClockOccupationPoint S ↦
      B.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
        (originalClockOccupationPosition S w p)) := by
  have h := (((measurable_const : Measurable (fun _ : Fin (finrank ℝ S.covector.ker) → ℝ ↦ (1 : ℝ))).indicator hB).comp
    (measurable_originalClockOccupationPosition S hF hw)).mul
      (measurable_originalClockOccupationVelocity S hF hw).norm
  convert h using 1
  funext p
  by_cases hp : originalClockOccupationPosition S w p ∈ B <;> simp [hp]

/-- Finite original absolute traffic through a compact observation set
produces genuine local L1 occupation for every actual clock restriction. -/
theorem integrable_originalClockOccupation_compact_weight_of_traffic_lt_top
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (A : Set ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    {B : Set (Fin (finrank ℝ S.covector.ker) → ℝ)} (hB : MeasurableSet B)
    (htraffic : originalSeedCompletePathAbsoluteTraffic S w (B.indicator (fun _ ↦ (1 : ℝ))) s < (∞ : ℝ≥0∞)) :
    Integrable (fun p : OriginalClockOccupationPoint S ↦
      B.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
        (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A s) := by
  have hη : Measurable (B.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hB
  have hpos := measurable_originalClockOccupationPosition S hF hw
  have hvel := measurable_originalClockOccupationVelocity S hF hw
  let H : OriginalClockOccupationPoint S → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal (B.indicator (fun _ ↦ (1 : ℝ)) (originalClockOccupationPosition S w p)) *
      ENNReal.ofReal ‖originalClockOccupationVelocity S w p‖
  have hH : Measurable H := (hη.comp hpos).ennreal_ofReal.mul hvel.norm.ennreal_ofReal
  have hnorm (p : OriginalClockOccupationPoint S) :
      ENNReal.ofReal ‖B.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
        (originalClockOccupationPosition S w p)‖ = H p := by
    by_cases hp : originalClockOccupationPosition S w p ∈ B <;>
      simp [H, hp]
  refine ⟨(measurable_originalClockOccupation_compact_weight S hF hw hB).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp_rw [hnorm]
  apply lt_of_le_of_lt ?_ htraffic
  rw [originalClockOccupationMeasure, lintegral_prod _ hH.aemeasurable]
  change (∫⁻ a : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)), (∫⁻ c : ℝ in A,
      ENNReal.ofReal (B.indicator (fun _ ↦ (1 : ℝ)) (a.1 + originalSeedPathOffset S w c a.2)) *
        ENNReal.ofReal ‖originalSeedClockOccupation S w c a.2‖ ∂volume)
      ∂physicalScenePairKernel s.1) ≤
    originalSeedCompletePathAbsoluteTraffic S w (B.indicator (fun _ ↦ (1 : ℝ))) s
  apply lintegral_mono
  intro a
  exact lintegral_mono' Measure.restrict_le_self le_rfl

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- A single full-measure set of original scenes has locally integrable absolute
occupation on every compact spatial set and every original clock restriction. -/
theorem ae_integrable_originalClockOccupation_compact_weight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ℝ) (B : Set (Fin (finrank ℝ S.covector.ker) → ℝ)), IsCompact B →
        Integrable (fun p : OriginalClockOccupationPoint S ↦
          B.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
            (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A s) := by
  have hballs (n : ℕ) :
      ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
        originalSeedCompletePathAbsoluteTraffic S w
          ((closedBall (0 : Fin (finrank ℝ S.covector.ker) → ℝ) (n : ℝ)).indicator
            (fun _ ↦ (1 : ℝ))) s < (∞ : ℝ≥0∞) := by
    apply D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q
    · exact measurable_const.indicator measurableSet_closedBall
    · exact (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne).integrable_indicator
        measurableSet_closedBall
  filter_upwards [ae_all_iff.mpr hballs] with s hs
  intro A B hB
  obtain ⟨r, hr⟩ := hB.isBounded.subset_closedBall (0 : Fin (finrank ℝ S.covector.ker) → ℝ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hBn : B ⊆ closedBall (0 : Fin (finrank ℝ S.covector.ker) → ℝ) (n : ℝ) :=
    hr.trans (closedBall_subset_closedBall hn.le)
  have hint := integrable_originalClockOccupation_compact_weight_of_traffic_lt_top S hF hw A s
    measurableSet_closedBall (hs n)
  refine hint.mono' (measurable_originalClockOccupation_compact_weight S hF hw
    hB.measurableSet).aestronglyMeasurable ?_
  filter_upwards with p
  by_cases hp : originalClockOccupationPosition S w p ∈ B
  · simp [hp, hBn hp]
  · simp only [indicator_of_notMem hp, norm_zero]
    exact indicator_nonneg (fun _ _ ↦ norm_nonneg _) _

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
