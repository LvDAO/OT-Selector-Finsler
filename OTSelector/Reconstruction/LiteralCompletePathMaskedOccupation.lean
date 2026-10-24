import OTSelector.Reconstruction.OriginalCompletePathEdgeTraffic
import OTSelector.Reconstruction.FinslerOriginalPathMeasurability
import OTSelector.Reconstruction.OriginalMaskedOneEdgeTraffic

/-! The physical one-edge estimate bounds literal original complete-path edge traffic. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Literal original edge traffic with its true physical speed and an arbitrary edge-clock mask. -/
def originalMaskedCompletePathEdgeTraffic (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) e

/-- The literal readout is the original complete path's full physical-clock occupation. -/
theorem originalMaskedCompletePathEdgeTraffic_eq_lintegral
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    originalMaskedCompletePathEdgeTraffic S w η mask e =
      ∫⁻ c : ℝ, ENNReal.ofReal
          (η (originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 c)) *
        ENNReal.ofReal ‖originalSeedClockOccupation S w c (physicalPairAnchor e).2‖ *
          mask ((physicalPairAnchor e).2, c) := by
  simp only [originalMaskedCompletePathEdgeTraffic, legalMarkedCompletePathEdgeTraffic,
    originalSeedCompletePath_eq_anchor_add_offset, mul_assoc]
  rfl

/-- A mask supported in the actual clock band restricts the full integral exactly,
without requiring mask measurability or changing the original path. -/
theorem originalMaskedCompletePathEdgeTraffic_eq_setLIntegral
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (l r : ℝ)
    (hmaskZero : ∀ c ∉ Icc l r, mask ((physicalPairAnchor e).2, c) = 0) :
    originalMaskedCompletePathEdgeTraffic S w η mask e =
      ∫⁻ c in Icc l r, ENNReal.ofReal
          (η (originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 c)) *
        ENNReal.ofReal ‖originalSeedClockOccupation S w c (physicalPairAnchor e).2‖ *
          mask ((physicalPairAnchor e).2, c) := by
  rw [originalMaskedCompletePathEdgeTraffic_eq_lintegral]
  apply (setLIntegral_eq_of_support_subset ?_).symm
  intro c hc
  by_contra hn
  exact hc (by simp only [hmaskZero c hn, mul_zero])

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- An existing actual physical cone bounds the literal full-clock edge traffic,
including both its min-one estimate and the uniform real occupation bound. -/
theorem original_maskedCompletePathEdgeTraffic_bound_of_physicalCone
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 - S.level ∈ Ioo D.lo D.hi)
    {l r R M : ℝ} (hlr : l ≤ r) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hclock : ∀ c ∈ Icc l r, c - S.level ∈ Ioo D.lo D.hi)
    {v : Fin (finrank ℝ S.covector.ker) → ℝ}
    (hcone : ∀ c ∈ Icc l r,
      ‖originalSeedKernel S w (c - S.level) *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor e).2 - v‖ ≤ ‖v‖ / 4)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη0 : ∀ x, 0 ≤ η x) (hηM : ∀ x, η x ≤ M)
    (hηR : ∀ x, R < ‖x‖ → η x = 0)
    {mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hmask : ∀ c ∈ Icc l r, mask ((physicalPairAnchor e).2, c) ≤ 1)
    (hmaskZero : ∀ c ∉ Icc l r, mask ((physicalPairAnchor e).2, c) = 0) :
    originalMaskedCompletePathEdgeTraffic S w η mask e ≤
      ENNReal.ofReal ((4 * M * (R + 1)) * min 1 ((r - l) * ‖v‖)) ∧
    (originalMaskedCompletePathEdgeTraffic S w η mask e).toReal ≤ 4 * M * (R + 1) := by
  have hb : originalMaskedCompletePathEdgeTraffic S w η mask e ≤
      ENNReal.ofReal ((4 * M * (R + 1)) * min 1 ((r - l) * ‖v‖)) := by
    rw [originalMaskedCompletePathEdgeTraffic_eq_setLIntegral S w η mask e l r hmaskZero]
    exact D.original_maskedOneEdgeTraffic_le_min_one_of_physicalCone hF hw
      e.1.1 (physicalPairAnchor e).2 ha hlr hR hM hclock hcone hη0 hηM hηR hmask
  refine ⟨hb, ?_⟩
  have hC : 0 ≤ 4 * M * (R + 1) := by positivity
  apply ENNReal.toReal_le_of_le_ofReal hC
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right hC (min_le_left _ _)))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
