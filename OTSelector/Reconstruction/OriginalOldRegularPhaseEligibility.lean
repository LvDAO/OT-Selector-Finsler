import OTSelector.Reconstruction.FinslerOriginalRegularMaskGeometry
import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes
import OTSelector.Reconstruction.OriginalPairClockSupportMask

/-! The original supported old/regular clock mask internally supplies the exact
canonical phase eligibility used by the actual minimizer field. Original
source/target support separation gives the clock gap, and both compliance legs
are the unchanged original legs in the identity frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Old/regular supported original masks imply literal phase-node eligibility
uniformly at nearby references, using only actual original geometry and clock
support separation. No contributor eligibility is assumed. -/
theorem exists_original_oldRegular_supportedMask_phaseEligibility
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ε gap diameter : ℝ} (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ h δ : ℝ, 0 < h ∧ 0 < δ ∧ ∀ {i : Fin 8}, (i = 3 ∨ i = 7) →
      ∀ (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (c r : ℝ),
      originalPairClockSupportMask (finrank ℝ S.covector.ker) μ ν ((physicalPairAnchor e).2, c) *
        originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε i
          ((physicalPairAnchor e).2, c) ≠ 0 → |r - c| ≤ δ →
      r - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
        e ∈ D.normalizedMomentumPhaseEligibleEdges 1 (r - S.level) h := by
  obtain ⟨h, δ, hh, hδ, hlegs⟩ := D.exists_original_oldRegular_mask_reference_legs hF hw hε hgap
  let e₀ := min ε gap
  have he : 0 < e₀ := lt_min hε hgap
  refine ⟨h, min δ (e₀ / 4), hh, lt_min hδ (by positivity), ?_⟩
  intro i hi e c r hmask hr
  have hsupport := (originalPairClockSupportMask_ne_zero_iff _ _ _ _).mp
    (left_ne_zero_of_mul hmask)
  have hregion := right_ne_zero_of_mul hmask
  obtain ⟨hl, hu, hac, hcb, _⟩ := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hregion
  have hab : (physicalPairAnchor e).2.1.1 < (physicalPairAnchor e).2.1.2 := lt_trans hac hcb
  have hdist := hbounds.separated _ hsupport.1 _ hsupport.2
  have hgaplen : gap ≤ (physicalPairAnchor e).2.1.2 - (physicalPairAnchor e).2.1.1 := by
    simpa only [Real.dist_eq, abs_of_neg (sub_neg.mpr hab), neg_sub] using hdist
  have ht := original_oldRegularClock_mask_leg_bounds hi hregion hgaplen
  have hrs := abs_le.mp (hr.trans (min_le_right δ (e₀ / 4)))
  have har : (physicalPairAnchor e).2.1.1 < r := by dsimp [e₀] at hrs; linarith [ht.1]
  have hrb : r < (physicalPairAnchor e).2.1.2 := by dsimp [e₀] at hrs; linarith [ht.2]
  obtain ⟨hrI, hleft, hright⟩ := hlegs hi _ hregion hgaplen r
    (hr.trans (min_le_left δ (e₀ / 4)))
  have hsource : e.1.2 ∈ D.sourcePhaseClocks (r - S.level) := by
    change e.1.2 - (S.level : ℝ) ∈ Ioo D.lo (r - S.level)
    change D.lo + (S.level : ℝ) < e.1.2 at hl
    change e.1.2 < r at har
    exact ⟨by linarith, by linarith⟩
  have htarget : e.2.2 ∈ D.targetPhaseClocks (r - S.level) := by
    change e.2.2 - (S.level : ℝ) ∈ Ioo (r - S.level) D.hi
    change e.2.2 < D.hi + (S.level : ℝ) at hu
    change r < e.2.2 at hrb
    exact ⟨by linarith, by linarith⟩
  refine ⟨hrI, hsource, htarget, hsupport.1, hsupport.2, ?_, ?_⟩
  · simpa only [sourcePhaseLeg, indicator_of_mem hsource, Matrix.one_mul,
      Matrix.transpose_one, Matrix.mul_one, originalSeedClockCompliance, physicalPairAnchor] using hleft
  · simpa only [targetPhaseLeg, indicator_of_mem htarget, Matrix.one_mul,
      Matrix.transpose_one, Matrix.mul_one, originalSeedClockCompliance, physicalPairAnchor] using hright

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
