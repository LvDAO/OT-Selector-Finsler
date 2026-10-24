import OTSelector.Reconstruction.FinslerOriginalMomentumEligibleNodes
import OTSelector.Reconstruction.FinslerOriginalCommonCutLegalCycle

/-! Actual eligible complete-path nodes inherit their quantitative momentum
bound from the unchanged original legal kinetic two-cycle inequality. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The internal common-cut eligibility thresholds supply all four actual leg
bounds needed for the original cycle estimate. -/
theorem OriginalSeedConditionalMoments.eligible_kineticTwoCycle_momentum_norm_sq_le
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {cut h δ : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) (hδ : 0 ≤ δ)
    (e f : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (he : e ∈ D.momentumPhaseEligibleEdges cut h)
    (hf : f ∈ D.momentumPhaseEligibleEdges cut h)
    (hcycle : D.originalFocalKinetic gap e.1.2 e.2.2 (e.2.1 - e.1.1) +
      D.originalFocalKinetic gap f.1.2 f.2.2 (f.2.1 - f.1.1) ≤
        D.originalFocalKinetic gap e.1.2 f.2.2 (f.2.1 - e.1.1) +
          D.originalFocalKinetic gap f.1.2 e.2.2 (e.2.1 - f.1.1) + δ) :
    ‖originalMomentumNodeValue S w e - originalMomentumNodeValue S w f‖ ^ 2 ≤
      (finrank ℝ S.covector.ker : ℝ) / h ^ 2 *
        ‖originalMomentumNodePosition S w (cut + S.level) e -
          originalMomentumNodePosition S w (cut + S.level) f‖ ^ 2 + 2 * δ / h := by
  obtain ⟨hea, heb, heμ, heν, heA, heB⟩ := he
  obtain ⟨hfa, hfb, hfμ, hfν, hfA, hfB⟩ := hf
  have ha₁ : e.1.2 - S.level ∈ Ioo D.lo D.hi ∧ e.1.2 ∈ μ.support :=
    ⟨⟨hea.1, hea.2.trans hcut.2⟩, heμ⟩
  have hb₁ : e.2.2 - S.level ∈ Ioo D.lo D.hi ∧ e.2.2 ∈ ν.support :=
    ⟨⟨hcut.1.trans heb.1, heb.2⟩, heν⟩
  have ha₂ : f.1.2 - S.level ∈ Ioo D.lo D.hi ∧ f.1.2 ∈ μ.support :=
    ⟨⟨hfa.1, hfa.2.trans hcut.2⟩, hfμ⟩
  have hb₂ : f.2.2 - S.level ∈ Ioo D.lo D.hi ∧ f.2.2 ∈ ν.support :=
    ⟨⟨hcut.1.trans hfb.1, hfb.2⟩, hfν⟩
  have heqA : D.sourcePhaseLeg cut e.1.2 =
      originalSeedClockCompliance S w e.1.2 (cut + S.level) := by
    simp only [OriginalSeedConditionalMoments.sourcePhaseLeg, indicator_of_mem hea,
      originalSeedClockCompliance, add_sub_cancel_right]
  have heqB : D.targetPhaseLeg cut e.2.2 =
      originalSeedClockCompliance S w (cut + S.level) e.2.2 := by
    simp only [OriginalSeedConditionalMoments.targetPhaseLeg, indicator_of_mem heb,
      originalSeedClockCompliance, add_sub_cancel_right]
  have hfqA : D.sourcePhaseLeg cut f.1.2 =
      originalSeedClockCompliance S w f.1.2 (cut + S.level) := by
    simp only [OriginalSeedConditionalMoments.sourcePhaseLeg, indicator_of_mem hfa,
      originalSeedClockCompliance, add_sub_cancel_right]
  have hfqB : D.targetPhaseLeg cut f.2.2 =
      originalSeedClockCompliance S w (cut + S.level) f.2.2 := by
    simp only [OriginalSeedConditionalMoments.targetPhaseLeg, indicator_of_mem hfb,
      originalSeedClockCompliance, add_sub_cancel_right]
  rw [heqA] at heA
  rw [heqB] at heB
  rw [hfqA] at hfA
  rw [hfqB] at hfB
  have hdisp₁ : f.1.1 + (physicalPairAnchor f).2.2 - e.1.1 = f.2.1 - e.1.1 := by
    change f.1.1 + (f.2.1 - f.1.1) - e.1.1 = _
    abel
  have hdisp₂ : e.1.1 + (physicalPairAnchor e).2.2 - f.1.1 = e.2.1 - f.1.1 := by
    change e.1.1 + (e.2.1 - e.1.1) - f.1.1 = _
    abel
  have hn := D.original_commonCut_legalCycle_momentum_norm_sq_le_of_leg_lower_bounds hF hw hbounds
    e.1.1 f.1.1 (physicalPairAnchor e).2 (physicalPairAnchor f).2
    ha₁ hb₁ ha₂ hb₂ (by change e.1.2 < cut + S.level; linarith [hea.2])
    (by change cut + S.level < e.2.2; linarith [heb.1])
    (by change f.1.2 < cut + S.level; linarith [hfa.2])
    (by change cut + S.level < f.2.2; linarith [hfb.1]) hh hδ heA heB hfA hfB
    (by rw [hdisp₁, hdisp₂]; exact hcycle)
  simpa only [originalMomentumNodeValue, originalMomentumNodePosition, norm_sub_rev] using hn

end OTSelector.Reconstruction
