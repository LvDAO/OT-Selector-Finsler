import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseContributors

/-! Moving the physical source window preserves the same canonical normalized
inverse construction, with the target moved in the identical phase frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
  (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)

theorem normalizedMomentumPhaseCurvePosition_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall
      (legalMarkedInputSceneReroot _ v s) r =
      D.normalizedMomentumPhaseInverse T cut h L (R r) (hsmall r hr) s (T *ᵥ v) - T *ᵥ v := by
  simpa only [normalizedMomentumPhaseCurvePosition, canonicalUnitPhasePosition,
    unitPhaseMobility, Set.indicator_of_mem hr, sub_self, normalizedMomentumPhaseInverse] using
    D.normalizedMomentumPhaseInverse_reroot T hF hw hcut h L (R r) (hsmall r hr) s hs v (T *ᵥ v)

theorem normalizedMomentumPhaseCurvePair_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    D.normalizedMomentumPhaseCurvePair T cut h L R hsmall
      (legalMarkedInputSceneReroot _ v s) r =
      phasePairVector
        (D.normalizedMomentumPhaseInverse T cut h L (R r) (hsmall r hr) s (T *ᵥ v) - T *ᵥ v)
        (D.normalizedMomentumPhaseField T cut h L s
          (D.normalizedMomentumPhaseInverse T cut h L (R r) (hsmall r hr) s (T *ᵥ v))) := by
  change phasePairVector
    (D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall
      (legalMarkedInputSceneReroot _ v s) r)
    (D.normalizedMomentumPhaseField T cut h L (legalMarkedInputSceneReroot _ v s)
      (D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall
        (legalMarkedInputSceneReroot _ v s) r)) = _
  rw [D.normalizedMomentumPhaseCurvePosition_reroot T hF hw hcut h L R hsmall s hs v hr,
    D.normalizedMomentumPhaseField_reroot hF hw T hcut h L s hs v]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
