import OTSelector.Reconstruction.UnitPhaseCurveWindowMeasurability
import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseContributors

/-! Actual normalized Finsler canonical curves are Borel from on-window mobility alone. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
  (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)

/-- The same literal normalized inverse curve is Borel in scene and clock
when the actual fixed mobility is Lipschitz only on the physical unit window. -/
theorem measurable_normalizedMomentumPhaseCurvePosition_of_lipschitzOn
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ)) {A : ℝ} (hA : 0 ≤ A)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall a.1 a.2) :=
  measurable_canonicalUnitPhasePosition_of_lipschitzOn
    (P := D.normalizedMomentumPhaseField T cut h L)
    (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L) R hA hRLip hsmall

/-- Joint measurability of the actual normalized position-momentum curve
uses the same original mobility, without any extension premise on raw `R`. -/
theorem measurable_normalizedMomentumPhaseCurvePair_of_lipschitzOn
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ)) {A : ℝ} (hA : 0 ≤ A)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      D.normalizedMomentumPhaseCurvePair T cut h L R hsmall a.1 a.2) :=
  measurable_canonicalUnitPhasePair_of_lipschitzOn
    (P := D.normalizedMomentumPhaseField T cut h L)
    (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L) R hA hRLip hsmall

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
