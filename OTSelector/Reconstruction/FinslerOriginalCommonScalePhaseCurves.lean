import OTSelector.Analysis.CommonScaleCanonicalCurve
import OTSelector.Reconstruction.FinslerOriginalCommonScaleMomentumField
import OTSelector.Reconstruction.FinslerNormalizedPhaseCurveWindowMeasurability

/-! Literal original canonical curves are divided by the same deterministic
phase scale. Their full-scene Borel property and amplitude/speed bounds follow
from the actual field, without replacing the original inverse curve. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
  (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)

/-- The same actual canonical inverse position in common phase coordinates. -/
def commonScaleNormalizedMomentumPhaseCurvePosition (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (δ : ℝ) (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (r : ℝ) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  commonScalePhaseCurve δ (D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall s) r

/-- The literal original canonical pair with position and momentum both divided by δ. -/
def commonScaleNormalizedMomentumPhaseCurvePair (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (δ : ℝ) (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (r : ℝ) : Fin (2 * finrank ℝ S.covector.ker) → ℝ :=
  commonScalePhaseCurve δ (D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s) r

theorem measurable_commonScaleNormalizedMomentumPhaseCurvePosition
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ)) {A : ℝ} (hA : 0 ≤ A)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ‖R r - R v‖ ≤ A * |r - v|)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) (δ : ℝ) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      D.commonScaleNormalizedMomentumPhaseCurvePosition T cut h L R hsmall δ a.1 a.2) :=
  Measurable.const_smul
    (D.measurable_normalizedMomentumPhaseCurvePosition_of_lipschitzOn
      T hF hw hcut h L R hA hRLip hsmall) δ⁻¹

theorem measurable_commonScaleNormalizedMomentumPhaseCurvePair
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ)) {A : ℝ} (hA : 0 ≤ A)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ‖R r - R v‖ ≤ A * |r - v|)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) (δ : ℝ) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ a.1 a.2) :=
  Measurable.const_smul
    (D.measurable_normalizedMomentumPhaseCurvePair_of_lipschitzOn
      T hF hw hcut h L R hA hRLip hsmall) δ⁻¹

/-- The exact same curve has origin-field amplitude divided by δ. -/
theorem commonScaleNormalizedMomentumPhaseCurve_bounds
    (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    {δ : ℝ} (hδ : 0 < δ) {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ‖R r - R v‖ ≤ A * |r - v|)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∀ r ∈ Icc (0 : ℝ) 1,
      D.commonScaleNormalizedMomentumPhaseCurvePosition T cut h L R hsmall δ s r +
        R r (D.commonScaleNormalizedMomentumPhaseField T cut h L δ s
          (D.commonScaleNormalizedMomentumPhaseCurvePosition T cut h L R hsmall δ s r)) = 0) ∧
    (∀ r ∈ Icc (0 : ℝ) 1,
      ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r‖ ≤
        2 * (ρ + 1) * (‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ)) ∧
    ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r -
        D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s v‖ ≤
        4 * (1 + (L : ℝ)) * A *
          (‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ) * |r - v| :=
  commonScaleCanonicalPhasePair_bounds hδ L.coe_nonneg
    (D.normalizedMomentumPhaseField_lipschitz T cut h L s) R hsmall hρ hA hR hRLip

/-- Genuine physical mobility is zero initially, so the same actual inverse
position remains exactly zero initially after common scaling. -/
theorem commonScaleNormalizedMomentumPhaseCurvePosition_zero
    (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (hzero : R 0 = 0) (δ : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    D.commonScaleNormalizedMomentumPhaseCurvePosition T cut h L R hsmall δ s 0 = 0 := by
  have hz : canonicalUnitPhasePosition (D.normalizedMomentumPhaseField T cut h L s)
      (D.normalizedMomentumPhaseField_lipschitz T cut h L s) R hsmall 0 = 0 := by
    symm
    apply phaseInverseAt_unique (D.normalizedMomentumPhaseField_lipschitz T cut h L s)
      (unitPhaseMobility R 0) (unitPhaseMobility_small R hsmall 0)
    simp [unitPhaseMobility, hzero]
  change δ⁻¹ • canonicalUnitPhasePosition _ _ R hsmall 0 = 0
  rw [hz, smul_zero]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction