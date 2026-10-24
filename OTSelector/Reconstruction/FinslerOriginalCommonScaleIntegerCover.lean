import OTSelector.Reconstruction.FinslerOriginalCommonScalePhaseCurves
import OTSelector.Reconstruction.FinslerOriginalMeasurableCanonicalScale

/-! The actual cover scale is selected from the actual divided field amplitude.
It remains Borel in the complete scene and has the sharp linear 1/δ bound. -/
open Set Function MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The real-scene natural cover scale uses the original amplitude divided by δ. -/
def commonScaleNormalizedCanonicalCurveIntegerScale
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (ρ A δ : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℕ :=
  canonicalPhaseIntegerScale (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A)
    (‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ)

theorem measurable_commonScaleNormalizedCanonicalCurveIntegerScale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (ρ A δ : ℝ) :
    Measurable (D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ) :=
  Nat.measurable_ceil.comp (measurable_const.mul
    (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm.div_const δ))

/-- The selected integer lies in the retained scale tail and costs only
a fixed multiple of the genuinely divided original field amplitude. -/
theorem commonScaleNormalizedCanonicalCurveIntegerScale_spec
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (ρ A δ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hamp : (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ) :
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    N ≤ D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ s ∧
      C * (‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ) ≤
        (D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ s : ℝ) ∧
      (D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ s : ℝ) ≤
        (C + 1) * (‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ) :=
  canonicalPhaseIntegerScale_spec
    (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1 hN hamp

/-- The actual rescaled canonical curve obeys both integer covering bounds. -/
theorem commonScaleNormalizedCanonicalCurveIntegerScale_covers
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    {δ : ℝ} (hδ : 0 < δ) {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ‖R r - R v‖ ≤ A * |r - v|)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ s
    (∀ r ∈ Icc (0 : ℝ) 1,
      ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r‖ ≤ (k : ℝ)) ∧
    ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r -
        D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s v‖ ≤
          (k : ℝ) * |r - v| := by
  have hb := D.commonScaleNormalizedMomentumPhaseCurve_bounds
    T cut h L R hsmall hδ hρ hA hR hRLip s
  have hcoef := canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A
  have hampl : 0 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ := by positivity
  have hceil := Nat.le_ceil (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A *
    (‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ))
  refine ⟨fun r hr ↦ (hb.2.1 r hr).trans ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hcoef.2.1 hampl).trans hceil
  · intro r hr v hv
    exact (hb.2.2 r hr v hv).trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hcoef.2.2 hampl).trans hceil) (abs_nonneg _))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction