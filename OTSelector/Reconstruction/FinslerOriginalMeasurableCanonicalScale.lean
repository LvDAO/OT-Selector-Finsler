import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumField
import OTSelector.Finite.IntegerAmplitudeScale
import Mathlib.MeasureTheory.Function.Floor

/-! The actual canonical cover integer is a Borel function of its unchanged
whole original scene. No external scale selector is supplied. -/
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

/-- The literal natural phase-cover scale chosen from the actual field amplitude. -/
def normalizedCanonicalCurveIntegerScale
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (ρ A : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℕ :=
  canonicalPhaseIntegerScale (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A)
    ‖D.normalizedMomentumPhaseField T cut h L s 0‖

theorem measurable_normalizedCanonicalCurveIntegerScale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (ρ A : ℝ) :
    Measurable (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A) :=
  Nat.measurable_ceil.comp (measurable_const.mul
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm)

/-- On the retained amplitude range this actual Borel integer lies in the
same all-scale event and satisfies the sharp linear cover-scale bound. -/
theorem normalizedCanonicalCurveIntegerScale_spec
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (ρ A : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hamp : (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    N ≤ D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s ∧
      C * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
        (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
      (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ≤
        (C + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ :=
  canonicalPhaseIntegerScale_spec
    (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1 hN hamp

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
