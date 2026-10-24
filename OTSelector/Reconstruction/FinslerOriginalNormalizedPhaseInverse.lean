import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumField
import OTSelector.Analysis.ContractiveInverseCovariance
import OTSelector.MeasureTheory.MeasurableFieldReindex

/-! The canonical inverse and inverse curves of the actual normalized momentum field. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
  (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)

theorem normalizedMomentumPhaseField_lipschitz (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    ∀ z y, ‖D.normalizedMomentumPhaseField T cut h L s z -
      D.normalizedMomentumPhaseField T cut h L s y‖ ≤ (L : ℝ) * ‖z - y‖ := by
  intro z y
  simpa only [dist_eq_norm] using
    (D.lipschitzWith_normalizedMomentumPhaseField T cut h L s).dist_le_mul z y

/-- The canonical inverse at an actual target in the same normalized frame. -/
def normalizedMomentumPhaseInverse (cut h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ‖R‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (a : Fin (finrank ℝ S.covector.ker) → ℝ) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  phaseInverseAt (D.normalizedMomentumPhaseField T cut h L s)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L s) R hsmall a

theorem normalizedMomentumPhaseInverse_eq (cut h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ‖R‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (a : Fin (finrank ℝ S.covector.ker) → ℝ) :
    D.normalizedMomentumPhaseInverse T cut h L R hsmall s a +
      R (D.normalizedMomentumPhaseField T cut h L s
        (D.normalizedMomentumPhaseInverse T cut h L R hsmall s a)) = a :=
  phaseInverseAt_eq (D.normalizedMomentumPhaseField_lipschitz T cut h L s) R hsmall a

theorem measurable_normalizedMomentumPhaseInverse
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ‖R‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
        D.normalizedMomentumPhaseInverse T cut h L R hsmall a.1 a.2) :=
  measurable_phaseInverseAt (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L)
    measurable_const (D.normalizedMomentumPhaseField_lipschitz T cut h L) (fun _ ↦ hsmall)

/-- Every actual curve parameter and the unchanged whole scene remain in
the jointly Borel normalized inverse, including a scene-dependent mobility. -/
theorem measurable_normalizedMomentumPhaseInverse_parameters
    {U : Type*} [MeasurableSpace U]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × U →
      (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ] (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hR : Measurable R) (hsmall : ∀ a, ‖R a‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (target : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × U →
      (Fin (finrank ℝ S.covector.ker) → ℝ)) (htarget : Measurable target) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × U ↦
      D.normalizedMomentumPhaseInverse T cut h L (R a) (hsmall a) a.1 (target a)) := by
  unfold normalizedMomentumPhaseInverse phaseInverseAt
  apply htarget.add
  apply measurable_phaseInverseZero
  · exact measurable_phaseField_apply (P := D.normalizedMomentumPhaseField T cut h L)
      (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L)
      measurable_fst.fst ((htarget.comp measurable_fst).add measurable_snd)
  · exact hR

/-- Rerooting the physical scene subtracts `T v` from both the normalized
target and its unique actual inverse point. -/
theorem normalizedMomentumPhaseInverse_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ‖R‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s)
    (v a : Fin (finrank ℝ S.covector.ker) → ℝ) :
    D.normalizedMomentumPhaseInverse T cut h L R hsmall
      (legalMarkedInputSceneReroot _ v s) (a - T *ᵥ v) =
      D.normalizedMomentumPhaseInverse T cut h L R hsmall s a - T *ᵥ v :=
  phaseInverseAt_translate_covariant
    (D.normalizedMomentumPhaseField_lipschitz T cut h L s)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L (legalMarkedInputSceneReroot _ v s))
    R hsmall hsmall (T *ᵥ v) (D.normalizedMomentumPhaseField_reroot hF hw T hcut h L s hs v) a

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
