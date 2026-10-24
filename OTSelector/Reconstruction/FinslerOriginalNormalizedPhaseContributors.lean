import OTSelector.Reconstruction.FinslerOriginalMinimizerNormalizedField
import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseInverse
import OTSelector.Analysis.CanonicalUnitCurve

/-! Actual normalized canonical inverse curves and their original occupied contributors. -/
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

/-- The literal target-zero normalized inverse curve of the same original scene. -/
def normalizedMomentumPhaseCurvePosition (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (r : ℝ) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  canonicalUnitPhasePosition (D.normalizedMomentumPhaseField T cut h L s)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L s) R hsmall r

/-- The same canonical normalized curve with both position and original momentum retained. -/
def normalizedMomentumPhaseCurvePair (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (r : ℝ) : Fin (2 * finrank ℝ S.covector.ker) → ℝ :=
  canonicalUnitPhasePair (D.normalizedMomentumPhaseField T cut h L s)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L s) R hsmall r

theorem measurable_normalizedMomentumPhaseCurvePosition
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ)) (hR : Measurable R)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall a.1 a.2) :=
  measurable_canonicalUnitPhasePosition
    (P := D.normalizedMomentumPhaseField T cut h L)
    (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L) R hR hsmall

theorem measurable_normalizedMomentumPhaseCurvePair
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ)) (hR : Measurable R)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      D.normalizedMomentumPhaseCurvePair T cut h L R hsmall a.1 a.2) :=
  measurable_canonicalUnitPhasePair (P := D.normalizedMomentumPhaseField T cut h L)
    (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L)
    (D.normalizedMomentumPhaseField_lipschitz T cut h L) R hR hsmall

/-- The actual canonical normalized curve retains the original amplitude
and speed constants on every ambient scene. -/
theorem normalizedMomentumPhaseCurve_bounds (cut h : ℝ) (L : ℝ≥0)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∀ r ∈ Icc (0 : ℝ) 1,
      D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall s r +
        R r (D.normalizedMomentumPhaseField T cut h L s
          (D.normalizedMomentumPhaseCurvePosition T cut h L R hsmall s r)) = 0) ∧
    (∀ r ∈ Icc (0 : ℝ) 1,
      ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r‖ ≤
        2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖) ∧
    (∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r -
        D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r'‖ ≤
        4 * (1 + (L : ℝ)) * A * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ * |r - r'|) := by
  have hb := canonicalUnitPhasePair_bounds L.coe_nonneg
    (D.normalizedMomentumPhaseField_lipschitz T cut h L s) R hsmall hρ hA hR hRLip
  exact ⟨hb.1, hb.2.1, hb.2.2.1⟩

/-- Every actually occupied normalized node of the original weighted
minimizer that contributes to a physical window lies in the same canonical
inverse-curve tube, with the explicit original `sqrt(|t|)` error. -/
theorem ae_original_minimizer_normalized_phase_contributors
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    (R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ *
      Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ : ℝ} (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ r ∈ Icc (0 : ℝ) 1,
      ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ a : ℝ,
        ‖normalizedMomentumNodePosition S w T (cut + S.level) e +
          R r (normalizedMomentumNodeValue S w T e)‖ ≤ a →
        ‖phasePairVector (normalizedMomentumNodePosition S w T (cut + S.level) e)
            (normalizedMomentumNodeValue S w T e) -
          D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r‖ ≤
            max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b)) := by
  dsimp only
  have hfield := D.original_minimizer_canonical_normalized_momentum_field
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh
  filter_upwards [hfield.2.2] with s hs
  intro r hr e he a hphysical
  exact canonicalUnitPhasePair_contributor (Real.sqrt_nonneg _)
    (D.normalizedMomentumPhaseField_lipschitz T cut h _ s) R hsmall hr (hR r hr)
    hphysical (hs e he)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
