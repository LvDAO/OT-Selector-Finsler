import OTSelector.Reconstruction.FinslerOriginalCommonScalePhaseCurves
import OTSelector.Reconstruction.FinslerOriginalCommonScaleNodeIdentities

/-! The original weighted minimizer's genuine occupied nodes lie near the
same rescaled canonical curve. A physical support of normalized radius Aδ
therefore gives a tube radius independent of δ≥1. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual weighted minimality gives the scaled canonical phase tube with
its exact original occupied-node error b/δ. -/
theorem ae_original_minimizer_commonScale_phase_contributors
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {δ : ℝ} (hδ : 0 < δ)
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
        ‖commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e +
          R r (commonScaleNormalizedMomentumNodeValue S w T δ e)‖ ≤ a →
        ‖phasePairVector
            (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
            (commonScaleNormalizedMomentumNodeValue S w T δ e) -
          D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r‖ ≤
            max (2 * (a + ρ * (b / δ)))
              (b / δ + 2 * (L : ℝ) * (a + ρ * (b / δ))) := by
  dsimp only
  have hf := D.original_minimizer_canonical_normalized_momentum_field
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh
  filter_upwards [hf.2.2] with s hs
  intro r hr e he a hphysical
  exact commonScaleCanonicalPhasePair_contributor hδ (Real.sqrt_nonneg _)
    (D.normalizedMomentumPhaseField_lipschitz T cut h _ s) R hsmall hr (hR r hr)
    hphysical (hs e he)

/-- The literal original complete path in a physical support of radius Aδ
gives a constant-radius actual canonical tube at every common scale δ≥1. -/
theorem ae_original_minimizer_commonScale_completePath_contributors_uniform
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {δ : ℝ} (hδ : 1 ≤ δ)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    (hclock : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let R := originalNormalizedClockMobility S w T (cut + S.level) ell
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ r ∈ Icc (0 : ℝ) 1,
      ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ A : ℝ,
        ‖T *ᵥ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2
          (cut + S.level + ell * r)‖ ≤ A * δ →
        ‖phasePairVector
            (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
            (commonScaleNormalizedMomentumNodeValue S w T δ e) -
          D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r‖ ≤
            max (2 * (A + ρ * b)) (b + 2 * (L : ℝ) * (A + ρ * b)) := by
  dsimp only
  have hδpos : 0 < δ := by linarith
  have hf := D.original_minimizer_canonical_normalized_momentum_field
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh
  filter_upwards [Q.full_matching, hf.2.2] with s hs hnode
  intro r hr e he A hepath
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have heE := ((mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mp he).2
  have hphys : ‖commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e +
      originalNormalizedClockMobility S w T (cut + S.level) ell r
        (commonScaleNormalizedMomentumNodeValue S w T δ e)‖ ≤ A := by
    rw [D.commonScaleNormalizedMomentumNode_completePath_identity hF hw T δ e
      ⟨heE.1.1, heE.1.2.trans hcut.2⟩ hcut (hclock r hr), norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδpos)]
    have hpath := mul_le_mul_of_nonneg_left hepath (inv_nonneg.mpr hδpos.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hδpos.ne', one_mul, mul_comm A δ,
      inv_mul_cancel_left₀ hδpos.ne'] using hpath
  exact commonScaleCanonicalPhasePair_contributor_uniform hδ (Real.sqrt_nonneg _)
    (D.normalizedMomentumPhaseField_lipschitz T cut h _ s)
    _ hsmall hr hρ (Real.sqrt_nonneg _) (hR r hr) hphys (hnode e he)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction