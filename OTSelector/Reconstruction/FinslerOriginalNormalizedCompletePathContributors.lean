import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseContributors
import OTSelector.Reconstruction.OriginalNormalizedCompletePath
import OTSelector.Reconstruction.NormalizedComplianceContractionWindow

/-! The unchanged actual Finsler complete paths contribute to the canonical
normalized inverse curve of their own original weighted-minimizer scene. -/
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

/-- A phase point is the exact normalized original complete path, with the
same original edge momentum and clocks. -/
theorem normalizedMomentumNode_completePath_identity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    {cut ell r : ℝ} (ha : e.1.2 - S.level ∈ Ioo D.lo D.hi)
    (hcut : cut ∈ Ioo D.lo D.hi) (hr : cut + ell * r ∈ Ioo D.lo D.hi) :
    normalizedMomentumNodePosition S w T (cut + S.level) e +
      originalNormalizedClockMobility S w T (cut + S.level) ell r
        (normalizedMomentumNodeValue S w T e) =
      T *ᵥ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2
        (cut + S.level + ell * r) := by
  simpa only [normalizedMomentumNodePosition, normalizedMomentumNodeValue,
    originalMomentumNodePosition, originalMomentumNodeValue] using
    D.originalNormalizedClockMobility_completePath_identity hF hw T
      (Matrix.isUnit_det_of_invertible T) e.1.1 (physicalPairAnchor e).2 ha
      (by simpa only [add_sub_cancel_right] using hcut)
      (by convert hr using 1; ring)

/-- Actual weighted minimality and actual original path evolution put every
occupied eligible contributor in the same canonical inverse-curve tube. -/
theorem ae_original_minimizer_normalized_completePath_contributors
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
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
    {ρ : ℝ} (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let R := originalNormalizedClockMobility S w T (cut + S.level) ell
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ r ∈ Icc (0 : ℝ) 1,
      ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ a : ℝ,
        ‖T *ᵥ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2
          (cut + S.level + ell * r)‖ ≤ a →
        ‖phasePairVector (normalizedMomentumNodePosition S w T (cut + S.level) e)
            (normalizedMomentumNodeValue S w T e) -
          D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r‖ ≤
            max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b)) := by
  dsimp only
  have hc := D.ae_original_minimizer_normalized_phase_contributors T hF hw hgap hbounds
    hg hgb t Q hmin hcut hh _ hsmall hR
  filter_upwards [Q.full_matching, hc] with s hs hc
  intro r hr e he a hepath
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have heE := ((mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mp he).2
  apply hc r hr e he a
  rw [D.normalizedMomentumNode_completePath_identity hF hw T e
    ⟨heE.1.1, heE.1.2.trans hcut.2⟩ hcut (hclock r hr)]
  exact hepath

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
