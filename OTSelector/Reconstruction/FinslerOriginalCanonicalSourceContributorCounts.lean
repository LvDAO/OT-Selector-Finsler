import OTSelector.Reconstruction.FinslerOriginalCanonicalPositiveTrafficTube
import OTSelector.Reconstruction.FinslerNormalizedAdaptivePhaseCurveCounts

/-! The genuine original minimizer's random canonical curve is controlled
by the single fixed-data normalized source-count event. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- One data-only normalized source event controls the literal positive
original traffic contributors of the actual weighted minimizer. The curve is
constructed from the same original scene, after the event has been fixed. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_positiveTraffic_count_of_source_not_badEvent
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) (ha : 0 ≤ a)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r -
        originalNormalizedClockMobility S w T (cut + S.level) ell r'‖ ≤ A * |r - r'|)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    {m : ℕ} (hm : 1 ≤ m) (K : ℝ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.normalizedSourcePhaseCurveBadEvent T cut m radius K →
      2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ (m : ℝ) →
      4 * (1 + (L : ℝ)) * A * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ (m : ℝ) →
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) < (⊤ : ℝ≥0∞) ∧
        ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f)).toReal < K * (m : ℝ) := by
  dsimp only
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let R := originalNormalizedClockMobility S w T (cut + S.level) ell
  have hρ : 0 ≤ ρ := (norm_nonneg (R 0)).trans (hR 0 ⟨le_rfl, zero_le_one⟩)
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have htube := D.ae_original_minimizer_positiveTraffic_canonical_tube hF hw hgap
    hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask
  have hcount := D.ae_count_normalizedPathPhaseTube_lt_of_not_badEvent hF hw T hcut hm Q
    (r := radius) (K := K) hradius
  filter_upwards [htube, hcount] with s hsTube hsCount
  intro hsnot hroot hspeed
  have hcurve := D.normalizedMomentumPhaseCurve_bounds T cut h L R hsmall hρ hA hR hRLip s
  have hrootγ : ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s 0‖ ≤ (m : ℝ) :=
    (hcurve.2.1 0 ⟨le_rfl, zero_le_one⟩).trans hroot
  have hLipγ : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r -
        D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r'‖ ≤
          (m : ℝ) * |r - r'| := by
    intro r hr r' hr'
    exact (hcurve.2.2 r hr r' hr').trans (mul_le_mul_of_nonneg_right hspeed (abs_nonneg _))
  have hc := hsCount hsnot (D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s)
    hrootγ hLipγ (occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s) (fun e he ↦
        ⟨(hsTube e he).1, (hsTube e he).2.2.2.2⟩)
  simpa only [measure_occupiedCompletePathTrafficContributors] using hc

end OTSelector.Reconstruction
