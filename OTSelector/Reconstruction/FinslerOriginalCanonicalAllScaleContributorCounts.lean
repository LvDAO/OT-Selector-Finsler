import OTSelector.Reconstruction.FinslerOriginalCanonicalSourceContributorCounts
import OTSelector.Reconstruction.FinslerOriginalCanonicalTargetContributorCounts
import OTSelector.Reconstruction.FinslerNormalizedAllScalePhaseEvents
import OTSelector.Finite.IntegerAmplitudeScale

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

/-- The all-scale original-data event controls the actual canonical
integer scale chosen from this scene's own field amplitude. No count bound
or integer scale is supplied as an additional assumption. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_positiveTraffic_count_of_source_allScale_not_badEvent
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
    {N : ℕ} (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.normalizedSourcePhaseCurveAllScaleBadEvent T cut N radius K →
      (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) < (⊤ : ℝ≥0∞) ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) ≤
          (K * (C + 1)) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  have hC := canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A
  have hcounts := ae_all_iff.mpr (fun n : ℕ ↦
    D.ae_original_minimizer_positiveTraffic_count_of_source_not_badEvent hF hw hgap
      hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
      hclock hηwindow hmask (m := n + 1) (by omega) K)
  filter_upwards [hcounts] with s hs
  intro hsnot hamp
  let amplitude := ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let m := canonicalPhaseIntegerScale C amplitude
  have hms := canonicalPhaseIntegerScale_spec hC.1 hN hamp
  have hm : 1 ≤ m := hN.trans hms.1
  have hsnotm : s ∉ D.normalizedSourcePhaseCurveBadEvent T cut m
      (max (2 * (a + ρ * Real.sqrt (8 * |t| * G / h)))
        (Real.sqrt (8 * |t| * G / h) + 2 * (L : ℝ) *
          (a + ρ * Real.sqrt (8 * |t| * G / h)))) K :=
    not_mem_natTailEventUnion hms.1 hsnot
  have hroot : 2 * (ρ + 1) * amplitude ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right hC.2.1 (norm_nonneg _)).trans hms.2.1
  have hspeed : 4 * (1 + (L : ℝ)) * A * amplitude ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right hC.2.2 (norm_nonneg _)).trans hms.2.1
  have hc := hs (m - 1)
  rw [Nat.sub_add_cancel hm] at hc
  have hc' := hc hsnotm hroot hspeed
  refine ⟨hc'.1, ?_⟩
  have hb := hc'.2.le.trans (mul_le_mul_of_nonneg_left hms.2.2 hK)
  simpa only [Measure.real, mul_assoc] using hb

/-- The all-scale original-data event controls the actual canonical
integer scale chosen from this scene's own field amplitude. No count bound
or integer scale is supplied as an additional assumption. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_positiveTraffic_count_of_target_allScale_not_badEvent
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
    {N : ℕ} (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.normalizedTargetPhaseCurveAllScaleBadEvent T cut N radius K →
      (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) < (⊤ : ℝ≥0∞) ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) ≤
          (K * (C + 1)) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  have hC := canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A
  have hcounts := ae_all_iff.mpr (fun n : ℕ ↦
    D.ae_original_minimizer_positiveTraffic_count_of_target_not_badEvent hF hw hgap
      hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
      hclock hηwindow hmask (m := n + 1) (by omega) K)
  filter_upwards [hcounts] with s hs
  intro hsnot hamp
  let amplitude := ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let m := canonicalPhaseIntegerScale C amplitude
  have hms := canonicalPhaseIntegerScale_spec hC.1 hN hamp
  have hm : 1 ≤ m := hN.trans hms.1
  have hsnotm : s ∉ D.normalizedTargetPhaseCurveBadEvent T cut m
      (max (2 * (a + ρ * Real.sqrt (8 * |t| * G / h)))
        (Real.sqrt (8 * |t| * G / h) + 2 * (L : ℝ) *
          (a + ρ * Real.sqrt (8 * |t| * G / h)))) K :=
    not_mem_natTailEventUnion hms.1 hsnot
  have hroot : 2 * (ρ + 1) * amplitude ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right hC.2.1 (norm_nonneg _)).trans hms.2.1
  have hspeed : 4 * (1 + (L : ℝ)) * A * amplitude ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right hC.2.2 (norm_nonneg _)).trans hms.2.1
  have hc := hs (m - 1)
  rw [Nat.sub_add_cancel hm] at hc
  have hc' := hc hsnotm hroot hspeed
  refine ⟨hc'.1, ?_⟩
  have hb := hc'.2.le.trans (mul_le_mul_of_nonneg_left hms.2.2 hK)
  simpa only [Measure.real, mul_assoc] using hb

end OTSelector.Reconstruction
