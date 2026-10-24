import OTSelector.Reconstruction.FinslerOriginalCanonicalAllScaleContributorCounts
import OTSelector.Reconstruction.FinslerOriginalMinimizerContractiveTrafficSquare

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

/-- The actual data-only all-scale event and the internally constructed
canonical integer scale give the literal original momentum-weighted traffic
square estimate. No contributor-count bound is assumed. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_completePathTraffic_sq_of_source_allScale_not_badEvent
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
    (hη : Measurable η) (hf : Measurable f)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B)
    {N : ℕ} (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.normalizedSourcePhaseCurveAllScaleBadEvent T cut N radius K →
      (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
      2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
        (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
          (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal ^ 2 ≤
          (3 * B * (K * (C + 1))) *
            (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
              (fun z ↦ originalSeedPathOffset S w z.2 z.1) η
              (fun z ↦ ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1) * f z)
                s).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let Good := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    s ∉ D.normalizedSourcePhaseCurveAllScaleBadEvent T cut N radius K ∧
      (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let Count := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
      (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) < (⊤ : ℝ≥0∞) ∧
    (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real
      (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) ≤
      (K * (C + 1)) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  have hC : 1 ≤ C := (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1
  have hκ : 0 ≤ K * (C + 1) := mul_nonneg hK (by linarith)
  have hcounts := D.ae_original_minimizer_positiveTraffic_count_of_source_allScale_not_badEvent
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hN K hK
  have hsquare := D.ae_original_minimizer_completePathTraffic_sq_le_of_count
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hη hf hηfinite hffinite
    hclock hηwindow hmask (fun s ↦ Good s ∧ Count s) hB hκ hbound (fun _ hs ↦ hs.2)
  filter_upwards [hcounts, hsquare] with s hsCount hsSquare
  intro hsnot hamp hlarge
  exact hsSquare ⟨⟨hsnot, hamp⟩, hsCount hsnot hamp⟩ hlarge

/-- The actual data-only all-scale event and the internally constructed
canonical integer scale give the literal original momentum-weighted traffic
square estimate. No contributor-count bound is assumed. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_completePathTraffic_sq_of_target_allScale_not_badEvent
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
    (hη : Measurable η) (hf : Measurable f)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B)
    {N : ℕ} (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.normalizedTargetPhaseCurveAllScaleBadEvent T cut N radius K →
      (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
      2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
        (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
          (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal ^ 2 ≤
          (3 * B * (K * (C + 1))) *
            (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
              (fun z ↦ originalSeedPathOffset S w z.2 z.1) η
              (fun z ↦ ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1) * f z)
                s).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let Good := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    s ∉ D.normalizedTargetPhaseCurveAllScaleBadEvent T cut N radius K ∧
      (N : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let Count := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
      (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) < (⊤ : ℝ≥0∞) ∧
    (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real
      (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) ≤
      (K * (C + 1)) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  have hC : 1 ≤ C := (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1
  have hκ : 0 ≤ K * (C + 1) := mul_nonneg hK (by linarith)
  have hcounts := D.ae_original_minimizer_positiveTraffic_count_of_target_allScale_not_badEvent
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hN K hK
  have hsquare := D.ae_original_minimizer_completePathTraffic_sq_le_of_count
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hη hf hηfinite hffinite
    hclock hηwindow hmask (fun s ↦ Good s ∧ Count s) hB hκ hbound (fun _ hs ↦ hs.2)
  filter_upwards [hcounts, hsquare] with s hsCount hsSquare
  intro hsnot hamp hlarge
  exact hsSquare ⟨⟨hsnot, hamp⟩, hsCount hsnot hamp⟩ hlarge

end OTSelector.Reconstruction
