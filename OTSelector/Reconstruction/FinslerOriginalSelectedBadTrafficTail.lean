import OTSelector.Reconstruction.FinslerOriginalCanonicalGlobalTrafficDomination
import OTSelector.Reconstruction.FinslerNormalizedCanonicalSelectedBadScale

/-! The actual original minimizer full-path traffic has a vanishing second moment
on the bad event at its internally chosen current canonical scale. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
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

/-- Literal original full-path traffic has an integrable and vanishing second
moment on its current canonical source bad event above increasing scale cutoffs.
The canonical scale, whole-input count bound and tail are all proved internally. -/
theorem OriginalSeedConditionalMoments.original_minimizer_completePathTraffic_canonical_source_selected_bad_sq_tail
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
    {K : ℝ} (hK :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
        (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
        2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
          (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1) + 1 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let Bad := fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m radius K
    let Count := fun m ↦ D.normalizedGlobalSourceEnvelopeCount T cut m radius
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
    (∀ N : ℕ, 1 ≤ N →
      Integrable (fun s ↦ (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        B ^ 2 * ∑' n : ℕ, ∫ s, ((Bad (n + N)).indicator (Count (n + N)) s) ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ∧
    Tendsto (fun N : ℕ ↦ ∫ s,
      (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
      atTop (𝓝 0) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hρ : 0 ≤ ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut + S.level) ell 0)).trans
      (hR 0 ⟨le_rfl, zero_le_one⟩)
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have hdom := D.ae_original_minimizer_completePathTraffic_le_canonical_source_globalCount
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB hbound
  have hdom' : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∈ D.normalizedSourcePhaseCurveBadEvent T cut
        (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s) radius K →
      |(legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s).toReal| ≤
        B * |D.normalizedGlobalSourceEnvelopeCount T cut
          (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s) radius s| := by
    filter_upwards [hdom] with s hs _
    simpa only [OriginalSeedConditionalMoments.normalizedGlobalSourceEnvelopeCount,
      abs_of_nonneg ENNReal.toReal_nonneg] using hs
  exact D.normalizedCanonicalSource_selected_bad_sq_tail hF hw T hcut h L ρ A Q
    hradius hK (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal hB hdom'

/-- Literal original full-path traffic has an integrable and vanishing second
moment on its current canonical target bad event above increasing scale cutoffs.
The canonical scale, whole-input count bound and tail are all proved internally. -/
theorem OriginalSeedConditionalMoments.original_minimizer_completePathTraffic_canonical_target_selected_bad_sq_tail
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
    {K : ℝ} (hK :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
        (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
        2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
          (D.normalizedTargetPhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1) + 1 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let Bad := fun m ↦ D.normalizedTargetPhaseCurveBadEvent T cut m radius K
    let Count := fun m ↦ D.normalizedGlobalTargetEnvelopeCount T cut m radius
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
    (∀ N : ℕ, 1 ≤ N →
      Integrable (fun s ↦ (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        B ^ 2 * ∑' n : ℕ, ∫ s, ((Bad (n + N)).indicator (Count (n + N)) s) ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ∧
    Tendsto (fun N : ℕ ↦ ∫ s,
      (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
      atTop (𝓝 0) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hρ : 0 ≤ ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut + S.level) ell 0)).trans
      (hR 0 ⟨le_rfl, zero_le_one⟩)
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have hdom := D.ae_original_minimizer_completePathTraffic_le_canonical_target_globalCount
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB hbound
  have hdom' : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∈ D.normalizedTargetPhaseCurveBadEvent T cut
        (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s) radius K →
      |(legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s).toReal| ≤
        B * |D.normalizedGlobalTargetEnvelopeCount T cut
          (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s) radius s| := by
    filter_upwards [hdom] with s hs _
    simpa only [OriginalSeedConditionalMoments.normalizedGlobalTargetEnvelopeCount,
      abs_of_nonneg ENNReal.toReal_nonneg] using hs
  exact D.normalizedCanonicalTarget_selected_bad_sq_tail hF hw T hcut h L ρ A Q
    hradius hK (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal hB hdom'

end OTSelector.Reconstruction
