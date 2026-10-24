import OTSelector.Reconstruction.FinslerOriginalSelectedBadTrafficTail
import OTSelector.Reconstruction.FinslerOriginalCurrentScaleMinimizerTrafficSquare
import OTSelector.Reconstruction.FinslerNormalizedAllScalePhaseEvents

/-! Actual original large-amplitude traffic squares are integrated against the
true original Palm moment, with a current-bad remainder vanishing in expectation. -/
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

/-- On the actual large-amplitude branch, full-path traffic squares are
integrable and bounded by the original pure normalized-momentum Palm moment
plus the internally proved current-bad remainder; that remainder tends to zero. -/
theorem OriginalSeedConditionalMoments.original_minimizer_largeCanonicalTraffic_source_sq_integral_le
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
    (hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {K : ℝ} (hK :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      D.normalizedSourcePhaseCurveCountThreshold T cut radius ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
    let Bad := fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m radius K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
    let large := fun N : ℕ ↦ {s | N ≤ k s ∧ 1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s}
    let error := fun N : ℕ ↦ ∫ s,
      (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    let originalPalmMean := ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    (∀ N : ℕ, 1 ≤ N →
      Integrable (fun s ↦ ((large N).indicator traffic s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, ((large N).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        (3 * B * (K * (C + 1))) * originalPalmMean + error N) ∧
    Tendsto error atTop (𝓝 0) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
  let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let Bad := fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m radius K
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let pweight := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1) * f z
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s).toReal
  let weighted := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η pweight s).toReal
  let coeff := 3 * B * (K * (C + 1))
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hpweight : Measurable pweight :=
    ((measurable_originalNormalizedMomentumMarkNorm S hF hw T).comp measurable_fst).ennreal_ofReal.mul hf
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal
  have hweighted := measurable_legalMarkedCompletePathTraffic d hd hη hpweight
  have hweightedMean : (∫⁻ s, legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      d η pweight s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hpweight]
    exact ENNReal.mul_ne_top hηfinite hpfinite
  have hiweighted : Integrable weighted (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    integrable_toReal_of_lintegral_ne_top hweighted.aemeasurable hweightedMean
  have heqweighted : (∫ s, weighted s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, pweight (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal := by
    rw [integral_toReal hweighted.aemeasurable (ae_lt_top hweighted hweightedMean),
      Q.lintegral_completePathTraffic d hd hη hpweight]
  have hK0 : 0 ≤ K := (D.normalizedSourcePhaseCurveCountThreshold_pos T cut radius).le.trans hK
  have hC : 1 ≤ C := (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1
  have hcoeff : 0 ≤ coeff := mul_nonneg (mul_nonneg (by positivity) hB) (mul_nonneg hK0 (by linarith))
  have hbad := D.original_minimizer_completePathTraffic_canonical_source_selected_bad_sq_tail
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB hbound hK
  have hgood := D.ae_original_minimizer_completePathTraffic_sq_of_source_currentScale_not_badEvent
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB hbound K hK0
  refine ⟨?_, hbad.2⟩
  intro N hN
  let large := {s | N ≤ k s ∧ 1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s}
  let badTail := fun s ↦ (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
  have hk : Measurable k := D.measurable_normalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A
  have hamp : Measurable amp :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hlarge : MeasurableSet large :=
    (measurableSet_le measurable_const hk).inter
      ((measurableSet_le measurable_const hamp).inter (measurableSet_le measurable_const hamp))
  have hmajor : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ((large.indicator traffic) s) ^ 2 ≤ coeff * weighted s + badTail s := by
    filter_upwards [hgood] with s hs
    by_cases hls : s ∈ large
    · rw [indicator_of_mem hls]
      by_cases hbs : s ∈ Bad (k s)
      · have hb : s ∈ {s | N ≤ k s ∧ s ∈ Bad (k s)} := ⟨hls.1, hbs⟩
        dsimp [badTail]
        rw [indicator_of_mem hb]
        exact le_add_of_nonneg_left (mul_nonneg hcoeff ENNReal.toReal_nonneg)
      · exact (hs hbs hls.2.1 hls.2.2).trans (le_add_of_nonneg_right (sq_nonneg _))
    · rw [indicator_of_notMem hls, zero_pow (by norm_num : 2 ≠ 0)]
      exact add_nonneg (mul_nonneg hcoeff ENNReal.toReal_nonneg) (sq_nonneg _)
  have hiBad : Integrable badTail (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    (hbad.1 N hN).1
  have hiMajor := (hiweighted.const_mul coeff).add hiBad
  have hiLarge : Integrable (fun s ↦ ((large.indicator traffic) s) ^ 2)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    apply hiMajor.mono' ((htraffic.indicator hlarge).pow_const 2).aestronglyMeasurable
    filter_upwards [hmajor] with s hs
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hiLarge, ?_⟩
  calc
    _ ≤ ∫ s, coeff * weighted s + badTail s
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
      integral_mono_ae hiLarge hiMajor hmajor
    _ = _ := by rw [integral_add (hiweighted.const_mul coeff) hiBad,
      integral_const_mul, heqweighted]

/-- On the actual large-amplitude branch, full-path traffic squares are
integrable and bounded by the original pure normalized-momentum Palm moment
plus the internally proved current-bad remainder; that remainder tends to zero. -/
theorem OriginalSeedConditionalMoments.original_minimizer_largeCanonicalTraffic_target_sq_integral_le
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
    (hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {K : ℝ} (hK :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      D.normalizedTargetPhaseCurveCountThreshold T cut radius ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
    let Bad := fun m ↦ D.normalizedTargetPhaseCurveBadEvent T cut m radius K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
    let large := fun N : ℕ ↦ {s | N ≤ k s ∧ 1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s}
    let error := fun N : ℕ ↦ ∫ s,
      (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    let originalPalmMean := ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    (∀ N : ℕ, 1 ≤ N →
      Integrable (fun s ↦ ((large N).indicator traffic s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, ((large N).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        (3 * B * (K * (C + 1))) * originalPalmMean + error N) ∧
    Tendsto error atTop (𝓝 0) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
  let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let Bad := fun m ↦ D.normalizedTargetPhaseCurveBadEvent T cut m radius K
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let pweight := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1) * f z
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s).toReal
  let weighted := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η pweight s).toReal
  let coeff := 3 * B * (K * (C + 1))
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hpweight : Measurable pweight :=
    ((measurable_originalNormalizedMomentumMarkNorm S hF hw T).comp measurable_fst).ennreal_ofReal.mul hf
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal
  have hweighted := measurable_legalMarkedCompletePathTraffic d hd hη hpweight
  have hweightedMean : (∫⁻ s, legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      d η pweight s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hpweight]
    exact ENNReal.mul_ne_top hηfinite hpfinite
  have hiweighted : Integrable weighted (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    integrable_toReal_of_lintegral_ne_top hweighted.aemeasurable hweightedMean
  have heqweighted : (∫ s, weighted s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, pweight (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal := by
    rw [integral_toReal hweighted.aemeasurable (ae_lt_top hweighted hweightedMean),
      Q.lintegral_completePathTraffic d hd hη hpweight]
  have hK0 : 0 ≤ K := (D.normalizedTargetPhaseCurveCountThreshold_pos T cut radius).le.trans hK
  have hC : 1 ≤ C := (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1
  have hcoeff : 0 ≤ coeff := mul_nonneg (mul_nonneg (by positivity) hB) (mul_nonneg hK0 (by linarith))
  have hbad := D.original_minimizer_completePathTraffic_canonical_target_selected_bad_sq_tail
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB hbound hK
  have hgood := D.ae_original_minimizer_completePathTraffic_sq_of_target_currentScale_not_badEvent
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB hbound K hK0
  refine ⟨?_, hbad.2⟩
  intro N hN
  let large := {s | N ≤ k s ∧ 1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s}
  let badTail := fun s ↦ (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
  have hk : Measurable k := D.measurable_normalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A
  have hamp : Measurable amp :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hlarge : MeasurableSet large :=
    (measurableSet_le measurable_const hk).inter
      ((measurableSet_le measurable_const hamp).inter (measurableSet_le measurable_const hamp))
  have hmajor : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ((large.indicator traffic) s) ^ 2 ≤ coeff * weighted s + badTail s := by
    filter_upwards [hgood] with s hs
    by_cases hls : s ∈ large
    · rw [indicator_of_mem hls]
      by_cases hbs : s ∈ Bad (k s)
      · have hb : s ∈ {s | N ≤ k s ∧ s ∈ Bad (k s)} := ⟨hls.1, hbs⟩
        dsimp [badTail]
        rw [indicator_of_mem hb]
        exact le_add_of_nonneg_left (mul_nonneg hcoeff ENNReal.toReal_nonneg)
      · exact (hs hbs hls.2.1 hls.2.2).trans (le_add_of_nonneg_right (sq_nonneg _))
    · rw [indicator_of_notMem hls, zero_pow (by norm_num : 2 ≠ 0)]
      exact add_nonneg (mul_nonneg hcoeff ENNReal.toReal_nonneg) (sq_nonneg _)
  have hiBad : Integrable badTail (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    (hbad.1 N hN).1
  have hiMajor := (hiweighted.const_mul coeff).add hiBad
  have hiLarge : Integrable (fun s ↦ ((large.indicator traffic) s) ^ 2)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    apply hiMajor.mono' ((htraffic.indicator hlarge).pow_const 2).aestronglyMeasurable
    filter_upwards [hmajor] with s hs
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hiLarge, ?_⟩
  calc
    _ ≤ ∫ s, coeff * weighted s + badTail s
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
      integral_mono_ae hiLarge hiMajor hmajor
    _ = _ := by rw [integral_add (hiweighted.const_mul coeff) hiBad,
      integral_const_mul, heqweighted]

end OTSelector.Reconstruction
