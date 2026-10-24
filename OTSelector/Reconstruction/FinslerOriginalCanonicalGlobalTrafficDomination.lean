import OTSelector.Reconstruction.CompletePathTrafficCountUpper
import OTSelector.Reconstruction.FinslerOriginalMeasurableCanonicalScale
import OTSelector.Reconstruction.FinslerOriginalCanonicalPositiveTrafficTube
import OTSelector.Reconstruction.FinslerNormalizedAdaptiveGlobalCount
import OTSelector.Reconstruction.FinslerNormalizedAdaptiveTargetGlobalCount

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

/-- Actual original raw traffic is dominated by the complete original
input envelope count at the internally chosen Borel canonical scale, including
on its geometric bad event. No envelope domination is assumed. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_completePathTraffic_le_canonical_source_globalCount
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
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal ≤
        B * ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
          (D.normalizedAdaptiveGlobalSourceEnvelope T cut
            (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s) radius ×ˢ {0})).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let R := originalNormalizedClockMobility S w T (cut + S.level) ell
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hAdata := measurableSet_legalMarkedCompletePathContributors d hd hη hf
  have hρ : 0 ≤ ρ := (norm_nonneg (R 0)).trans (hR 0 ⟨le_rfl, zero_le_one⟩)
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have hfiniteIntegral : (∫⁻ s, legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      d η f s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hf]
    exact ENNReal.mul_ne_top hηfinite hffinite
  have htube := D.ae_original_minimizer_positiveTraffic_canonical_tube hF hw hgap
    hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask
  have hcounts := ae_all_iff.mpr (fun m : ℕ ↦
    D.ae_count_normalizedSourcePathPhaseTube_le_globalEnvelope hF hw T hcut m Q hradius)
  filter_upwards [htube, hcounts,
    ae_lt_top (measurable_legalMarkedCompletePathTraffic d hd hη hf) hfiniteIntegral]
    with s hsTube hsCount hfinite
  let m := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s
  let V := occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker) d η f s
  have hV : MeasurableSet V :=
    (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).isClosed_support.measurableSet.inter hAdata
  have hC := canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A
  have hscale : C * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ (m : ℝ) := Nat.le_ceil _
  have hcurve := D.normalizedMomentumPhaseCurve_bounds T cut h L R hsmall hρ hA hR hRLip s
  have hroot : ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s 0‖ ≤ (m : ℝ) :=
    (hcurve.2.1 0 ⟨le_rfl, zero_le_one⟩).trans
      ((mul_le_mul_of_nonneg_right hC.2.1 (norm_nonneg _)).trans hscale)
  have hLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r -
        D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r'‖ ≤ (m : ℝ) * |r - r'| := by
    intro r hr r' hr'
    exact (hcurve.2.2 r hr r' hr').trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hC.2.2 (norm_nonneg _)).trans hscale) (abs_nonneg _))
  have hc := hsCount m (D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s)
    hroot hLip V (fun e he ↦ ⟨(hsTube e he).1, (hsTube e he).2.2.2.2⟩)
  have hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      e ∉ V → legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e = 0 := by
    filter_upwards [(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support_mem_ae]
      with e he hnot
    by_contra hnonzero
    exact hnot ⟨he, hnonzero⟩
  have hb : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict V,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e).toReal ≤ B := by
    filter_upwards [ae_restrict_mem hV] with e he
    exact hbound e he.2
  have hu := legalMarkedCompletePathTraffic_le_bound_mul_count d hd hη hf s V hc.1 hfinite.ne hzero hb
  have hcReal : (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real V ≤
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.normalizedAdaptiveGlobalSourceEnvelope T cut m radius ×ˢ {0})).toReal := by
    simpa only [Measure.real] using hc.2
  exact hu.trans (mul_le_mul_of_nonneg_left hcReal hB)

/-- Actual original raw traffic is dominated by the complete original
input envelope count at the internally chosen Borel canonical scale, including
on its geometric bad event. No envelope domination is assumed. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_completePathTraffic_le_canonical_target_globalCount
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
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal ≤
        B * ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
          (D.normalizedAdaptiveGlobalTargetEnvelope T cut
            (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s) radius ×ˢ {1})).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let b := Real.sqrt (8 * |t| * G / h)
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let R := originalNormalizedClockMobility S w T (cut + S.level) ell
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hAdata := measurableSet_legalMarkedCompletePathContributors d hd hη hf
  have hρ : 0 ≤ ρ := (norm_nonneg (R 0)).trans (hR 0 ⟨le_rfl, zero_le_one⟩)
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have hfiniteIntegral : (∫⁻ s, legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      d η f s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hf]
    exact ENNReal.mul_ne_top hηfinite hffinite
  have htube := D.ae_original_minimizer_positiveTraffic_canonical_tube hF hw hgap
    hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask
  have hcounts := ae_all_iff.mpr (fun m : ℕ ↦
    D.ae_count_normalizedTargetPathPhaseTube_le_globalEnvelope hF hw T hcut m Q hradius)
  filter_upwards [htube, hcounts,
    ae_lt_top (measurable_legalMarkedCompletePathTraffic d hd hη hf) hfiniteIntegral]
    with s hsTube hsCount hfinite
  let m := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s
  let V := occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker) d η f s
  have hV : MeasurableSet V :=
    (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).isClosed_support.measurableSet.inter hAdata
  have hC := canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A
  have hscale : C * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ (m : ℝ) := Nat.le_ceil _
  have hcurve := D.normalizedMomentumPhaseCurve_bounds T cut h L R hsmall hρ hA hR hRLip s
  have hroot : ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s 0‖ ≤ (m : ℝ) :=
    (hcurve.2.1 0 ⟨le_rfl, zero_le_one⟩).trans
      ((mul_le_mul_of_nonneg_right hC.2.1 (norm_nonneg _)).trans hscale)
  have hLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r -
        D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r'‖ ≤ (m : ℝ) * |r - r'| := by
    intro r hr r' hr'
    exact (hcurve.2.2 r hr r' hr').trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hC.2.2 (norm_nonneg _)).trans hscale) (abs_nonneg _))
  have hc := hsCount m (D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s)
    hroot hLip V (fun e he ↦ ⟨(hsTube e he).2.2.1, (hsTube e he).2.1, (hsTube e he).2.2.2.1, (hsTube e he).2.2.2.2⟩)
  have hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      e ∉ V → legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e = 0 := by
    filter_upwards [(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support_mem_ae]
      with e he hnot
    by_contra hnonzero
    exact hnot ⟨he, hnonzero⟩
  have hb : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict V,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e).toReal ≤ B := by
    filter_upwards [ae_restrict_mem hV] with e he
    exact hbound e he.2
  have hu := legalMarkedCompletePathTraffic_le_bound_mul_count d hd hη hf s V hc.1 hfinite.ne hzero hb
  have hcReal : (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real V ≤
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.normalizedAdaptiveGlobalTargetEnvelope T cut m radius ×ˢ {1})).toReal := by
    simpa only [Measure.real] using hc.2
  exact hu.trans (mul_le_mul_of_nonneg_left hcReal hB)

end OTSelector.Reconstruction
