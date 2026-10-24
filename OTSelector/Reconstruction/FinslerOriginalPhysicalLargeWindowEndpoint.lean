import OTSelector.Reconstruction.FinslerOriginalLargeWindowTrafficExpectation
import OTSelector.Reconstruction.FinslerFocalLiteralEdgeOccupation
import OTSelector.Reconstruction.OriginalCompactClockWeightedOccupation
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Physical endpoint windows provide the literal one-edge constant and every
Palm integrability input in the original current-scale large-traffic L2 estimate. -/
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


private theorem finite_spatial_smoothing_mass {q : ℕ}
    {η : (Fin q → ℝ) → ℝ}
    {R M : ℝ} (hηM : ∀ x, η x ≤ M)
    (hηR : ∀ x, R < ‖x‖ → η x = 0) :
    (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))) ≠ (⊤ : ℝ≥0∞) := by
  have hpoint : ∀ x, ENNReal.ofReal (η x) ≤
      (Metric.closedBall (0 : Fin q → ℝ) R).indicator (fun _ ↦ ENNReal.ofReal M) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin q → ℝ) R
    · rw [indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (hηM x)
    · have hnorm : R < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
      rw [hηR x hnorm, ENNReal.ofReal_zero]
      positivity
  have hbound := lintegral_mono (μ := (volume : Measure (Fin q → ℝ))) hpoint
  rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet, lintegral_const,
    Measure.restrict_apply_univ] at hbound
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (isCompact_closedBall (0 : Fin q → ℝ) R).measure_lt_top.ne) hbound

/-- Actual left focal geometry supplies the physical single-edge constant;
original kinetic energy supplies both Palm moments. The current good/bad split
therefore yields the literal masked large-traffic L2 estimate internally. -/
theorem OriginalSeedConditionalMoments.exists_original_left_focal_largeCanonicalTraffic_sq_integral_le
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
    {R₀ M₀ : ℝ} (hR₀ : 0 ≤ R₀) (hM₀ : 0 ≤ M₀)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) (hηM : ∀ x, η x ≤ M₀)
    (hηR : ∀ x, R₀ < ‖x‖ → η x = 0)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (hmaskM : Measurable mask) (hmaskOne : ∀ z, mask z ≤ 1)
    (hclock : ∀ m c, mask (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (heligible : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c (physicalPairAnchor e).2‖ *
          mask ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h) :
    ∃ δ : ℝ, δ > 0 ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ inward ∈ Ioo (0 : ℝ) δ, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |c - S.level - D.lo - inward| ≤ σ * inward) →
      (∀ c ∈ Icc l r, c - S.level ∈ Ioo D.lo D.hi) →
      (∀ m c, c ∉ Icc l r → mask (m, c) = 0) →
      ∀ {K : ℝ}, (
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      D.normalizedSourcePhaseCurveCountThreshold T cut radius ≤ K) →
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
    let Bad := fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m radius K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x)) (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) s).toReal
    let large := fun N : ℕ ↦ {s | N ≤ k s ∧ 1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s}
    let error := fun N : ℕ ↦ ∫ s,
      (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    let originalPalmMean := ((∫⁻ x, (fun x ↦ ENNReal.ofReal (η x)) x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    (∀ N : ℕ, 1 ≤ N →
      Integrable (fun s ↦ ((large N).indicator traffic s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, ((large N).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        (3 * (4 * M₀ * (R₀ + 1)) * (K * (C + 1))) * originalPalmMean + error N) ∧
    Tendsto error atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδspan, σ, hσ, hσhalf, hedgePhysical⟩ :=
    D.exists_original_left_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ, hδ, hδspan, σ, hσ, hσhalf, ?_⟩
  intro inward hinward l r hlr hband hclockJ hzero K hK
  let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hf : Measurable f :=
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hmaskM
  have hηfinite := finite_spatial_smoothing_mass hηM hηR
  have hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top (b := ∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
    · rw [D.lintegral_original_clockOccupation_norm_eq_pathLength hF hw hbounds Q]
      exact ENNReal.ofReal_ne_top
    · apply lintegral_mono
      intro m
      apply lintegral_mono
      intro c
      exact mul_le_of_le_one_right (by positivity) (hmaskOne (m, c))
  have hpfinite := D.lintegral_original_compactClock_maskedWeightedOccupation_lt_top
    hF hw hgap hbounds Q (Tᵀ)⁻¹ isCompact_Icc hclockJ mask hmaskOne hzero
  have hclockf : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r := by
    intro m c hfc
    apply hclock m c
    intro hzero
    exact hfc (by simp only [f, hzero, mul_zero])
  have hηwindow' : ∀ x, ENNReal.ofReal (η x) ≠ 0 → ‖T *ᵥ x‖ ≤ a := by
    intro x hx
    apply hηwindow x
    intro hz
    exact hx (by rw [hz, ENNReal.ofReal_zero])
  have hedge : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
      d (fun x ↦ ENNReal.ofReal (η x)) f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        d (fun x ↦ ENNReal.ofReal (η x)) f e).toReal ≤ 4 * M₀ * (R₀ + 1) := by
    intro e he
    have heinterior : e.1.2 - S.level ∈ Ioo D.lo D.hi := by
      by_contra hn
      have hfc : ∀ c : ℝ, f ((physicalPairAnchor e).2, c) = 0 := by
        intro c
        by_contra hnonzero
        have hs := (heligible e c hnonzero).1
        change e.1.2 - S.level ∈ Ioo D.lo cut at hs
        exact hn ⟨hs.1, hs.2.trans hcut.2⟩
      apply he
      unfold legalMarkedCompletePathEdgeTraffic
      simp_rw [hfc, mul_zero]
      exact lintegral_zero
    exact (hedgePhysical inward hinward l r hlr hband e heinterior R₀ M₀ hR₀ hM₀
      η hη0 hηM hηR mask (fun c _ ↦ hmaskOne _) (hzero (physicalPairAnchor e).2)).2
  exact D.original_minimizer_largeCanonicalTraffic_source_sq_integral_le
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclockf hηwindow' heligible hη.ennreal_ofReal hf hηfinite hffinite
    (by positivity : 0 ≤ 4 * M₀ * (R₀ + 1)) hedge hpfinite.ne hK

/-- Actual right focal geometry supplies the physical single-edge constant;
original kinetic energy supplies both Palm moments. The current good/bad split
therefore yields the literal masked large-traffic L2 estimate internally. -/
theorem OriginalSeedConditionalMoments.exists_original_right_focal_largeCanonicalTraffic_sq_integral_le
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
    {R₀ M₀ : ℝ} (hR₀ : 0 ≤ R₀) (hM₀ : 0 ≤ M₀)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) (hηM : ∀ x, η x ≤ M₀)
    (hηR : ∀ x, R₀ < ‖x‖ → η x = 0)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (hmaskM : Measurable mask) (hmaskOne : ∀ z, mask z ≤ 1)
    (hclock : ∀ m c, mask (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (heligible : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c (physicalPairAnchor e).2‖ *
          mask ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h) :
    ∃ δ : ℝ, δ > 0 ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ inward ∈ Ioo (0 : ℝ) δ, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |D.hi - (c - S.level) - inward| ≤ σ * inward) →
      (∀ c ∈ Icc l r, c - S.level ∈ Ioo D.lo D.hi) →
      (∀ m c, c ∉ Icc l r → mask (m, c) = 0) →
      ∀ {K : ℝ}, (
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      D.normalizedTargetPhaseCurveCountThreshold T cut radius ≤ K) →
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
    let Bad := fun m ↦ D.normalizedTargetPhaseCurveBadEvent T cut m radius K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x)) (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) s).toReal
    let large := fun N : ℕ ↦ {s | N ≤ k s ∧ 1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s}
    let error := fun N : ℕ ↦ ∫ s,
      (({s | N ≤ k s ∧ s ∈ Bad (k s)}).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    let originalPalmMean := ((∫⁻ x, (fun x ↦ ENNReal.ofReal (η x)) x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    (∀ N : ℕ, 1 ≤ N →
      Integrable (fun s ↦ ((large N).indicator traffic s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, ((large N).indicator traffic s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        (3 * (4 * M₀ * (R₀ + 1)) * (K * (C + 1))) * originalPalmMean + error N) ∧
    Tendsto error atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδspan, σ, hσ, hσhalf, hedgePhysical⟩ :=
    D.exists_original_right_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ, hδ, hδspan, σ, hσ, hσhalf, ?_⟩
  intro inward hinward l r hlr hband hclockJ hzero K hK
  let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hf : Measurable f :=
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hmaskM
  have hηfinite := finite_spatial_smoothing_mass hηM hηR
  have hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top (b := ∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
    · rw [D.lintegral_original_clockOccupation_norm_eq_pathLength hF hw hbounds Q]
      exact ENNReal.ofReal_ne_top
    · apply lintegral_mono
      intro m
      apply lintegral_mono
      intro c
      exact mul_le_of_le_one_right (by positivity) (hmaskOne (m, c))
  have hpfinite := D.lintegral_original_compactClock_maskedWeightedOccupation_lt_top
    hF hw hgap hbounds Q (Tᵀ)⁻¹ isCompact_Icc hclockJ mask hmaskOne hzero
  have hclockf : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r := by
    intro m c hfc
    apply hclock m c
    intro hzero
    exact hfc (by simp only [f, hzero, mul_zero])
  have hηwindow' : ∀ x, ENNReal.ofReal (η x) ≠ 0 → ‖T *ᵥ x‖ ≤ a := by
    intro x hx
    apply hηwindow x
    intro hz
    exact hx (by rw [hz, ENNReal.ofReal_zero])
  have hedge : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
      d (fun x ↦ ENNReal.ofReal (η x)) f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        d (fun x ↦ ENNReal.ofReal (η x)) f e).toReal ≤ 4 * M₀ * (R₀ + 1) := by
    intro e he
    have heinterior : e.1.2 - S.level ∈ Ioo D.lo D.hi := by
      by_contra hn
      have hfc : ∀ c : ℝ, f ((physicalPairAnchor e).2, c) = 0 := by
        intro c
        by_contra hnonzero
        have hs := (heligible e c hnonzero).1
        change e.1.2 - S.level ∈ Ioo D.lo cut at hs
        exact hn ⟨hs.1, hs.2.trans hcut.2⟩
      apply he
      unfold legalMarkedCompletePathEdgeTraffic
      simp_rw [hfc, mul_zero]
      exact lintegral_zero
    exact (hedgePhysical inward hinward l r hlr hband e heinterior R₀ M₀ hR₀ hM₀
      η hη0 hηM hηR mask (fun c _ ↦ hmaskOne _) (hzero (physicalPairAnchor e).2)).2
  exact D.original_minimizer_largeCanonicalTraffic_target_sq_integral_le
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclockf hηwindow' heligible hη.ennreal_ofReal hf hηfinite hffinite
    (by positivity : 0 ≤ 4 * M₀ * (R₀ + 1)) hedge hpfinite.ne hK

end OTSelector.Reconstruction
