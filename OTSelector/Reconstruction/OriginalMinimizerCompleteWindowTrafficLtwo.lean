import OTSelector.Reconstruction.FinslerOriginalSelectedBadTrafficTail
import OTSelector.Reconstruction.OriginalMinimizerBoundedPhaseTrafficLtwo
import OTSelector.Reconstruction.FinslerOriginalLargeWindowTrafficExpectation
import OTSelector.Reconstruction.FinslerNormalizedAllScalePhaseEvents

/-! The actual bounded and large canonical phases together give complete
original-window traffic L2, using the unchanged matching and input law. -/
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

/-- Actual bounded and large canonical phases exhaust the same original
traffic. The original cell count produces bounded-phase L2 internally and the
actual large-phase theorem gives the complementary L2 bound. -/
theorem OriginalSeedConditionalMoments.original_minimizer_completeWindowTraffic_memLp_two
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
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
        ENNReal.ofReal B)
    (hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
 :
    MemLp (fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let H := 1 + 2 * ((L : ℝ) * a + b)
  let K := D.normalizedSourcePhaseCurveCountThreshold T cut
    (max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b)))
  have hH : 0 ≤ H := by dsimp [H, b]; positivity
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let traffic := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s).toReal
  let Small := {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}
  let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
  let Big := {s | 1 ≤ k s ∧ 1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
    2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖}
  have hbounded := D.original_minimizer_boundedPhase_traffic_memLp_two hF hw hgap hbounds
    T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask ha hH hη hf hB hsingle
  have heBound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker) d η f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e).toReal ≤ B := by
    intro e _
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsingle e.1.1 (physicalPairAnchor e).2)
    simpa only [legalMarkedCompletePathEdgeTraffic, physicalPairAnchor, d,
      ENNReal.toReal_ofReal hB] using ht
  have hlarge := D.original_minimizer_largeCanonicalTraffic_source_sq_integral_le
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB heBound hpfinite (K := K) le_rfl
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d
      (measurable_originalSeedPathOffset_joint S hF hw) hη hf).ennreal_toReal
  have hamp : Measurable (fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hk := D.measurable_normalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A
  have hBig : MeasurableSet Big :=
    (measurableSet_le measurable_const hk).inter
      ((measurableSet_le measurable_const hamp).inter (measurableSet_le measurable_const hamp))
  have hbigLp : MemLp (Big.indicator traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    (memLp_two_iff_integrable_sq (htraffic.aestronglyMeasurable.indicator hBig)).mpr
      (hlarge.1 1 le_rfl).1
  apply (hbounded.add hbigLp).mono' htraffic.aestronglyMeasurable
  filter_upwards [] with s
  change ‖traffic s‖ ≤ Small.indicator traffic s + Big.indicator traffic s
  have ht0 : 0 ≤ traffic s := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg ht0]
  by_cases hs : s ∈ Small
  · rw [indicator_of_mem hs]
    exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg) s)
  · have hampH : H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := lt_of_not_ge hs
    have hH1 : 1 ≤ H := by
      have hn : 0 ≤ 2 * ((L : ℝ) * a + b) := by dsimp [b]; positivity
      dsimp [H]
      linarith
    have hamp1 : (1 : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ :=
      hH1.trans hampH.le
    have hscale := D.normalizedCanonicalCurveIntegerScale_spec T cut h L ρ A (N := 1) le_rfl s (by simpa only [Nat.cast_one] using hamp1)
    have hsBig : s ∈ Big := ⟨hscale.1, hamp1, by dsimp [H] at hampH; linarith⟩
    rw [indicator_of_notMem hs, indicator_of_mem hsBig, zero_add]

end OTSelector.Reconstruction
