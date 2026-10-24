import OTSelector.Reconstruction.FinslerOriginalBoundedPhaseOriginalCounts
import OTSelector.Reconstruction.OriginalCountTailOnEventCompletePathAELtwo
import OTSelector.Reconstruction.OriginalOccupiedTrafficInputCounts
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! The actual bounded canonical phase uses the same original two-color input
counts. All count domination is derived from the original minimizer and matching. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Every bounded actual canonical phase has L2 original traffic internally,
using its unchanged original input count and finite original cell intensity.
No count or occupied-support hypothesis is required from the caller. -/
theorem OriginalSeedConditionalMoments.original_minimizer_boundedPhase_traffic_memLp_two
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
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ : ℝ} (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (ha : 0 ≤ a) {H : ℝ} (hH : 0 ≤ H)
    (hη : Measurable η) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
        ENNReal.ofReal B) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    MemLp ({s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}.indicator
      (fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let PB := 2 * H + 2 * ((L : ℝ) * a + b)
  let radius := max PB (a + ρ * PB)
  let W := D.normalizedSourcePhaseCell T cut 0 0 radius
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  let V := occupiedPairTrafficContributors (finrank ℝ S.covector.ker) d η f
  let Small := {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}
  have hSmall : MeasurableSet Small := measurableSet_le
    (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hW := D.measurableSet_normalizedSourcePhaseCell hF hw T hcut 0 0 radius
  have hWfin := D.normalizedSourcePhaseCell_intensity_lt_top hF hw T hcut 0 0 radius
  let mass := ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ) W
  have hmass : mass ≤ ENNReal.ofReal mass.toReal := by
    rw [ENNReal.ofReal_toReal hWfin.ne]
  have hc := D.ae_original_minimizer_boundedPhase_original_counts hF hw hgap hbounds
    T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask ha hH hη hf
  have ht := Q.original_source_countTail_completePath_ltwo_ae_on d hd hη hf hW
    ENNReal.toReal_nonneg hmass hSmall V
    (fun s ↦ measurableSet_occupiedPairTrafficContributors d hd hη hf s) (K := -1) hB
    (by
      filter_upwards [hc] with s hs hss _
      refine ⟨ae_occupiedPairTrafficContributors_outside_zero d η f s, ?_, (hs hss).1⟩
      exact ae_of_all _ (fun z ↦ hsingle z.1 z.2))
  have hall : {s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) |
      (-1 : ℝ) < ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (W ×ˢ {0})).toReal} = univ := by
    apply eq_univ_of_forall
    intro s
    exact lt_of_lt_of_le (by norm_num) ENNReal.toReal_nonneg
  dsimp only [W] at hall
  simpa only [hall, indicator_univ] using ht.1

end OTSelector.Reconstruction
