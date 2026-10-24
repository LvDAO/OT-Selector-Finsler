import OTSelector.Reconstruction.FinslerOriginalBoundedPhaseContributorBounds
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

/-- Actual source and target input counts bound the same literal occupied
contributor family on the bounded canonical phase event. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_boundedPhase_original_counts
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
    (hη : Measurable η) (hf : Measurable f) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let PB := 2 * H + 2 * ((L : ℝ) * a + b)
    let radius := max PB (a + ρ * PB)
    let V := occupiedPairTrafficContributors (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H →
      physicalScenePairKernel s.1 (V s) ≤
        (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
          (D.normalizedSourcePhaseCell T cut 0 0 radius ×ˢ {(0 : Fin 2)}) ∧
      physicalScenePairKernel s.1 (V s) ≤
        (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
          (D.normalizedTargetPhaseCell T cut 0 0 radius ×ˢ {(1 : Fin 2)}) := by
  dsimp only
  have hb := D.ae_original_minimizer_boundedPhase_contributor_bounds hF hw hgap hbounds
    T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask ha hH
  filter_upwards [Q.full_matching, hb] with s hs hbounds
  intro hamp
  constructor
  · apply occupiedPairTrafficContributors_source_count_le _
      (measurable_originalSeedPathOffset_joint S hF hw) hη hf s hs
      (D.measurableSet_normalizedSourcePhaseCell hF hw T hcut 0 0 _)
    intro e he
    exact (hbounds hamp e he).2.2.2.2.1
  · apply occupiedPairTrafficContributors_target_count_le _
      (measurable_originalSeedPathOffset_joint S hF hw) hη hf s hs
      (D.measurableSet_normalizedTargetPhaseCell hF hw T hcut 0 0 _)
    intro e he
    exact (hbounds hamp e he).2.2.2.2.2

end OTSelector.Reconstruction
