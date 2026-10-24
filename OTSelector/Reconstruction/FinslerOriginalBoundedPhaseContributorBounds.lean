import OTSelector.Reconstruction.FinslerOriginalCanonicalPositiveTrafficTube
import OTSelector.Reconstruction.FinslerOriginalMinimizerNormalizedField
import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseSourceContainment
import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseTargetContainment
import OTSelector.Analysis.ContractiveFieldAmplitude

/-! Actual positive original traffic lies in its own scene's normalized
canonical phase tube, with both unchanged source and target clocks retained. -/
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

/-- The actual bounded canonical field controls the momenta and cut positions
of actual positive original contributors, and puts their unchanged source and
target in deterministic normalized original-input cells. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_boundedPhase_contributor_bounds
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
    (ha : 0 ≤ a) {H : ℝ} (hH : 0 ≤ H) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let PB := 2 * H + 2 * ((L : ℝ) * a + b)
    let ZB := a + ρ * PB
    let radius := max PB ZB
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H →
      ∀ e ∈ occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s,
        e.1.2 ∈ D.sourcePhaseClocks cut ∧ e.2.2 ∈ D.targetPhaseClocks cut ∧
        ‖normalizedMomentumNodeValue S w T e‖ ≤ PB ∧
        ‖normalizedMomentumNodePosition S w T (cut + S.level) e‖ ≤ ZB ∧
        e.1 ∈ D.normalizedSourcePhaseCell T cut 0 0 radius ∧
        e.2 ∈ D.normalizedTargetPhaseCell T cut 0 0 radius := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let PB := 2 * H + 2 * ((L : ℝ) * a + b)
  let ZB := a + ρ * PB
  let radius := max PB ZB
  let R := originalNormalizedClockMobility S w T (cut + S.level) ell
  have hρ : 0 ≤ ρ := (norm_nonneg (R 0)).trans (hR 0 ⟨le_rfl, zero_le_one⟩)
  have hPB : 0 ≤ PB := by dsimp [PB, b]; positivity
  have hrad : 0 ≤ radius := hPB.trans (le_max_left _ _)
  have hfield := D.original_minimizer_canonical_normalized_momentum_field hF hw hgap
    hbounds T hg hgb t Q hmin hcut hh
  filter_upwards [Q.full_matching, hfield.2.2] with s hs hnodes
  intro hamp e he
  obtain ⟨r, hr, _, hfc, hpath⟩ :=
    original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor
      S w η f T (cut + S.level) ell e he.2 hclock hηwindow
  have heE := hmask e _ hfc
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have heN := (mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mpr ⟨he.1, heE⟩
  have hrough := hnodes e heN
  have hphysical : ‖normalizedMomentumNodePosition S w T (cut + S.level) e +
      R r (normalizedMomentumNodeValue S w T e)‖ ≤ a := by
    rw [D.normalizedMomentumNode_completePath_identity hF hw T e
      ⟨heE.1.1, heE.1.2.trans hcut.2⟩ hcut (hclockRange r hr)]
    exact hpath
  have hP : ∀ x y, ‖D.normalizedMomentumPhaseField T cut h L s x -
      D.normalizedMomentumPhaseField T cut h L s y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    intro x y
    simpa only [dist_eq_norm] using (hfield.2.1 s).dist_le_mul x y
  have hpRaw := (original_phaseAmplitude_actualMomentum_bounds L.coe_nonneg hP
    (hsmall r hr) hphysical hrough).2
  have hp : ‖normalizedMomentumNodeValue S w T e‖ ≤ PB := by
    dsimp [PB]
    linarith
  have hz : ‖normalizedMomentumNodePosition S w T (cut + S.level) e‖ ≤ ZB := by
    have hmul := (mul_le_mul_of_nonneg_right (hR r hr) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hp hρ)
    have hpos := norm_actual_phasePosition_le_of_physical (R r) hphysical
    dsimp [ZB]
    linarith
  have hz' : ‖T *ᵥ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2
      (cut + S.level) - 0‖ ≤ radius := by
    simpa only [normalizedMomentumNodePosition, originalMomentumNodePosition, sub_zero] using
      hz.trans (le_max_right PB ZB)
  have hp' : ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w (physicalPairAnchor e).2 - 0‖ ≤ radius := by
    simpa only [normalizedMomentumNodeValue, originalMomentumNodeValue, sub_zero] using
      hp.trans (le_max_left PB ZB)
  have hsource := D.original_normalized_pathPhase_source_mem hF hw T hcut e.1.1 0 0
    (physicalPairAnchor e).2 heE.1 hrad hz' hp'
  have htarget := D.original_normalized_pathPhase_target_mem hF hw T hcut e.1.1 0 0
    (physicalPairAnchor e).2 ⟨heE.1.1, heE.1.2.trans hcut.2⟩ heE.2.1
    (by simpa only [physicalPairAnchor] using
      (show e.1.2 < e.2.2 by linarith [heE.1.2, heE.2.1.1]))
    hrad hz' hp'
  refine ⟨heE.1, heE.2.1, hp, hz, hsource, ?_⟩
  have htargetPoint : e.1.1 + (physicalPairAnchor e).2.2 = e.2.1 := by
    dsimp [physicalPairAnchor]
    abel
  rwa [htargetPoint] at htarget

end OTSelector.Reconstruction
