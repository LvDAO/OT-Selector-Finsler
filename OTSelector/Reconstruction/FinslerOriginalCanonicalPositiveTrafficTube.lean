import OTSelector.Reconstruction.FinslerOriginalNormalizedCompletePathContributors
import OTSelector.Reconstruction.FinslerPositiveCompletePathContributors

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

/-- The occupied original edges with a positive complete-path traffic readout. -/
def occupiedCompletePathTrafficContributors (q : ℕ)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (s : LegalMarkedOptimalInputScene q) : Set (LegalMarkedPhysicalEdge q) :=
  (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support ∩
    legalMarkedCompletePathContributors q d η f

/-- Intersecting with actual occupied support leaves the original contributor
count unchanged; no selected process is substituted. -/
theorem measure_occupiedCompletePathTrafficContributors {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (s : LegalMarkedOptimalInputScene q) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        (occupiedCompletePathTrafficContributors q d η f s) =
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        (legalMarkedCompletePathContributors q d η f) := by
  apply measure_congr
  filter_upwards [(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support_mem_ae] with e he
  apply propext
  change (e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support ∧
    e ∈ legalMarkedCompletePathContributors q d η f) ↔
      e ∈ legalMarkedCompletePathContributors q d η f
  exact and_iff_right he

/-- The true weighted minimizer's positive original traffic contributors lie
in its actual normalized canonical curve tube, with both physical endpoint
clocks active and ordered. No field or contributing-clock premise is supplied. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_positiveTraffic_canonical_tube
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
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let R := originalNormalizedClockMobility S w T (cut + S.level) ell
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s,
        e.1.2 ∈ D.sourcePhaseClocks cut ∧ e.2.2 ∈ D.targetPhaseClocks cut ∧
        e.1.2 - S.level ∈ Ioo D.lo D.hi ∧ e.1.2 < e.2.2 ∧
        ∃ r ∈ Icc (0 : ℝ) 1,
          ‖phasePairVector (normalizedMomentumNodePosition S w T (cut + S.level) e)
              (normalizedMomentumNodeValue S w T e) -
            D.normalizedMomentumPhaseCurvePair T cut h L R hsmall s r‖ ≤
              max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b)) := by
  dsimp only
  have hc := D.ae_original_minimizer_normalized_completePath_contributors hF hw hgap
    hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hR
  filter_upwards [Q.full_matching, hc] with s hs hc
  intro e he
  obtain ⟨r, hr, _, hf, hpath⟩ :=
    original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor
      S w η f T (cut + S.level) ell e he.2 hclock hηwindow
  have heE := hmask e _ hf
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have heN := (mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mpr ⟨he.1, heE⟩
  refine ⟨heE.1, heE.2.1, ⟨heE.1.1, heE.1.2.trans hcut.2⟩, ?_, r, hr, hc r hr e heN a hpath⟩
  linarith [heE.1.2, heE.2.1.1]

end OTSelector.Reconstruction
