import OTSelector.Reconstruction.FinslerOriginalContractiveFocalPhaseWindows
import OTSelector.Reconstruction.FinslerPositiveCompletePathContributors
import OTSelector.Reconstruction.OriginalContractiveCompletePathTrafficSquare
import OTSelector.Reconstruction.FinslerNormalizedCompletePathTrafficSquare

/-! Weighted traffic-square control for the unchanged original Finsler
minimizer. Actual node errors and contributing clocks are produced internally. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every actually occupied positive-traffic edge yields a true contributing
clock and the actual canonical field's node error in the same phase frame. -/
theorem original_occupied_completePath_contributors_are_contractive
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut h ell a b : ℝ} (L : ℝ≥0)
    (hcut : cut ∈ Ioo D.lo D.hi)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞)
    (f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s)
    (herror : ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ‖normalizedMomentumNodeValue S w T e - D.normalizedMomentumPhaseField T cut h L s
        (normalizedMomentumNodePosition S w T (cut + S.level) e)‖ ≤ b) :
    ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support ∩
      legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      ∃ r ∈ Icc (0 : ℝ) 1,
        ‖normalizedMomentumNodePosition S w T (cut + S.level) e +
          originalNormalizedClockMobility S w T (cut + S.level) ell r
            (normalizedMomentumNodeValue S w T e)‖ ≤ a ∧
        ‖normalizedMomentumNodeValue S w T e - D.normalizedMomentumPhaseField T cut h L s
          (normalizedMomentumNodePosition S w T (cut + S.level) e)‖ ≤ b := by
  intro e he
  obtain ⟨r, hr, _, hf, hpath⟩ :=
    original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor
      S w η f T (cut + S.level) ell e he.2 hclock hηwindow
  have heE := hmask e _ hf
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have heN := (mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mpr ⟨he.1, heE⟩
  refine ⟨r, hr, ?_, herror e heN⟩
  rw [D.normalizedMomentumNode_completePath_identity hF hw T e
    ⟨heE.1.1, heE.1.2.trans hcut.2⟩ hcut (hclockRange r hr)]
  exact hpath

/-- On a data-controlled counting event, the actual original minimizer's
large-amplitude traffic is squared against the literal original momentum-weighted
traffic. Actual cyclic optimality, field error, contributing clocks, and weighted
traffic finiteness are all derived in the proof. -/
theorem ae_original_minimizer_completePathTraffic_sq_le_of_count
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
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (Good : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → Prop)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B)
    (hcount : let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      ∀ s, Good s →
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) < (⊤ : ℝ≥0∞) ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real
          (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f) ≤
          κ * ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Good s → 2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
        (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
          (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal ^ 2 ≤
          3 * B * κ * (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η
            (fun z ↦ ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1) * f z)
              s).toReal := by
  dsimp only at hcount ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let A := legalMarkedCompletePathContributors (finrank ℝ S.covector.ker) d η f
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hA := measurableSet_legalMarkedCompletePathContributors d hd hη hf
  have hfiniteIntegral : (∫⁻ s, legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      d η f s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hf]
    exact ENNReal.mul_ne_top hηfinite hffinite
  have hfield := D.original_minimizer_canonical_normalized_momentum_field
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh
  filter_upwards [Q.full_matching, hfield.2.2,
    ae_lt_top (measurable_legalMarkedCompletePathTraffic d hd hη hf) hfiniteIntegral]
    with s hs herror hfinite
  intro hgood hlarge
  let V := (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support ∩ A
  have hV : MeasurableSet V :=
    (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).isClosed_support.measurableSet.inter hA
  have hcg := hcount s hgood
  have hfiniteV : (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V < (⊤ : ℝ≥0∞) :=
    (measure_mono inter_subset_right).trans_lt hcg.1
  have hcountV : (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).real V ≤
      κ * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ :=
    (measureReal_mono inter_subset_right hcg.1.ne).trans hcg.2
  have hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      e ∉ V → legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e = 0 := by
    filter_upwards [(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support_mem_ae]
      with e he hnot
    by_contra hnonzero
    exact hnot ⟨he, hnonzero⟩
  have hc := D.original_occupied_completePath_contributors_are_contractive hF hw T L
    hcut hclockRange η f hclock hηwindow hmask s hs herror
  let p := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    (Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m
  have hp : Measurable p :=
    (continuous_const.matrix_mulVec continuous_id).measurable.comp
      (measurable_originalSeedPairMomentum S hF hw)
  have hvbound : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict V,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e).toReal ≤ B := by
    filter_upwards [ae_restrict_mem hV] with e he
    exact hbound e he.2
  have hsq := legalMarkedCompletePathTraffic_sq_le_of_contractive_contributors d hd hη hf p hp
    s V hV hfiniteV hfinite.ne hzero (D.normalizedMomentumPhaseField T cut h L s)
    L.coe_nonneg (D.normalizedMomentumPhaseField_lipschitz T cut h L s)
    (originalNormalizedClockMobility S w T (cut + S.level) ell) hsmall
    (normalizedMomentumNodePosition S w T (cut + S.level)) hlarge hc hB hκ
    (show (0 : ℝ) ≤ 1 by norm_num) hvbound hcountV (by simp only [one_mul, le_refl])
  simpa only [mul_one, p, d, originalNormalizedMomentumMarkNorm] using hsq

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
