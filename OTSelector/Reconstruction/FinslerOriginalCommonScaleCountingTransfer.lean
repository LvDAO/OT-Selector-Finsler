import OTSelector.Reconstruction.FinslerOriginalCommonScaleWholePathLtwo
import OTSelector.Reconstruction.FinslerOriginalCanonicalSourceContributorCounts

/-!
# Scaled-coordinate counting transfer for the common-scale L2 bound

The actual occupied positive contributors are counted on one measurable
good-event complement: the current-scale source phase-curve bad event at the
fixed integer phase scale one, together with the two fixed-amplitude walls. Off
that event the phase-walk envelope count theorem gives a genuine uniform bound
on the literal occupied contributor mass, independent of the scene. Feeding that
uniform count into the whole-path L2/Palm-square theorem closes the L2 step with
no remaining counting hypothesis.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The measurable counting-good-event complement: the current-scale source
phase-curve bad event at the fixed integer phase scale one, plus the two
fixed-amplitude walls that make the integer phase scale genuinely one. -/
def commonScaleCountBadEvent
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (ρ A radius K : ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :=
  D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
    {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖} ∪
      {s | 1 < 4 * (1 + (L : ℝ)) * A * ‖D.normalizedMomentumPhaseField T cut h L s 0‖}

theorem measurableSet_commonScaleCountBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (ρ A radius K : ℝ) :
    MeasurableSet (D.commonScaleCountBadEvent T cut h L ρ A radius K) := by
  have hfield : Measurable (fun s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) ↦
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  unfold commonScaleCountBadEvent
  apply MeasurableSet.union
  · apply MeasurableSet.union
    · exact D.measurableSet_normalizedSourcePhaseCurveBadEvent hF hw T hcut 1 radius K
    · exact measurableSet_lt measurable_const (measurable_const.mul hfield)
  · exact measurableSet_lt measurable_const (measurable_const.mul hfield)

/-- Uniform occupied-count transfer: off the measurable counting event the
literal actual occupied contributor measure is at most K, uniformly in the
scene. The count is the phase-walk envelope count at the fixed integer phase
scale one. -/
theorem ae_occupiedCount_le_of_not_commonScaleCountBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
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
    (K : ℝ) (hK : 0 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.commonScaleCountBadEvent T cut h L ρ A
        (max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))) K →
      (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker) d η f s) ≤
        ENNReal.ofReal K := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  have hcount := D.ae_original_minimizer_positiveTraffic_count_of_source_not_badEvent
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask (m := 1) (le_refl 1) K
  filter_upwards [hcount] with s hs
  intro hsnot
  unfold commonScaleCountBadEvent at hsnot
  have hsbad : s ∉ D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K :=
    fun h ↦ hsnot (Or.inl (Or.inl h))
  have hroot : 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ (1 : ℝ) :=
    not_lt.mp fun hlt ↦ hsnot (Or.inl (Or.inr hlt))
  have hspeed : 4 * (1 + (L : ℝ)) * A *
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ (1 : ℝ) :=
    not_lt.mp fun hlt ↦ hsnot (Or.inr hlt)
  have hc := hs hsbad (by simpa only [L, Nat.cast_one] using hroot)
    (by simpa only [L, Nat.cast_one] using hspeed)
  have hfin : ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
      (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker) d η f)) <
        (⊤ : ℝ≥0∞) := hc.1
  have hrealK : ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
      (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker) d η f)).toReal ≤ K := by
    have h := hc.2
    simpa only [Nat.cast_one, mul_one] using h.le
  calc ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker) d η f s))
      ≤ ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (legalMarkedCompletePathContributors (finrank ℝ S.covector.ker) d η f)) :=
        measure_mono inter_subset_right
    _ ≤ ENNReal.ofReal K := (ENNReal.le_ofReal_iff_toReal_le hfin.ne hK).mpr hrealK

/-- Full L2/Palm-square bound for the literal whole path, with the uniform
occupied-count bound derived from the scaled-coordinate counting transfer. No
occupied-count hypothesis remains; only the measurable counting event (whose
probability is controlled separately) and the original single-edge bound. -/
theorem ae_original_minimizer_commonScale_wholePath_memLp_two_of_count
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
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
    (hη : Measurable η) (hf : Measurable f)
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (hfinite : (∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≤ ENNReal.ofReal B) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1
    let Bad := D.commonScaleCountBadEvent T cut h L ρ A
      (max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))) K
    MemLp (Badᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ s, (Badᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d η f z).toReal) s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      (B * K) * ((∫⁻ x, η x ∂(volume : Measure
          (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let Bad := D.commonScaleCountBadEvent T cut h L ρ A radius K
  have hBad : MeasurableSet Bad :=
    D.measurableSet_commonScaleCountBadEvent hF hw T hcut h L ρ A radius K
  have hcount := D.ae_occupiedCount_le_of_not_commonScaleCountBadEvent hF hw hgap hbounds T
    hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip hclock hηwindow hmask K hK
  refine ae_wholePath_memLp_two_of_uniformOccupiedCount Q d
    (measurable_originalSeedPathOffset_joint S hF hw) hη hf hfinite hBad hB hK hbound ?_
  simpa only [Bad, radius] using hcount

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
