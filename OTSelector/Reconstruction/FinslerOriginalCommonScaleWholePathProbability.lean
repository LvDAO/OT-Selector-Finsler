import OTSelector.Reconstruction.FinslerOriginalCommonScaleCountingTransfer
import OTSelector.Reconstruction.FinslerNormalizedAdaptivePhaseCurveCounts

/-!
# Bad-event probability tail for the common-scale whole-path L2 bound

The counting event of the common-scale whole-path L2 bound splits into the
current-scale source phase-curve bad event at the fixed integer phase scale one
and the two fixed-amplitude walls. The phase-walk count theorem bounds the first
part by its exact exponential tail with threshold given by the normalized source
cell intensity at the tube radius; the two amplitude walls are retained
explicitly as separate probability terms. This is composed with the literal
whole-path L2/Palm-square bound, which now holds off an event with a genuine
exponential tail rather than an abstract counting hypothesis.
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

/-- Probability tail of the common-scale counting event. The source phase-curve
part is bounded by the exact exponential normalized phase-walk tail at the tube
radius; the two amplitude walls remain as explicit probability terms. -/
theorem commonScaleCountBadEvent_measure_real_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (ρ A radius K : ℝ)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        (D.commonScaleCountBadEvent T cut h L ρ A radius K) ≤
      Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
          (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
          2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1))) +
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖} +
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          {s | 1 < 4 * (1 + (L : ℝ)) * A *
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} := by
  have hbad := D.normalizedSourcePhaseCurveBadEvent_measure_le hF hw T hcut
    (m := 1) (le_refl 1) Q radius K
  dsimp only at hbad
  simp only [Nat.cast_one, mul_one] at hbad
  rw [show D.commonScaleCountBadEvent T cut h L ρ A radius K =
      D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
        {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖} ∪
          {s | 1 < 4 * (1 + (L : ℝ)) * A *
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} from rfl]
  calc
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
          {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖}) ∪
          {s | 1 < 4 * (1 + (L : ℝ)) * A *
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖})
        ≤ (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
            (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
              {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖}) +
          (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
            {s | 1 < 4 * (1 + (L : ℝ)) * A *
              ‖D.normalizedMomentumPhaseField T cut h L s 0‖} :=
          measureReal_union_le _ _
    _ ≤ ((Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
            (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) +
          (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
            {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖}) +
          (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
            {s | 1 < 4 * (1 + (L : ℝ)) * A *
              ‖D.normalizedMomentumPhaseField T cut h L s 0‖} := by
          have h := measureReal_union_le
            (s₁ := D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)
            (s₂ := {s | 1 < 2 * (ρ + 1) *
              ‖D.normalizedMomentumPhaseField T cut h L s 0‖})
            (μ := (Q.law : Measure
              (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
          linarith
    _ ≤ _ := by linarith [hbad]

/-- Composed statement: the literal whole-path traffic satisfies the
L2/Palm-square bound off the common-scale counting event, and that event has an
explicit probability tail: the exact exponential normalized phase-walk tail at
the tube radius plus the two amplitude-wall probabilities. -/
theorem ae_original_minimizer_commonScale_wholePath_memLp_two_probability
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
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
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let Bad := D.commonScaleCountBadEvent T cut h L ρ A radius K
    MemLp (Badᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ s, (Badᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d η f z).toReal) s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      (B * K) * ((∫⁻ x, η x ∂(volume : Measure
          (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal ∧
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real Bad ≤
      Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
          (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
          2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1))) +
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖} +
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          {s | 1 < 4 * (1 + (L : ℝ)) * A *
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let Bad := D.commonScaleCountBadEvent T cut h L ρ A radius K
  have hL2 := D.ae_original_minimizer_commonScale_wholePath_memLp_two_of_count
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hmask hfinite hB hK hbound
  have hprob := D.commonScaleCountBadEvent_measure_real_le hF hw T hcut h L ρ A radius K Q
  dsimp only at hL2
  exact ⟨hL2.1, hL2.2, by simpa only [L, radius] using hprob⟩

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction