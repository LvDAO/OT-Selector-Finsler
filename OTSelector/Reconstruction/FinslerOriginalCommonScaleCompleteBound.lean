import OTSelector.Reconstruction.FinslerOriginalCommonScaleUnconditionalBound
import OTSelector.Reconstruction.OriginalMinimizerBoundedPhaseTrafficLtwo
import OTSelector.Reconstruction.OriginalCountTailOnEventCompletePathAELtwo
import OTSelector.Reconstruction.FinslerOriginalBoundedPhaseOriginalCounts

/-!
# Bounded-phase squared-integral certificate with an explicit constant

The pre-existing bounded-phase module proves that bounded-phase traffic is L2 but
does not expose the counting constant. Here the same on-event count-tail bound is
applied a second time, capturing both conjuncts, which yields the explicit
bounded-phase certificate

  CB = 8 * B^2 * exp (Lambda * (exp 1 - 1)) * exp (1/2),

where Lambda is the literal source cell intensity at the bounded-phase counting
radius max (2 H + 2 (La + b)) (a + rho (2 H + 2 (La + b))). The index is K = -1,
so the count tail is the whole bounded set and its exponential factor is
exp (-(-1)/2) = exp (1/2).
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology
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

/-- Bounded-phase traffic squares are integrable with the explicit count-tail
constant: MemLp plus the literal squared-integral bound with
8 B^2 exp (Lambda (e - 1)) exp (1/2). -/
theorem ae_boundedPhase_sq_integral_le
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
    let b := Real.sqrt (8 * |t| * G / h)
    let PB := 2 * H + 2 * ((L : ℝ) * a + b)
    let radius := max PB (a + ρ * PB)
    let W := D.normalizedSourcePhaseCell T cut 0 0 radius
    MemLp ({s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}.indicator
      (fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ x, ({s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}.indicator
      (fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal) x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      8 * B ^ 2 * Real.exp ((((volume : Measure
          (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ) W).toReal *
            (Real.exp 1 - 1)) * Real.exp (1 / 2) := by
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
  let Small := {s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) |
    ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}
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
  refine ⟨?_, ?_⟩
  · simpa only [hall, indicator_univ] using ht.1
  · simpa only [hall, indicator_univ, neg_neg, neg_div] using ht.2.1

/-- Complete unconditional whole-path bound with explicit constants: the
bounded-phase certificate is supplied by the explicit constant theorem above, the
amplitude-one large branch is fully instantiated inside the unconditional bound,
and the only remaining external input is the retained canonical certificate
(whose application is the same single step as in the certified bound). -/
theorem ae_original_minimizer_commonScale_completeBound_of_certificate
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
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
    {ρ A : ℝ}
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
        ENNReal.ofReal B)
    {radK Blarge : ℝ}
    (hCertLp : MemLp (Set.indicator {s |
        ((Nat.floor (canonicalPhaseCurveScaleCoefficient
          ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) ρ A) : ℕ) : ℝ) ≤
          (D.normalizedCanonicalCurveIntegerScale T cut h
            ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
              Real.sqrt_nonneg _⟩ ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h
          ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ s 0‖ ∧
          2 * (((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) * a +
              Real.sqrt (8 * |t| * G / h)) ≤
            ‖D.normalizedMomentumPhaseField T cut h
              ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
                Real.sqrt_nonneg _⟩ s 0‖} (fun s ↦
        (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
          (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (hCertInt : (∫ x, (Set.indicator {s |
        ((Nat.floor (canonicalPhaseCurveScaleCoefficient
          ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) ρ A) : ℕ) : ℝ) ≤
          (D.normalizedCanonicalCurveIntegerScale T cut h
            ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
              Real.sqrt_nonneg _⟩ ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h
          ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ s 0‖ ∧
          2 * (((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) * a +
              Real.sqrt (8 * |t| * G / h)) ≤
            ‖D.normalizedMomentumPhaseField T cut h
              ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
                Real.sqrt_nonneg _⟩ s 0‖} (fun s ↦
        (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
          (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal) x) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        Blarge) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let d : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) := fun z ↦ originalSeedPathOffset S w z.2 z.1
    let Hbc := max 1 (2 * ((L : ℝ) * a + b))
    let PB := 2 * Hbc + 2 * ((L : ℝ) * a + b)
    let Wbc := D.normalizedSourcePhaseCell T cut 0 0 (max PB (a + ρ * PB))
    let CB := 8 * B ^ 2 * Real.exp ((((volume : Measure
          (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ) Wbc).toReal *
            (Real.exp 1 - 1)) * Real.exp (1 / 2)
    let phaseBad := D.normalizedSourcePhaseCurveBadEvent T cut 1 radK K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic
      (finrank ℝ S.covector.ker) d η f s).toReal
    MemLp (phaseBadᶜ.indicator traffic) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ x, (phaseBadᶜ.indicator traffic x) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        2 * CB + 2 * Blarge := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) := fun z ↦ originalSeedPathOffset S w z.2 z.1
  let Hbc := max 1 (2 * ((L : ℝ) * a + b))
  let PB := 2 * Hbc + 2 * ((L : ℝ) * a + b)
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic
    (finrank ℝ S.covector.ker) d η f s).toReal
  have hHbc : 0 ≤ Hbc := by
    have : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans this (le_max_left 1 (2 * ((L : ℝ) * a + b)))
  have hbdd := D.ae_boundedPhase_sq_integral_le hF hw hgap hbounds T hg hgb t Q hmin
    hcut hh hclockRange hsmall hR hclock hηwindow hmask ha (H := Hbc) hHbc hη hf hB hsingle
  dsimp only at hbdd
  have hmain := D.ae_original_minimizer_commonScale_unconditional_of_boundedPhase
    hF hw T hcut h L ρ A a b radK K
    (8 * B ^ 2 * Real.exp ((((volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 (max PB (a + ρ * PB)))).toReal *
        (Real.exp 1 - 1)) * Real.exp (1 / 2))
    Blarge Q hbdd.1 hbdd.2 hCertLp hCertInt
  exact ⟨hmain.1, hmain.2.1⟩

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
