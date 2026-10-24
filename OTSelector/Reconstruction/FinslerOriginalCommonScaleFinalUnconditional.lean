import OTSelector.Reconstruction.FinslerOriginalCommonScaleFinalBound
import OTSelector.Reconstruction.FinslerOriginalCommonScaleCompleteBound
import OTSelector.Reconstruction.FinslerOriginalLargeWindowTrafficExpectation
import OTSelector.Reconstruction.FinslerOriginalCommonScaleLargeAmplitude
import OTSelector.Reconstruction.FinslerOriginalCommonScaleTwoBranch

/-!
# Final whole-path two-branch bound with explicit probability tail

This file performs the final branch-certificate applications:

* the small/truncation branch certificate is produced by applying the counting
  good-event L2 theorem and transferring it through the wall-to-truncation
  containment at level Hc = max H (2(La+b));
* the large-amplitude branch certificate is produced from the large-amplitude
  module (with the current-scale certificate passed in);
* the two branch certificates are spliced by the two-branch theorem, which also
  supplies the exact exponential phase-bad-event probability tail.

The result is the literal whole-path L2/Palm-square bound off the phase-curve bad
event, with explicit branch coefficients and explicit probability deficit.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Final two-branch whole-path L2 bound with explicit probability tail. The
small-branch certificate is produced from the counting good-event L2 theorem via
the truncation containment; the large-branch certificate is passed in from the
large-amplitude module; the splice and the exponential phase tail are the
two-branch theorem. -/
theorem ae_certificate_at_amplitude_one
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
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≤ ENNReal.ofReal B)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    (hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    (hKthreshold :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      D.normalizedSourcePhaseCurveCountThreshold T cut radius ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let d : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) := fun z ↦ originalSeedPathOffset S w z.2 z.1
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic
      (finrank ℝ S.covector.ker) d η f s).toReal
    let error := fun N : ℕ ↦ ∫ s, (({s | N ≤ k s ∧ s ∈
      D.normalizedSourcePhaseCurveBadEvent T cut (k s) radius K}).indicator traffic s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    let weightedPalmMoment := ((∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    MemLp (Set.indicator {s | ((Nat.floor C : ℕ) : ℝ) ≤ (k s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ x, (Set.indicator {s | ((Nat.floor C : ℕ) : ℝ) ≤ (k s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic x) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        (3 * B * (K * (C + 1))) * weightedPalmMoment + error (Nat.floor C)
  := by

  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) := fun z ↦ originalSeedPathOffset S w z.2 z.1
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let phaseBad := D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic
    (finrank ℝ S.covector.ker) d η f s).toReal
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
  have hfinite : (∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top hηfinite hffinite
  have hbound' : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B := by
    intro e he
    have hle := hbound e he
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    simpa only [ENNReal.toReal_ofReal hB] using ht
  have hKthr : D.normalizedSourcePhaseCurveCountThreshold T cut radius ≤ K := hKthreshold
  have hlarge := D.original_minimizer_largeCanonicalTraffic_source_sq_integral_le
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite (B := B) hB hbound' hpfinite
    (K := K) hKthr
  dsimp only at hlarge
  have hmeas : Measurable amp :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d
      (measurable_originalSeedPathOffset_joint S hF hw) hη hf).ennreal_toReal
  have hk : Measurable k :=
    D.measurable_normalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A
  have hC1 : (1 : ℝ) ≤ C := (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1
  have hNpos : 1 ≤ Nat.floor C := Nat.le_floor (by simpa only [Nat.cast_one] using hC1)
  have hcertmeas : MeasurableSet {s | Nat.floor C ≤ k s ∧ 1 ≤ amp s ∧
      2 * ((L : ℝ) * a + b) ≤ amp s} :=
    (measurableSet_le measurable_const hk).inter
      ((measurableSet_le measurable_const hmeas).inter
        (measurableSet_le measurable_const hmeas))
  have hcertset : {s | ((Nat.floor C : ℕ) : ℝ) ≤ (k s : ℝ) ∧ 1 ≤ amp s ∧
      2 * ((L : ℝ) * a + b) ≤ amp s} =
      {s | Nat.floor C ≤ k s ∧ 1 ≤ amp s ∧
        2 * ((L : ℝ) * a + b) ≤ amp s} := by
    ext s
    simp only [Set.mem_ofPred_eq, Nat.cast_le]
  have hCertLp : MemLp (Set.indicator {s | ((Nat.floor C : ℕ) : ℝ) ≤ (k s : ℝ) ∧
      1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s} traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    rw [hcertset]
    exact (memLp_two_iff_integrable_sq
      (htraffic.aestronglyMeasurable.indicator hcertmeas)).mpr
      (hlarge.1 (Nat.floor C) hNpos).1
  let weightedPalmMoment := ((∫⁻ x, η x ∂(volume : Measure
      (Fin (finrank ℝ S.covector.ker) → ℝ))) *
    (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
  let err := fun N : ℕ ↦ ∫ s, (({s | N ≤ k s ∧ s ∈
    D.normalizedSourcePhaseCurveBadEvent T cut (k s) radius K}).indicator traffic s) ^ 2
    ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
  let CL := (3 * B * (K * (C + 1))) * weightedPalmMoment + err (Nat.floor C)
  have hCertInt : (∫ x, (Set.indicator {s | ((Nat.floor C : ℕ) : ℝ) ≤ (k s : ℝ) ∧
      1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s} traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ CL := by
    rw [hcertset]
    exact (hlarge.1 (Nat.floor C) hNpos).2
  exact ⟨hCertLp, hCertInt⟩

/-- Fully unconditional final whole-path bound with explicit constants. The
retained certificate at amplitude one is applied above; the bounded-phase
certificate is the explicit count-tail constant; the amplitude-one large branch
is instantiated inside the complete bound; the exponential phase tail is the
two-branch probability estimate. No wall hypotheses and no certificate inputs
remain. -/
theorem ae_original_minimizer_commonScale_finalUnconditional
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
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≤ ENNReal.ofReal B)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    (hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    (hKthreshold :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      D.normalizedSourcePhaseCurveCountThreshold T cut radius ≤ K)
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
        ENNReal.ofReal B) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let d : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) := fun z ↦ originalSeedPathOffset S w z.2 z.1
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let Hbc := max 1 (2 * ((L : ℝ) * a + b))
    let PB := 2 * Hbc + 2 * ((L : ℝ) * a + b)
    let Wbc := D.normalizedSourcePhaseCell T cut 0 0 (max PB (a + ρ * PB))
    let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let phaseBad := D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic
      (finrank ℝ S.covector.ker) d η f s).toReal
    let error := fun N : ℕ ↦ ∫ s, (({s | N ≤ k s ∧ s ∈
      D.normalizedSourcePhaseCurveBadEvent T cut (k s) radius K}).indicator traffic s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    let weightedPalmMoment := ((∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    let CB := 8 * B ^ 2 * Real.exp ((((volume : Measure
          (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ) Wbc).toReal *
            (Real.exp 1 - 1)) * Real.exp (1 / 2)
    let CL := (3 * B * (K * (C + 1))) * weightedPalmMoment + error (Nat.floor C)
    MemLp (phaseBadᶜ.indicator traffic) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ x, (phaseBadᶜ.indicator traffic x) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        2 * CB + 2 * CL ∧
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          phaseBad ≤
        Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
            (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
            2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
              (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
              (Real.exp 1 - 1))) := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) := fun z ↦ originalSeedPathOffset S w z.2 z.1
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let amp := fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  let phaseBad := D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic
    (finrank ℝ S.covector.ker) d η f s).toReal
  let C := canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A
  let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
  let err := fun N : ℕ ↦ ∫ s, (({s | N ≤ k s ∧ s ∈
    D.normalizedSourcePhaseCurveBadEvent T cut (k s) radius K}).indicator traffic s) ^ 2
    ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
  let weightedPalmMoment := ((∫⁻ x, η x ∂(volume : Measure
      (Fin (finrank ℝ S.covector.ker) → ℝ))) *
    (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
  have hcert := D.ae_certificate_at_amplitude_one hF hw hgap hbounds T hg hgb t Q hmin
    hcut hh ha hclockRange hsmall hA hR hRLip hη hf hclock hηwindow hmask
    (B := B) (K := K) hB hK hbound hηfinite hffinite hpfinite hKthreshold
  dsimp only at hcert
  have hcomp := D.ae_original_minimizer_commonScale_completeBound_of_certificate
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall
    (ρ := ρ) (A := A) hR hη hf hclock hηwindow hmask hB hsingle
    (K := K) (radK := radius) (Blarge := (3 * B * (K * (C + 1))) * weightedPalmMoment +
      err (Nat.floor C)) hcert.1 hcert.2
  dsimp only at hcomp
  have htail := D.normalizedSourcePhaseCurveBadEvent_one_measure_real_le hF hw T hcut Q radius K
  exact ⟨hcomp.1, hcomp.2, htail⟩

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
