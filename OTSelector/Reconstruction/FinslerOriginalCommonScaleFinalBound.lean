import OTSelector.Reconstruction.FinslerOriginalCommonScaleBranchCertificates
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
theorem ae_original_minimizer_commonScale_finalBound
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
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≤ ENNReal.ofReal B)
    {H Hc Blarge : ℝ} {N : ℕ}
    (hHc : Hc = max H (2 * (((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
        Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) * a + Real.sqrt (8 * |t| * G / h))))
    (hH1 : Hc ≤ 1 / (2 * (ρ + 1)))
    (hH2 : Hc ≤ 1 / (4 * (1 +
      ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
        Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ)) * A))
    (hc1 : 0 < 2 * (ρ + 1))
    (hc2 : 0 < 4 * (1 + ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
        Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ)) * A)
    (hH : 1 ≤ H) (hN : 1 ≤ N)
    (hNH : (N : ℝ) ≤ canonicalPhaseCurveScaleCoefficient
      ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
        Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) ρ A * H)
    (hCertLp : MemLp (Set.indicator {s | (N : ℝ) ≤
        (D.normalizedCanonicalCurveIntegerScale T cut h
          ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩ ρ A s : ℝ) ∧
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
    (hCertInt : (∫ x, (Set.indicator {s | (N : ℝ) ≤
        (D.normalizedCanonicalCurveIntegerScale T cut h
          ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩ ρ A s : ℝ) ∧
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
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ Blarge) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let d : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) := fun z ↦ originalSeedPathOffset S w z.2 z.1
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    let phaseBad := D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic
      (finrank ℝ S.covector.ker) d η f s).toReal
    MemLp (phaseBadᶜ.indicator traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ x, (phaseBadᶜ.indicator traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      2 * ((B * K) * ((∫⁻ x, η x ∂(volume : Measure
          (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal) + 2 * Blarge ∧
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
  have hHcL : Hc = max H (2 * ((L : ℝ) * a + b)) := hHc
  have hH1L : Hc ≤ 1 / (2 * (ρ + 1)) := hH1
  have hH2L : Hc ≤ 1 / (4 * (1 + (L : ℝ)) * A) := hH2
  have hc2L : 0 < 4 * (1 + (L : ℝ)) * A := hc2
  have hNHL : (N : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A * H := hNH
  have hmeas : Measurable amp :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hcount := D.ae_original_minimizer_commonScale_wholePath_memLp_two_of_count
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hmask hfinite hB hK hbound
  dsimp only at hcount
  have hsub : D.commonScaleCountBadEvent T cut h L ρ A radius K ⊆
      phaseBad ∪ {s | Hc < amp s} := by
    simpa only [phaseBad, amp, radius] using
      (D.commonScaleCountBadEvent_subset_amplitudeTruncation hF hw T hcut h L ρ A radius K
        (H := Hc) hH1L hH2L hc1 hc2L)
  have hBad : MeasurableSet (phaseBad ∪ {s | Hc < amp s}) :=
    (D.measurableSet_normalizedSourcePhaseCurveBadEvent hF hw T hcut 1 radius K).union
      (measurableSet_lt measurable_const hmeas)
  obtain ⟨hSmallLp0, hSmallInt0⟩ := smallBranch_of_counting hsub hBad hcount.1 hcount.2
  have hCertLp' : MemLp (Set.indicator {s | (N : ℝ) ≤
      (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s} traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    exact hCertLp
  have hCertInt' : (∫ x, (Set.indicator {s | (N : ℝ) ≤
      (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ amp s ∧ 2 * ((L : ℝ) * a + b) ≤ amp s} traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      Blarge := by
    exact hCertInt
  obtain ⟨hLargeLp, hLargeInt⟩ := D.ae_largeAmplitudeBranch_sq_integral_le
    hF hw T hcut h L ρ A (a := a) (b := b) (H := H) (B := Blarge) (N := N)
    hH hN hNHL hCertLp' hCertInt'
  have hLargeLp' : MemLp (Set.indicator {s | 2 * ((L : ℝ) * a + b) ≤ amp s ∧
      H < amp s} traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    simpa only [amp, and_comm] using hLargeLp
  have hLargeInt' : (∫ x, (Set.indicator {s | 2 * ((L : ℝ) * a + b) ≤ amp s ∧
      H < amp s} traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      Blarge := by
    simpa only [amp, and_comm] using hLargeInt
  have hSmallLp' : MemLp (Set.indicator ({s | Hc < amp s} ∪ phaseBad)ᶜ traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    simpa only [Set.union_comm] using hSmallLp0
  have hSmallInt' : (∫ x, (Set.indicator ({s | Hc < amp s} ∪ phaseBad)ᶜ traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      (B * K) * ((∫⁻ x, η x ∂(volume : Measure
          (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal := by
    simpa only [Set.union_comm] using hSmallInt0
  exact D.ae_original_minimizer_commonScale_twoBranch_probability hF hw T hcut h L ρ A a b
    radius K (H := H) (Hc := Hc) (Q := Q) (traffic := traffic)
    (CA := (B * K) * ((∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal)
    (CL := Blarge) hHcL hSmallLp' hSmallInt' hLargeLp' hLargeInt'

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
