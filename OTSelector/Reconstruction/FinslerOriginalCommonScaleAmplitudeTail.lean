import OTSelector.Reconstruction.FinslerOriginalCommonScaleWholePathProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Amplitude tail for the common-scale whole-path probability wall

Markov's inequality turns a first-moment bound on the divided normalized
momentum field amplitude into an explicit tail estimate for the two amplitude
walls. Composing with the whole-path L2/Palm-square probability bound gives the
literal whole-path L2 statement off an event whose probability is bounded by the
exponential phase-walk tail plus the two Markov wall terms.
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

/-- Markov tail for a nonnegative measurable amplitude: a finite first moment
bounds the probability of exceeding any positive level. -/
theorem measureReal_lt_amplitude_le_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {amp : Ω → ℝ} (hamp : Measurable amp)
    {M H : ℝ} (hM0 : 0 ≤ M) (hH : 0 < H)
    (hint : (∫⁻ s, ENNReal.ofReal (amp s) ∂P) ≤ ENNReal.ofReal M) :
    P.real {s | H < amp s} ≤ M / H := by
  have hg : Measurable (fun s ↦ ENNReal.ofReal (amp s)) := hamp.ennreal_ofReal
  have hsub : {s | H < amp s} ⊆ {s | ENNReal.ofReal H ≤ ENNReal.ofReal (amp s)} :=
    fun s hs ↦ ENNReal.ofReal_le_ofReal hs.le
  have hmarkov : P {s | ENNReal.ofReal H ≤ ENNReal.ofReal (amp s)} ≤
      (∫⁻ s, ENNReal.ofReal (amp s) ∂P) / ENNReal.ofReal H :=
    meas_ge_le_lintegral_div hg.aemeasurable (ENNReal.ofReal_pos.mpr hH).ne'
      ENNReal.ofReal_ne_top
  have hdiv : (∫⁻ s, ENNReal.ofReal (amp s) ∂P) / ENNReal.ofReal H ≤
      ENNReal.ofReal (M / H) := by
    have hle : (∫⁻ s, ENNReal.ofReal (amp s) ∂P) / ENNReal.ofReal H ≤
        ENNReal.ofReal M / ENNReal.ofReal H := ENNReal.div_le_div_right hint _
    rwa [← ENNReal.ofReal_div_of_pos hH] at hle
  have hle : P {s | ENNReal.ofReal H ≤ ENNReal.ofReal (amp s)} ≤ ENNReal.ofReal (M / H) :=
    hmarkov.trans hdiv
  have hfin : P {s | ENNReal.ofReal H ≤ ENNReal.ofReal (amp s)} ≠ ⊤ :=
    (hle.trans_lt ENNReal.ofReal_lt_top).ne
  have h1 : P.real {s | H < amp s} ≤
      P.real {s | ENNReal.ofReal H ≤ ENNReal.ofReal (amp s)} := measureReal_mono hsub hfin
  have h2 : P.real {s | ENNReal.ofReal H ≤ ENNReal.ofReal (amp s)} ≤ M / H := by
    have hto := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := M / H)) hle
    simpa only [Measure.real, ENNReal.toReal_ofReal (div_nonneg hM0 hH.le)] using hto
  linarith

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Composed amplitude-tail statement: the literal whole-path traffic satisfies
the L2/Palm-square bound off the common-scale counting event, and that event's
probability is bounded by the exponential phase-walk tail plus the two Markov
amplitude-wall terms, with the field first moment as the explicit amplitude
parameter. -/
theorem ae_original_minimizer_commonScale_wholePath_memLp_two_amplitudeTail
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
    {B K M : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hM0 : 0 ≤ M)
    (hM : (∫⁻ s, ENNReal.ofReal (‖D.normalizedMomentumPhaseField T cut h
        ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
        s 0‖) ∂(Q.law : Measure
          (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ ENNReal.ofReal M)
    (hc1 : 0 < 2 * (ρ + 1)) (hc2 : 0 < 4 * (1 + (⟨Real.sqrt
        ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩ : ℝ≥0)) * A)
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
        M * (2 * (ρ + 1)) + M * (4 * (1 + (L : ℝ)) * A) := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
  let Bad := D.commonScaleCountBadEvent T cut h L ρ A radius K
  let amp : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ :=
    fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖
  have hamp : Measurable amp :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hM' : (∫⁻ s, ENNReal.ofReal (amp s) ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ ENNReal.ofReal M := by
    simpa only [amp, L] using hM
  have hprob := D.ae_original_minimizer_commonScale_wholePath_memLp_two_probability
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hmask hfinite hB hK hbound
  dsimp only at hprob
  have hw1 : (Q.law : Measure (LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker))).real {s | 1 < 2 * (ρ + 1) * amp s} ≤
      M * (2 * (ρ + 1)) := by
    have hset : {s | 1 < 2 * (ρ + 1) * amp s} = {s | 1 / (2 * (ρ + 1)) < amp s} := by
      ext s
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, div_lt_iff₀ hc1]
      constructor <;> intro h <;> linarith
    rw [hset]
    have htail := measureReal_lt_amplitude_le_moment (P := (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) hamp hM0
      (div_pos one_pos hc1) hM'
    calc (Q.law : Measure (LegalMarkedOptimalInputScene
          (finrank ℝ S.covector.ker))).real {s | 1 / (2 * (ρ + 1)) < amp s}
        ≤ M / (1 / (2 * (ρ + 1))) := htail
      _ = M * (2 * (ρ + 1)) := by field_simp
  have hw2 : (Q.law : Measure (LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker))).real {s | 1 < 4 * (1 + (L : ℝ)) * A * amp s} ≤
      M * (4 * (1 + (L : ℝ)) * A) := by
    have hc2' : 0 < 4 * (1 + (L : ℝ)) * A := hc2
    have hset : {s | 1 < 4 * (1 + (L : ℝ)) * A * amp s} =
        {s | 1 / (4 * (1 + (L : ℝ)) * A) < amp s} := by
      ext s
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, div_lt_iff₀ hc2']
      constructor <;> intro h <;> linarith
    rw [hset]
    have htail := measureReal_lt_amplitude_le_moment (P := (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) hamp hM0
      (div_pos one_pos hc2) hM'
    calc (Q.law : Measure (LegalMarkedOptimalInputScene
          (finrank ℝ S.covector.ker))).real
            {s | 1 / (4 * (1 + (L : ℝ)) * A) < amp s}
        ≤ M / (1 / (4 * (1 + (L : ℝ)) * A)) := htail
      _ = M * (4 * (1 + (L : ℝ)) * A) := by field_simp
  refine ⟨hprob.1, hprob.2.1, ?_⟩
  have htail := hprob.2.2
  calc (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real Bad
      ≤ Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
          (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
          2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1))) +
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          {s | 1 < 2 * (ρ + 1) * amp s} +
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          {s | 1 < 4 * (1 + (L : ℝ)) * A * amp s} := by
        simpa only [amp] using htail
    _ ≤ Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
          (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
          2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1))) +
        M * (2 * (ρ + 1)) + M * (4 * (1 + (L : ℝ)) * A) := by
        linarith [hw1, hw2]
end OriginalSeedConditionalMoments

end OTSelector.Reconstruction