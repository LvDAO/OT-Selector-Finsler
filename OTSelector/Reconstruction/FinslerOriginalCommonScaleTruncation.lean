import OTSelector.Reconstruction.FinslerOriginalCommonScaleCountingTransfer
import OTSelector.Reconstruction.FinslerOriginalCommonScaleWholePathProbability
import OTSelector.Reconstruction.FinslerNormalizedAdaptivePhaseCurveCounts

/-!
# Truncation route for the normalized momentum field amplitude branch

The infinite-volume node-position integral prevents a finite Markov amplitude
first moment. This file implements the truncation alternative: for a fixed
amplitude truncation level H below the two counting walls, the counting bad event
of the whole-path L2 chain is contained in the phase-curve bad event together
with the complementary truncation event {H < amplitude}. Therefore the whole-path
L2/Palm-square bound transfers to the truncated branch off an event whose
non-truncation part is the phase-curve bad event, which carries the exact
exponential phase-walk tail. The remaining branch is the large-amplitude
complement {amplitude > H}, handled separately.
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

/-- Truncation transfer: a whole-path L2/Palm-square bound holding off a smaller
measurable bad event transfers to any larger measurable bad event, and the
squared integral only decreases. -/
theorem memLp_two_indicator_of_bad_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {BadCount Bad : Set Ω} (hsub : BadCount ⊆ Bad)
    (hBad : MeasurableSet Bad) {C : ℝ}
    (hLp : MemLp (BadCountᶜ.indicator f) 2 P)
    (hInt : (∫ x, (BadCountᶜ.indicator f x) ^ 2 ∂P) ≤ C) :
    MemLp (Badᶜ.indicator f) 2 P ∧
      (∫ x, (Badᶜ.indicator f x) ^ 2 ∂P) ≤ C := by
  have hind : Badᶜ.indicator f = Badᶜ.indicator (BadCountᶜ.indicator f) := by
    funext x
    by_cases hx : x ∈ Badᶜ
    · have hx' : x ∈ BadCountᶜ := fun h ↦ hx (hsub h)
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · simp only [Set.indicator_of_notMem hx]
  have hLp' : MemLp (Badᶜ.indicator (BadCountᶜ.indicator f)) 2 P := by
    refine MemLp.of_le_mul (g := BadCountᶜ.indicator f) (c := 1) hLp
      (hLp.aestronglyMeasurable.indicator hBad.compl) ?_
    filter_upwards with x
    by_cases hx : x ∈ Badᶜ
    · have hx' : x ∈ BadCountᶜ := fun h => hx (hsub h)
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      simp
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      positivity
  refine ⟨?_, ?_⟩
  · rw [hind]
    exact hLp'
  · have hpt : ∀ x, (Badᶜ.indicator (BadCountᶜ.indicator f) x) ^ 2 ≤
        (BadCountᶜ.indicator f x) ^ 2 := by
      intro x
      by_cases hx : x ∈ Badᶜ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        nlinarith [sq_nonneg (BadCountᶜ.indicator f x)]
    have hInt' : Integrable (fun x ↦ (BadCountᶜ.indicator f x) ^ 2) P := hLp.integrable_sq
    have hInt'' : Integrable (fun x ↦ (Badᶜ.indicator (BadCountᶜ.indicator f) x) ^ 2) P :=
      hLp'.integrable_sq
    calc (∫ x, (Badᶜ.indicator f x) ^ 2 ∂P)
        = ∫ x, (Badᶜ.indicator (BadCountᶜ.indicator f) x) ^ 2 ∂P := by rw [hind]
      _ ≤ ∫ x, (BadCountᶜ.indicator f x) ^ 2 ∂P :=
          integral_mono_ae hInt'' hInt' (ae_of_all _ hpt)
      _ ≤ C := hInt

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Below the two counting walls, the common-scale counting bad event is
contained in the phase-curve bad event together with the complementary amplitude
truncation event. This removes the amplitude walls from the bad event at the cost
of the explicit truncation complement. -/
theorem commonScaleCountBadEvent_subset_amplitudeTruncation
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ)
    (L : ℝ≥0) (ρ A radius K : ℝ) {H : ℝ}
    (hH1 : H ≤ 1 / (2 * (ρ + 1))) (hH2 : H ≤ 1 / (4 * (1 + (L : ℝ)) * A))
    (hc1 : 0 < 2 * (ρ + 1)) (hc2 : 0 < 4 * (1 + (L : ℝ)) * A) :
    D.commonScaleCountBadEvent T cut h L ρ A radius K ⊆
      D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
        {s | H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖} := by
  intro s hs
  simp only [commonScaleCountBadEvent, Set.mem_union, Set.mem_setOf_eq] at hs
  rcases hs with (hbad | hwall1) | hwall2
  · exact Or.inl hbad
  · refine Or.inr ?_
    by_contra hle
    have hle' : ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H := not_lt.mp hle
    have hmono : 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
        2 * (ρ + 1) * H := by
      have := mul_le_mul_of_nonneg_left hle' (le_of_lt hc1)
      linarith
    have hbound : 2 * (ρ + 1) * H ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hH1 (le_of_lt hc1)
      rw [mul_one_div, div_self hc1.ne'] at this
      linarith
    linarith
  · refine Or.inr ?_
    by_contra hle
    have hle' : ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H := not_lt.mp hle
    have hmono : 4 * (1 + (L : ℝ)) * A *
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ 4 * (1 + (L : ℝ)) * A * H := by
      have := mul_le_mul_of_nonneg_left hle' (le_of_lt hc2)
      linarith
    have hbound : 4 * (1 + (L : ℝ)) * A * H ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hH2 (le_of_lt hc2)
      rw [mul_one_div, div_self hc2.ne'] at this
      linarith
    linarith

/-- The truncated bad event is Borel. -/
theorem measurableSet_amplitudeTruncationBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ)
    (L : ℝ≥0) (radius K H : ℝ) :
    MeasurableSet (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
      {s | H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖}) :=
  MeasurableSet.union
    (D.measurableSet_normalizedSourcePhaseCurveBadEvent hF hw T hcut 1 radius K)
    (measurableSet_lt measurable_const
      (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
        (measurable_id.prodMk measurable_const)).norm))

/-- Exact exponential probability tail of the non-truncation part of the
truncated bad event, at the fixed integer phase scale one. -/
theorem normalizedSourcePhaseCurveBadEvent_one_measure_real_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (radius K : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) ≤
      Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
          (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
          2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1))) := by
  have hp := D.normalizedSourcePhaseCurveBadEvent_measure_le hF hw T hcut
    (m := 1) (le_refl 1) Q radius K
  dsimp only at hp
  simpa only [Nat.cast_one, mul_one] using hp

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
