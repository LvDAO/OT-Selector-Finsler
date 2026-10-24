import OTSelector.Reconstruction.OriginalInputBadEventSecondMoment
import OTSelector.Reconstruction.FinslerNormalizedAdaptiveTargetPhaseCurveCounts

/-! # Actual original phase-curve bad events have exponentially small L2 count cost -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- On the literal all-candidate original-input bad event, any complete
original target envelope of finite intensity has the actual quantitative
mean-square bound. Neither count/event independence nor an adaptive Poisson
law is assumed. -/
theorem normalizedTargetPhaseCurveBadEvent_count_second_moment
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (r K : ℝ) {B : Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))}
    (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν) B ≠ (∞ : ℝ≥0∞)) :
    let N : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ := fun s ↦
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))) (B ×ˢ {1})).toReal
    let v := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.normalizedTargetPhaseCell T cut 0 0 (r + 2))).toReal
    Integrable (fun s ↦ ((D.normalizedTargetPhaseCurveBadEvent T cut m r K).indicator N s) ^ 2)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, ((D.normalizedTargetPhaseCurveBadEvent T cut m r K).indicator N s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        (192 * Real.exp (Real.exp 1 - 1) *
          (1 + (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν) B).toReal ^ 4)) ^
            (1 / 2 : ℝ) *
          Real.exp ((-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
            (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) - 2 * v * (Real.exp 1 - 1)) *
              (m : ℝ)) * (1 / 2 : ℝ)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have h2 := Q.original_target_badEvent_second_moment hB hfin
    (D.measurableSet_normalizedTargetPhaseCurveBadEvent hF hw T hcut m r K)
  have hp := D.normalizedTargetPhaseCurveBadEvent_measure_le hF hw T hcut hm Q r K
  dsimp only at h2 hp ⊢
  refine ⟨h2.1, h2.2.trans ?_⟩
  rw [Real.exp_mul]
  gcongr

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
