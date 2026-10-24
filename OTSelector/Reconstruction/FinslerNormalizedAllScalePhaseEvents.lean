import OTSelector.Probability.GeometricBadEventUnion
import OTSelector.Reconstruction.FinslerNormalizedAdaptivePhaseCurveCounts
import OTSelector.Reconstruction.FinslerNormalizedAdaptiveTargetPhaseCurveCounts

/-! One fixed original-data event controls every natural phase scale,
with an internally available threshold from the exact normalized cell rate. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- A deterministic threshold uses the exact original source congruence-cell intensity. -/
def normalizedSourcePhaseCurveCountThreshold
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut r : ℝ) : ℝ :=
  (3 * (2 * finrank ℝ S.covector.ker : ℝ) + (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
    2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 (r + 2))).toReal * (Real.exp 1 - 1) + 1

theorem normalizedSourcePhaseCurveCountThreshold_pos
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut r : ℝ) : 0 < D.normalizedSourcePhaseCurveCountThreshold T cut r := by
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr zero_le_one)
  unfold normalizedSourcePhaseCurveCountThreshold
  positivity

/-- This event depends on complete original input counts at all fixed scales ≥ N. -/
def normalizedSourcePhaseCurveAllScaleBadEvent
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (N : ℕ) (r K : ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :=
  natTailEventUnion (fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m r K) N

theorem measurableSet_normalizedSourcePhaseCurveAllScaleBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (N : ℕ) (r K : ℝ) :
    MeasurableSet (D.normalizedSourcePhaseCurveAllScaleBadEvent T cut N r K) :=
  measurableSet_natTailEventUnion
    (fun m ↦ D.measurableSet_normalizedSourcePhaseCurveBadEvent hF hw T hcut m r K) N

/-- The actual original Poisson law gives a simultaneous exponential tail.
Its threshold is the true normalized cell intensity, without a frame loss. -/
theorem normalizedSourcePhaseCurveAllScaleBadEvent_measure_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (r : ℝ) {K : ℝ} (hK : D.normalizedSourcePhaseCurveCountThreshold T cut r ≤ K)
    {N : ℕ} (hN : 1 ≤ N) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
      (D.normalizedSourcePhaseCurveAllScaleBadEvent T cut N r K) ≤
      Real.exp (-(N : ℝ)) / (1 - Real.exp (-1)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply measureReal_natTailEventUnion_le_exp (Q.law : Measure
    (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) _ _ hN
  intro m hm
  have hp := D.normalizedSourcePhaseCurveBadEvent_measure_le hF hw T hcut hm Q r K
  dsimp only at hp
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hcoef : 1 ≤ K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
      (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
      2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
        (D.normalizedSourcePhaseCell T cut 0 0 (r + 2))).toReal * (Real.exp 1 - 1) := by
    unfold normalizedSourcePhaseCurveCountThreshold at hK
    linarith
  have hmcoef := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) m)
  linarith

/-- A deterministic threshold uses the exact original target congruence-cell intensity. -/
def normalizedTargetPhaseCurveCountThreshold
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut r : ℝ) : ℝ :=
  (3 * (2 * finrank ℝ S.covector.ker : ℝ) + (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
    2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.normalizedTargetPhaseCell T cut 0 0 (r + 2))).toReal * (Real.exp 1 - 1) + 1

theorem normalizedTargetPhaseCurveCountThreshold_pos
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut r : ℝ) : 0 < D.normalizedTargetPhaseCurveCountThreshold T cut r := by
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr zero_le_one)
  unfold normalizedTargetPhaseCurveCountThreshold
  positivity

/-- This event depends on complete original input counts at all fixed scales ≥ N. -/
def normalizedTargetPhaseCurveAllScaleBadEvent
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (N : ℕ) (r K : ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :=
  natTailEventUnion (fun m ↦ D.normalizedTargetPhaseCurveBadEvent T cut m r K) N

theorem measurableSet_normalizedTargetPhaseCurveAllScaleBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (N : ℕ) (r K : ℝ) :
    MeasurableSet (D.normalizedTargetPhaseCurveAllScaleBadEvent T cut N r K) :=
  measurableSet_natTailEventUnion
    (fun m ↦ D.measurableSet_normalizedTargetPhaseCurveBadEvent hF hw T hcut m r K) N

/-- The actual original Poisson law gives a simultaneous exponential tail.
Its threshold is the true normalized cell intensity, without a frame loss. -/
theorem normalizedTargetPhaseCurveAllScaleBadEvent_measure_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (r : ℝ) {K : ℝ} (hK : D.normalizedTargetPhaseCurveCountThreshold T cut r ≤ K)
    {N : ℕ} (hN : 1 ≤ N) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
      (D.normalizedTargetPhaseCurveAllScaleBadEvent T cut N r K) ≤
      Real.exp (-(N : ℝ)) / (1 - Real.exp (-1)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply measureReal_natTailEventUnion_le_exp (Q.law : Measure
    (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) _ _ hN
  intro m hm
  have hp := D.normalizedTargetPhaseCurveBadEvent_measure_le hF hw T hcut hm Q r K
  dsimp only at hp
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hcoef : 1 ≤ K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
      (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
      2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
        (D.normalizedTargetPhaseCell T cut 0 0 (r + 2))).toReal * (Real.exp 1 - 1) := by
    unfold normalizedTargetPhaseCurveCountThreshold at hK
    linarith
  have hmcoef := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) m)
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
