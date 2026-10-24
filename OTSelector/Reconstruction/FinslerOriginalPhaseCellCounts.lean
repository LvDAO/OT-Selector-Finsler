import OTSelector.Reconstruction.FinslerOriginalPhaseSourceCells
import OTSelector.Reconstruction.OriginalStationaryFiniteIntensityCounts

/-!
# Actual original-input exponential bounds on Finsler phase source cells

The set, its measurability and finite intensity are produced from the actual
original Finsler compliance. The count is always the complete unchanged original
Poisson input, before any adaptive transport edge or candidate is chosen.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- The full original source count of every actual fixed phase cell is finite and has the
original Poisson exponential bound, including cells with unbounded spatial extent. -/
theorem original_source_phaseCell_exp_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {L : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hL : IsUnit L.det) {c : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    (hc : Measurable c) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    let B := markedPhaseSourceCell L (D.sourcePhaseLeg cut) c (D.sourcePhaseClocks cut) R
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (B ×ˢ {0}) < (∞ : ℝ≥0∞)) ∧
      Integrable (fun s ↦ Real.exp (t *
        ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
          (B ×ˢ {0})).toReal))
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, Real.exp (t * ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (B ×ˢ {0})).toReal)
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
          Real.exp ((((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            B).toReal * (Real.exp t - 1)) := by
  exact Q.original_source_exp_moment_of_finite_intensity
    (measurableSet_markedPhaseSourceCell _ (D.measurable_sourcePhaseLeg hF hw hcut) hc
      (D.measurableSet_sourcePhaseClocks cut) R)
    (D.sourcePhaseCell_intensity_lt_top hF hw hcut hL hc R).ne ht

omit [BorelSpace E] in
/-- The full original target count of every actual fixed phase cell is finite and has the
original Poisson exponential bound, including cells with unbounded spatial extent. -/
theorem original_target_phaseCell_exp_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {L : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hL : IsUnit L.det) {c : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    (hc : Measurable c) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    let B := markedPhaseSourceCell L (D.targetPhaseLeg cut) c (D.targetPhaseClocks cut) R
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (B ×ˢ {1}) < (∞ : ℝ≥0∞)) ∧
      Integrable (fun s ↦ Real.exp (t *
        ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
          (B ×ˢ {1})).toReal))
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, Real.exp (t * ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (B ×ˢ {1})).toReal)
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
          Real.exp ((((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
            B).toReal * (Real.exp t - 1)) := by
  exact Q.original_target_exp_moment_of_finite_intensity
    (measurableSet_markedPhaseSourceCell _ (D.measurable_targetPhaseLeg hF hw hcut) hc
      (D.measurableSet_targetPhaseClocks cut) R)
    (D.targetPhaseCell_intensity_lt_top hF hw hcut hL hc R).ne ht

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
