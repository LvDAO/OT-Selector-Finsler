import OTSelector.Reconstruction.PositiveCompletePathContributors
import OTSelector.Reconstruction.FinslerOriginalPathMeasurability

/-! Nonzero original edge traffic produces a clock on its literal general Finsler path. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Positive literal original complete-path traffic produces a genuine marked-clock
contributor on that same path. No cyclic, rough-field or integral measurability premise is used. -/
theorem original_completePathEdgeTraffic_ne_zero_exists_clock
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞)
    (f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (he : legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≠ 0) :
    ∃ c : ℝ, η (originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 c) ≠ 0 ∧
      f ((physicalPairAnchor e).2, c) ≠ 0 := by
  simpa only [originalSeedCompletePath_eq_anchor_add_offset] using
    legalMarkedCompletePathEdgeTraffic_ne_zero_exists_clock
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e he

/-- Actual clock-mask support and a normalized physical kernel window turn nonzero
original traffic into a unit-clock point on the literal original complete path. -/
theorem original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞)
    (f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (c₀ ell : ℝ) (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (he : legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≠ 0)
    (hclock : ∀ m c, f (m, c) ≠ 0 → ∃ r ∈ Icc (0 : ℝ) 1, c = c₀ + ell * r)
    {a : ℝ} (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a) :
    ∃ r ∈ Icc (0 : ℝ) 1,
      η (originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (c₀ + ell * r)) ≠ 0 ∧
      f ((physicalPairAnchor e).2, c₀ + ell * r) ≠ 0 ∧
      ‖T *ᵥ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (c₀ + ell * r)‖ ≤ a := by
  simpa only [originalSeedCompletePath_eq_anchor_add_offset] using
    legalMarkedCompletePathEdgeTraffic_ne_zero_exists_affineWindow_contributor
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f T c₀ ell e he hclock hηwindow

end OTSelector.Reconstruction
