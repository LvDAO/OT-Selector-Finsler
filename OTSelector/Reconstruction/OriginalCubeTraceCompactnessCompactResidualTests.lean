import OTSelector.Reconstruction.OriginalCubeTraceCompactnessSlabResidualMeasures
import OTSelector.Analysis.Sobolev.MeasureWeakNeumannFlux

/-! Actual finite original residual measures on the original compact smooth-test domain. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Restriction to the actual compact test support leaves every original smooth-test integral
unchanged, for an arbitrary original measure. -/
theorem integral_restrict_original_compact_test {q : ℕ}
    (K : Compacts (Fin q → ℝ)) (ν : Measure (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    (∫ x, φ x ∂ν.restrict K) = ∫ x, φ x ∂ν := by
  rw [← integral_indicator K.isCompact.measurableSet, indicator_eq_self.2 φ.support_subset]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual source-plus-incoming-cut measure restricted to the original compact test set. -/
def originalSceneCompactSlabResidualSource (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (s t : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  (originalSceneSlabResidualSource S w s t scene).restrict K

/-- The actual target-plus-outgoing-cut measure restricted to the original compact test set. -/
def originalSceneCompactSlabResidualTarget (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (s t : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  (originalSceneSlabResidualTarget S w s t scene).restrict K

/-- Actual compact original residual measures are finite by the genuine Campbell-derived
local finiteness of their source, target and cut measures. -/
theorem ae_originalSceneCompactSlabResidualMeasures_finite
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasure (originalSceneCompactSlabResidualSource S w K s t scene) ∧
      IsFiniteMeasure (originalSceneCompactSlabResidualTarget S w K s t scene) := by
  filter_upwards [ae_originalSceneSlabResidualMeasures_finiteOnCompacts S hF hw Q s t]
    with scene hfinite
  exact ⟨isFiniteMeasure_restrict.mpr (hfinite.1.lt_top_of_isCompact K.isCompact).ne,
    isFiniteMeasure_restrict.mpr (hfinite.2.lt_top_of_isCompact K.isCompact).ne⟩

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual finite positive residual measures have precisely the original smooth-test
measure discrepancy used by the weak Neumann consumer. The same infinite-scene path slab
produces that discrepancy, on one full-measure set for all original compact smooth tests. -/
theorem ae_all_originalCompactSlabResidual_testDiscrepancy_eq_weakSlab
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasure (originalSceneCompactSlabResidualSource S w K s t scene) ∧
      IsFiniteMeasure (originalSceneCompactSlabResidualTarget S w K s t scene) ∧
      ∀ φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ),
        (∫ x, φ x ∂originalSceneCompactSlabResidualSource S w K s t scene) -
          (∫ x, φ x ∂originalSceneCompactSlabResidualTarget S w K s t scene) =
            -originalSeedPathWeakSlabReadout S w φ s t scene := by
  filter_upwards [ae_originalSceneCompactSlabResidualMeasures_finite S hF hw Q K s t,
    D.ae_all_originalWeakSlab_residualMeasure_balance hF hw Q hst]
    with scene hfinite hbalance
  refine ⟨hfinite.1, hfinite.2, fun φ ↦ ?_⟩
  rw [originalSceneCompactSlabResidualSource, originalSceneCompactSlabResidualTarget,
    integral_restrict_original_compact_test, integral_restrict_original_compact_test]
  exact (hbalance φ (φ.contDiff.of_le (by norm_num)) φ.compact_supp).symm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
