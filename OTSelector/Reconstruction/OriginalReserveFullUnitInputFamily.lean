import OTSelector.Reconstruction.OriginalReserveFullUnitInputExperiment

/-! A family of genuine original unit-input experiments is constructed for every positive physical cube radius. -/
open Set Function MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal NNReal Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- Construct the actual full experiment at every positive radius from the
same original matching/reserve pair, theta and physical frame. Every value
retains the proved original pair, iid sampler, unit-input and full-array laws. -/
def originalReserve_fullUnitInputExperimentFamily
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Main Reserve : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  exact fun R hR ↦ Classical.choice
    (D.exists_originalReserve_fullUnitInputExperiment Main Reserve b hq hθ hθ1 (R := R) hR)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
