import OTSelector.Reconstruction.OriginalStageResidualNeumannReadout

/-! The concrete original mollifier closes the actual stage Neumann test identity. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual original stage identity uses the concrete smooth normalized radial kernel;
all kernel, integral and endpoint conditions are proved internally. The source and target
slabs remain respectively [s,t) and (s,t], on the same original axisaligned cube and scene. -/
theorem ae_all_originalCanonicalStageResidualDensity_Neumann_readout
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) {s t : ℝ} (hst : s ≤ t) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Integrable (fun z ↦ originalOmittedSmoothedSlabDerivative S w R ell s t η z scene)
        (volume.restrict (haarRootCube _ R)) ∧
      ∀ A : OriginalStageResidualDensityData S w R ell η, A.scene = scene →
      ∀ (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
        (φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ)),
        (∫ z in haarRootCube _ R, φ z) = 0 →
      (∫ z in haarRootCube _ R, (A.sourceDensity s t z - A.targetDensity s t z) * φ z) =
        (∫ z in haarRootCube _ R,
          originalOmittedSmoothedSlabDerivative S w R ell s t η z scene * φ z) +
        (∫ z in haarRootCube _ R, originalClassReflectedInputScalarField η R (Ico s t)
          (legalInputColorMeasure _ scene.2 0) z * φ z) -
        (∫ z in haarRootCube _ R, originalClassReflectedInputScalarField η R (Ioc s t)
          (legalInputColorMeasure _ scene.2 1) z * φ z) := by
  exact D.ae_all_originalStageResidualDensity_Neumann_readout hF hw Q hell hR
    ((contDiff_originalEuclideanMollifier _).of_le (by norm_num))
    (hasCompactSupport_originalEuclideanMollifier _) (integrable_originalEuclideanMollifier _)
    (integral_originalEuclideanMollifier_eq_one _)
    (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range _))
    (coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial _))
    (originalEuclideanMollifierBound_nonneg _) (abs_originalEuclideanMollifier_le _) hst

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
