import OTSelector.Reconstruction.OriginalStageResidualDensityGoodCutFloor
import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice

/-! A fixed genuine Euclidean mollifier and one event valid for all surviving Fin indices. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
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

/-- With the canonical actual mollifier, a single full-scene event supplies true equal
mass, exact full-cut cancellation and the actual good-cut density floor simultaneously
for every surviving subset of the unchanged original reserve indices. -/
theorem ae_all_originalCanonicalStageDensities
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R)
    (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalStageResidualDensityData S w R ell
          (originalEuclideanMollifier (finrank ℝ S.covector.ker)) :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      Integrable (A.sourceDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      Integrable (A.targetDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      (∫ z in haarRootCube _ R, A.sourceDensity s t z) =
        (∫ z in haarRootCube _ R, A.targetDensity s t z) ∧
      A.gamma s = (A.reservePrefix s + originalStageFullCutError S w R s
        (originalEuclideanMollifier _) scene) / A.cubeVolume ∧
      A.gamma t = (A.reservePrefix t + originalStageFullCutError S w R t
        (originalEuclideanMollifier _) scene) / A.cubeVolume ∧
      ∀ r : ℝ, A.goodCut r s → A.goodCut r t → ∀ z,
        3 * r ≤ A.sourceDensity s t z ∧ 3 * r ≤ A.targetDensity s t z := by
  let q := finrank ℝ S.covector.ker
  have hη := (contDiff_originalEuclideanMollifier q).continuous
  have hηI := integrable_originalEuclideanMollifier q
  have hηone := integral_originalEuclideanMollifier_eq_one q
  have hcη := hasCompactSupport_originalEuclideanMollifier q
  have hsupport := raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)
  have heven := coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q)
  have hηM := abs_originalEuclideanMollifier_le q
  have hmass : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier q) :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      Integrable (A.sourceDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      Integrable (A.targetDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      (∫ z in haarRootCube _ R, A.sourceDensity s t z) =
        ∫ z in haarRootCube _ R, A.targetDensity s t z := by
    apply ae_all_iff.mpr
    intro sourceKept
    apply ae_all_iff.mpr
    intro targetKept
    exact D.ae_originalStageResidualDensities_integrable_equal_mass hF hw Q
      (by linarith) hR (by linarith) hη.measurable hηI hηone hsupport heven hηM
      sourceReserve targetReserve sourceKept targetKept hst
  filter_upwards [hmass,
    D.ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError hF hw Q hell hR s
      hη hcη hηI hηone hsupport heven hηM,
    D.ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError hF hw Q hell hR t
      hη hcη hηI hηone hsupport heven hηM,
    D.ae_all_originalStageDensities_floor_on_goodCuts hF hw Q hell hR s t
      hη hcη hηI (originalEuclideanMollifier_nonneg q) hηone hsupport heven hηM]
    with scene hmass hgs hgt hfloor
  intro sourceKept targetKept
  dsimp only
  exact ⟨(hmass sourceKept targetKept).1, (hmass sourceKept targetKept).2.1,
    (hmass sourceKept targetKept).2.2, hgs sourceReserve targetReserve sourceKept targetKept,
    hgt sourceReserve targetReserve sourceKept targetKept,
    hfloor sourceReserve targetReserve sourceKept targetKept⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
