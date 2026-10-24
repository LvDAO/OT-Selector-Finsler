import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedRetentionGeometry
import OTSelector.Reconstruction.OriginalStageResidualDensityCutIntegrability
import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts

/-! The actual same-frame omitted cut and its unchanged physical canonical smoothing. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A compact physical window is contained in some nonnegative raw coordinate cube.
This only bounds an integration domain, without rotating the original scene or kernel. -/
theorem originalStagePhysicalCube_subset_rawCube {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    ∃ T ≥ 0, originalCenteredPhysicalCubeRegion b (2 * R) ⊆ haarRootCube (Fin q) T := by
  obtain ⟨T, hT⟩ := (isCompact_originalStagePhysicalCube b (2 * R)).isBounded.exists_norm_le
  refine ⟨max T 0, le_max_right _ _, fun z hz ↦ ?_⟩
  exact (mem_haarRootCube_iff_norm_le (le_max_right _ _) z).mpr ((hT z hz).trans (le_max_left _ _))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The true positive cut occupation of exactly the omitted original paths for this same
chosen physical orientation and unchanged genuine path-length cutoff. -/
def originalOrientedOmittedSceneActiveCutMeasure (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell c : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalRestrictedSceneActiveCutMeasure S w (originalOrientedPathLengthRetained S w b R ell)ᶜ c scene

/-- Literal physical smoothing of the actual omitted original cut, with the same fixed
canonical Euclidean mollifier used by the reflected ports and full input boundary term. -/
def originalOrientedOmittedCutDensity (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell c : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  ∫ x, originalEuclideanMollifier (finrank ℝ S.covector.ker) (x - z)
    ∂originalOrientedOmittedSceneActiveCutMeasure S w b R ell c scene

omit [BorelSpace E] in
theorem originalOrientedOmittedCutDensity_nonneg (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell c : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    0 ≤ originalOrientedOmittedCutDensity S w b R ell c scene z :=
  integral_nonneg (fun x ↦ originalEuclideanMollifier_nonneg _ (x - z))

/-- Actual Campbell local finiteness internally gives spatial L1 on the same physical
cube, for this actual omitted set, with no conditional law of selected cuts. -/
theorem ae_originalOrientedOmittedCutDensity_integrable (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell c : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Integrable (originalOrientedOmittedCutDensity S w b R ell c scene)
        (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) := by
  obtain ⟨T, hT, hsub⟩ := originalStagePhysicalCube_subset_rawCube b R
  filter_upwards [ae_originalRestrictedSceneSlabCharges_finiteOnCompacts S hF hw Q
    (originalOrientedPathLengthRetained S w b R ell)ᶜ c c] with scene hs
  let : IsFiniteMeasureOnCompacts (originalOrientedOmittedSceneActiveCutMeasure S w b R ell c scene) := hs.2.2.1
  exact (integrable_cube_compactKernel_smoothing _
    (contDiff_originalEuclideanMollifier _).continuous.measurable (abs_originalEuclideanMollifier_le _)
    (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range _)) hT).mono_measure
      (Measure.restrict_mono_set volume hsub)

end OTSelector.Reconstruction
