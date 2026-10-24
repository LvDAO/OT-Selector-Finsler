import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedRetentionGeometry
import OTSelector.Reconstruction.NormalizedShellBulkEnergy

/-! Genuine same-frame physical cube and collar volume, with no change of original law. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
variable {q : ℕ}

/-- The physical side-2R cube is exactly the inverse-frame preimage of the raw radius-R cube. -/
theorem originalOrientedTraffic_cube_eq_preimage
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    originalCenteredPhysicalCubeRegion b (2 * R) =
      (orthonormalPhysicalCubeMap b).symm ⁻¹' haarRootCube (Fin q) R := by
  ext z
  rw [mem_originalCenteredPhysicalCubeRegion_iff, show 2 * R / 2 = R by ring]
  rfl

/-- The actual oriented physical cube is Borel for every radius. -/
theorem measurableSet_originalOrientedTraffic_cube
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    MeasurableSet (originalCenteredPhysicalCubeRegion b (2 * R)) := by
  rw [originalOrientedTraffic_cube_eq_preimage]
  exact measurableSet_Icc.preimage (orthonormalPhysicalCubeMap b).symm.continuous.measurable

/-- The chosen genuine orthogonal physical cube has exactly its own original Haar volume. -/
theorem volume_originalOrientedTraffic_cube
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    volume (originalCenteredPhysicalCubeRegion b (2 * R)) = volume (haarRootCube (Fin q) R) := by
  rw [originalOrientedTraffic_cube_eq_preimage]
  exact (measurePreserving_orthonormalPhysicalCubeMap_symm b).measure_preimage
    measurableSet_Icc.nullMeasurableSet

/-- The collar of the same physical orientation has exactly its genuine raw collar volume. -/
theorem volume_originalOrientedTraffic_collar
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R delta : ℝ) :
    volume (originalCenteredPhysicalCubeRegion b (2 * R) \
      originalCenteredPhysicalCubeRegion b (2 * (R-delta))) =
    volume (haarRootCube (Fin q) R \ haarRootCube (Fin q) (R-delta)) := by
  rw [originalOrientedTraffic_cube_eq_preimage, originalOrientedTraffic_cube_eq_preimage,
    ← preimage_sdiff]
  exact (measurePreserving_orthonormalPhysicalCubeMap_symm b).measure_preimage
    (measurableSet_Icc.diff measurableSet_Icc).nullMeasurableSet

/-- A sublinear collar has vanishing relative volume in the same physical orientation. -/
theorem tendsto_originalOrientedTraffic_collar_ratio
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {delta : ℝ → ℝ} (hdelta : ∀ᶠ R in atTop, 0 ≤ delta R)
    (hsmall : Tendsto (fun R ↦ delta R / R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦
      volume.real (originalCenteredPhysicalCubeRegion b (2 * R) \
        originalCenteredPhysicalCubeRegion b (2 * (R-delta R))) /
      volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) atTop (𝓝 0) := by
  simp only [measureReal_def, volume_originalOrientedTraffic_cube,
    volume_originalOrientedTraffic_collar]
  simpa only [measureReal_def, one_mul] using tendsto_haarRootCube_innerCollar_ratio (Fin q) hdelta
    (k := 1) zero_le_one hsmall

end OTSelector.Reconstruction
