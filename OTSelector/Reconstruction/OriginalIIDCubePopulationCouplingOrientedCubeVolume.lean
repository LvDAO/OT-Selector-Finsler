import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingCubeVolume
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume
import OTSelector.Probability.FiniteMeasureConditioning

/-! The original unit-cube sampler has the exact law on the same chosen physical frame. -/

open Set Function MeasureTheory
open OTSelector.Probability
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
variable {q : ℕ}

/-- Original raw unit-cube positions, affinely centered and rotated into the
same chosen physical side-2R cube. The parameter R is the half-side length. -/
def originalOrientedRawCubePhysicalMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (v : Fin q → ℝ) : Fin q → ℝ :=
  orthonormalPhysicalCubeMap b (fun i ↦ 2*R*v i-R)

theorem measurable_originalOrientedRawCubePhysicalMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    Measurable (originalOrientedRawCubePhysicalMap b R) :=
  (orthonormalPhysicalCubeMap b).continuous.measurable.comp
    (measurable_pi_lambda _ fun i ↦ ((measurable_const_mul (2*R)).comp (measurable_pi_apply i)).sub measurable_const)

/-- The existing actual orthogonal map transports the restricted axis volume
to the literal project physical cube, including zero-dimensional space. -/
theorem map_haarRootCube_volume_orthonormalPhysicalCubeMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    ((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) R)).map
      (orthonormalPhysicalCubeMap b) = volume.restrict (originalCenteredPhysicalCubeRegion b (2*R)) := by
  have hpre : (orthonormalPhysicalCubeMap b) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R) =
      haarRootCube (Fin q) R := by
    rw [originalOrientedTraffic_cube_eq_preimage]
    ext v
    change (orthonormalPhysicalCubeMap b).symm (orthonormalPhysicalCubeMap b v) ∈
      haarRootCube (Fin q) R ↔ v ∈ haarRootCube (Fin q) R
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [← hpre, ← Measure.restrict_map (orthonormalPhysicalCubeMap b).continuous.measurable
    (measurableSet_originalOrientedTraffic_cube b R), (measurePreserving_orthonormalPhysicalCubeMap b).map_eq]

/-- The affine unit sampler is exactly normalized restricted volume on the
same physical cube, with no additional dimension or orientation factor. -/
theorem map_originalUnitCube_oriented_eq_normalized_volume
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R) :
    (cubeMeasure (Fin q) 1).map (originalOrientedRawCubePhysicalMap b R) =
      (volume (originalCenteredPhysicalCubeRegion b (2*R)))⁻¹ •
        volume.restrict (originalCenteredPhysicalCubeRegion b (2*R)) := by
  have hA : Measurable (fun v : Fin q → ℝ ↦ fun i ↦ 2*R*v i-R) :=
    measurable_pi_lambda _ fun i ↦ ((measurable_const_mul (2*R)).comp (measurable_pi_apply i)).sub measurable_const
  change (cubeMeasure (Fin q) 1).map ((orthonormalPhysicalCubeMap b) ∘ (fun v i ↦ 2*R*v i-R)) = _
  rw [← Measure.map_map (orthonormalPhysicalCubeMap b).continuous.measurable hA,
    map_originalUnitCube_centered_eq_normalized_volume q hR, Measure.map_smul,
    map_haarRootCube_volume_orthonormalPhysicalCubeMap b R, volume_originalOrientedTraffic_cube b R]

/-- Exact input law for the physical reserve producer using the project's
actual normalized finite-law API and the same closed physical cube. -/
theorem map_originalUnitCube_oriented_eq_normalizedFiniteLaw
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R) :
    (cubeMeasure (Fin q) 1).map (originalOrientedRawCubePhysicalMap b R) =
      normalizedFiniteLaw (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) := by
  rw [normalizedFiniteLaw_restrict_eq_cond volume _ (by
    rw [volume_originalOrientedTraffic_cube b R, volume_haarRootCube (Fin q) hR.le]
    exact ENNReal.ofReal_ne_top)]
  exact map_originalUnitCube_oriented_eq_normalized_volume b hR

end OTSelector.Reconstruction
