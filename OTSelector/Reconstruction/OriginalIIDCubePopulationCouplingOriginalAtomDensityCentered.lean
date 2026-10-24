import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOriginalAtomDensity
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingCubeVolume

/-! The unchanged raw reserve atom laws sum to the literal constant n/V
density on the actual centered cube, read in true Euclidean coordinates. -/

open MeasureTheory Set
open OTSelector.Probability
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The true centered physical population target is the literal n/V density
with respect to actual restricted cube volume, including n=0 and q=0. -/
theorem originalRawCubePopulationTarget_eq_centered_density (q n : ℕ)
    {R : ℝ} (hR : 0 < R) :
    (n : ℝ≥0∞) • (cubeMeasure (Fin q) 1).map
      (originalRawCubePhysicalMap
        ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2 * R)) =
      ((volume.restrict (haarRootCube (Fin q) R)).withDensity
        (fun _ ↦ ENNReal.ofReal ((n : ℝ) / volume.real (haarRootCube (Fin q) R)))).map
          (EuclideanSpace.equiv (Fin q) ℝ).symm := by
  let e := (EuclideanSpace.equiv (Fin q) ℝ).symm
  let A : (Fin q → ℝ) → (Fin q → ℝ) := fun v i ↦ 2 * R * v i - R
  have he : Measurable e := e.continuous.measurable
  have hA : Measurable A := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_const_mul (2 * R)).comp (measurable_pi_apply i)).sub measurable_const
  have hF : originalRawCubePhysicalMap (e (fun _ ↦ -R)) (2 * R) = e ∘ A := by
    funext v
    ext i
    change -R + (2 * R) * v i = 2 * R * v i - R
    ring
  have hVfin : volume (haarRootCube (Fin q) R) ≠ ∞ := by
    rw [volume_haarRootCube (Fin q) hR.le]
    exact ENNReal.ofReal_ne_top
  have hVpos : volume (haarRootCube (Fin q) R) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hR.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) _)).ne'
  have hVrpos : 0 < volume.real (haarRootCube (Fin q) R) :=
    ENNReal.toReal_pos hVpos hVfin
  have hcoef : ENNReal.ofReal ((n : ℝ) / volume.real (haarRootCube (Fin q) R)) =
      (n : ℝ≥0∞) * (volume (haarRootCube (Fin q) R))⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hVrpos, ENNReal.ofReal_natCast,
      show ENNReal.ofReal (volume.real (haarRootCube (Fin q) R)) =
        volume (haarRootCube (Fin q) R) from ENNReal.ofReal_toReal hVfin]
    rfl
  change (n : ℝ≥0∞) • (cubeMeasure (Fin q) 1).map
    (originalRawCubePhysicalMap (e (fun _ ↦ -R)) (2 * R)) = _
  rw [hF, ← Measure.map_map he hA,
    map_originalUnitCube_centered_eq_normalized_volume q hR, Measure.map_smul,
    withDensity_const, Measure.map_smul, hcoef, smul_smul]

/-- The actual probability laws attached to unchanged centered raw reserve
atoms sum exactly to the required physical n/V density measure. -/
theorem originalRawCubeAtomPopulationLaw_sum_centered_density {q n : ℕ}
    {R : ℝ} (hR : 0 < R) (x : Fin n → (Fin q → ℝ))
    (hx : ∀ i, x i ∈ unitCube q) :
    (∑ i, originalRawCubeAtomPopulationLaw
      ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2 * R) x i) =
      ((volume.restrict (haarRootCube (Fin q) R)).withDensity
        (fun _ ↦ ENNReal.ofReal ((n : ℝ) / volume.real (haarRootCube (Fin q) R)))).map
          (EuclideanSpace.equiv (Fin q) ℝ).symm :=
  (originalRawCubeAtomPopulationLaw_spec _ _ x hx).2.1.trans
    (originalRawCubePopulationTarget_eq_centered_density q n hR)

end OTSelector.Reconstruction
