import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedRetentionGeometry

/-! The same canonical physical mollifier and reflection kernel in the chosen cube frame. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual canonical reflected kernel in the chosen physical cube of side 2R. -/
def originalCanonicalOrientedReflectedKernel {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (z x : Fin q → ℝ) : ℝ :=
  originalCubeReflectedKernel (originalEuclideanMollifier q) R
    ((orthonormalPhysicalCubeMap b).symm z) ((orthonormalPhysicalCubeMap b).symm x)

/-- Canonical Euclidean radiality preserves the same physical mollifier under inverse frame readout. -/
theorem originalEuclideanMollifier_inverse_frame {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (v : Fin q → ℝ) :
    originalEuclideanMollifier q ((orthonormalPhysicalCubeMap b).symm v) = originalEuclideanMollifier q v := by
  have h := congrFun (euclideanRadial_comp_orthonormalPhysicalCubeMap b (originalEuclideanMollifier_radial q))
    ((orthonormalPhysicalCubeMap b).symm v)
  simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using h.symm

/-- This is a genuine nonnegative reflection kernel. -/
theorem originalCanonicalOrientedReflectedKernel_nonneg {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (z x : Fin q → ℝ) :
    0 ≤ originalCanonicalOrientedReflectedKernel b R z x :=
  originalCubeReflectedKernel_nonneg (originalEuclideanMollifier_nonneg q) _ _ _

set_option backward.isDefEq.respectTransparency true in
/-- Both actual physical kernel arguments are jointly measurable. -/
theorem measurable_originalCanonicalOrientedReflectedKernel {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦
      originalCanonicalOrientedReflectedKernel b R p.1 p.2) := by
  have hη : Measurable (originalEuclideanMollifier q) :=
    (contDiff_originalEuclideanMollifier q).continuous.measurable
  have hO : Measurable (fun x : Fin q → ℝ ↦ (orthonormalPhysicalCubeMap b).symm x) :=
    (orthonormalPhysicalCubeMap b).symm.continuous.measurable
  have hraw : Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦
      originalCubeReflectedKernel (originalEuclideanMollifier q) R p.1 p.2) :=
    measurable_originalCubeReflectedKernel hη R
  simpa only [Function.comp_def, Function.uncurry, originalCanonicalOrientedReflectedKernel]
    using hraw.comp ((hO.comp measurable_fst).prodMk (hO.comp measurable_snd))


/-- Every actual port inside this same oriented physical cube has genuine unit smoothing mass. -/
theorem integral_originalCanonicalOrientedReflectedKernel_eq_one {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    {x : Fin q → ℝ} (hx : x ∈ originalCenteredPhysicalCubeRegion b (2 * R)) :
    (∫ z in originalCenteredPhysicalCubeRegion b (2 * R),
      originalCanonicalOrientedReflectedKernel b R z x) = 1 := by
  have hhalf : 2 * R / 2 = R := by ring
  have hneg : -(2 * R) / 2 = -R := by ring
  have hx' : (orthonormalPhysicalCubeMap b).symm x ∈ haarRootCube (Fin q) R := by
    simpa only [hhalf] using (mem_originalCenteredPhysicalCubeRegion_iff b (2 * R) x).mp hx
  have hraw := integral_originalCubeReflectedKernel_eq_one
    (integrable_originalEuclideanMollifier q) (integral_originalEuclideanMollifier_eq_one q)
    (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q))
    (coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q)) hR hx'
  unfold originalCenteredPhysicalCubeRegion
  rw [integral_orthonormalPhysicalCubeRegion]
  simpa only [originalCanonicalOrientedReflectedKernel, ContinuousLinearEquiv.symm_apply_apply,
    hhalf, hneg, haarRootCube] using hraw

/-- On actual deep inputs the oriented reflection is precisely the unchanged physical raw
mollifier, not merely a kernel with matching total mass. -/
theorem originalCanonicalOrientedReflectedKernel_eq_raw_of_inner {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} {z x : Fin q → ℝ}
    (hz : z ∈ originalCenteredPhysicalCubeRegion b (2 * R))
    (hx : x ∈ originalCenteredPhysicalCubeRegion b (2 * (R - 1))) :
    originalCanonicalOrientedReflectedKernel b R z x = originalEuclideanMollifier q (z - x) := by
  have hhalf (a : ℝ) : 2 * a / 2 = a := by ring
  have hz' : (orthonormalPhysicalCubeMap b).symm z ∈ haarRootCube (Fin q) R := by
    simpa only [hhalf] using (mem_originalCenteredPhysicalCubeRegion_iff b (2 * R) z).mp hz
  have hx' : (orthonormalPhysicalCubeMap b).symm x ∈ haarRootCube (Fin q) (R - 1) := by
    simpa only [hhalf] using (mem_originalCenteredPhysicalCubeRegion_iff b (2 * (R - 1)) x).mp hx
  rw [originalCanonicalOrientedReflectedKernel, originalCubeReflectedKernel_eq_kernel_of_inner
    (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)) hz' hx',
    ← map_sub, originalEuclideanMollifier_inverse_frame]

end OTSelector.Reconstruction
