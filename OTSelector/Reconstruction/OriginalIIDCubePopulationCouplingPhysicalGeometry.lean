import OTSelector.Reconstruction.DyadicCubePartition
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The literal affine physical cube and its coordinate-to-Euclidean cost bound. -/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The actual standard-frame cube of origin z and scalar side length L. -/
def originalIIDCubePhysicalMap {q : ℕ} (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (u : DyadicUnitCube q) : EuclideanSpace ℝ (Fin q) :=
  z + L • (EuclideanSpace.equiv (Fin q) ℝ).symm (dyadicCubePoint u)

/-- The original coordinate cube maps measurably to its physical affine image. -/
theorem measurable_originalIIDCubePhysicalMap {q : ℕ}
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (originalIIDCubePhysicalMap z L) := by
  have hm : Measurable (dyadicCubePoint (q := q)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  exact measurable_const.add
    (((EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.comp hm).const_smul L)

/-- Genuine Euclidean squared distances are bounded by q times the original
coordinate squared distance, with the actual affine scale, including L=0. -/
theorem originalIIDCubePhysicalMap_squareCost_le {q : ℕ}
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (u v : DyadicUnitCube q) :
    ‖originalIIDCubePhysicalMap z L u - originalIIDCubePhysicalMap z L v‖ ^ 2 ≤
      (q : ℝ) * L ^ 2 * ‖dyadicCubePoint u - dyadicCubePoint v‖ ^ 2 := by
  rw [originalIIDCubePhysicalMap, originalIIDCubePhysicalMap, add_sub_add_left_eq_sub,
    ← smul_sub,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, EuclideanSpace.norm_sq_eq]
  calc
    L ^ 2 * ∑ i, ‖((EuclideanSpace.equiv (Fin q) ℝ).symm (dyadicCubePoint u) -
        (EuclideanSpace.equiv (Fin q) ℝ).symm (dyadicCubePoint v)) i‖ ^ 2 ≤
        L ^ 2 * ∑ _i : Fin q, ‖dyadicCubePoint u - dyadicCubePoint v‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_le_pi_norm (dyadicCubePoint u - dyadicCubePoint v) i) 2
    _ = (q : ℝ) * L ^ 2 * ‖dyadicCubePoint u - dyadicCubePoint v‖ ^ 2 := by simp; ring

end OTSelector.Reconstruction
