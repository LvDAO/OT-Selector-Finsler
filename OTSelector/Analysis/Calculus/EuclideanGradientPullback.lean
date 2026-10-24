import Mathlib.Analysis.Calculus.Gradient.Basic
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PhysicalGradientPullback.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PhysicalGradientPullback`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual gradient for a scalar function in Euclidean coordinates and the specified coordinate equivalence.

Objects: The unchanged physical-coordinate gradient after pullback.

Proof detail: Apply the actual derivative chain rule and identify the Euclidean gradient by its inner-product pairing.

Sources: Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Terence Tao, Section 1.4, Theorem 1.4.13, p. 53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62).
Relation: Coordinate adapter for actual gradients; it changes representation, not the point or law.
-/

/-!
# Euclidean gradient tests in the unchanged physical coordinates

The coordinate change here only identifies finite real vectors with their
Euclidean norm. It does not replace the original physical point or measure.
-/
open InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pulling a genuine Euclidean test back to the original physical coordinates
recovers exactly the same coordinate gradient vector. -/
theorem physicalCoordinateGradient_pullback
    (F : EuclideanSpace ℝ ι → ℝ) (p : EuclideanSpace ℝ ι) (x : ι → ℝ)
    (hF : HasGradientAt F p ((EuclideanSpace.equiv ι ℝ).symm x)) :
    physicalCoordinateGradient ι
      (fderiv ℝ (fun z ↦ F ((EuclideanSpace.equiv ι ℝ).symm z)) x) = p := by
  have hd := hF.hasFDerivAt.comp x (EuclideanSpace.equiv ι ℝ).symm.hasFDerivAt
  change physicalCoordinateGradient ι
    (fderiv ℝ (F ∘ (EuclideanSpace.equiv ι ℝ).symm) x) = p
  rw [hd.fderiv]
  ext i
  rw [physicalCoordinateGradient_apply, ContinuousLinearMap.comp_apply, toDual_apply_apply]
  have hsingle : (EuclideanSpace.equiv ι ℝ).symm (Pi.single i (1 : ℝ)) =
      EuclideanSpace.single i 1 := rfl
  change inner ℝ p ((EuclideanSpace.equiv ι ℝ).symm (Pi.single i (1 : ℝ))) = p i
  rw [hsingle, EuclideanSpace.inner_single_right]
  simp

end OTSelector.Reconstruction

end
end
