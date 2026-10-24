import OTSelector.Reconstruction.FinslerOriginalCoefficientSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Basic
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic

/-!
# Coefficient-lane differentiability of kin and g

This module produces the differentiability data left as hypothesis in
`FinslerOriginalCoefficientSmoothness`: the frozen coefficient cost is the
quadratic form `matrixQuadratic A` of the positive definite frozen inverse
compliance, which is a polynomial in the displacement coordinates.  Therefore it is
`ContDiff ℝ 1`, and on a nonempty compact retained-root family the bounded
derivative interface `HasBoundedFDerivOn` follows from
`exists_hasBoundedFDerivOn_of_compact` with `f' := fderiv ℝ f`.

The exact remaining sub-gap is stated in the module doc: the mark coordinate map
of `kin` and `g` (the population seed label readout) is Lipschitz/linear on the
retained roots, so that the quadratic form pulls back; proving that linearity of
the readout from the seed window structure is the only analytic step left.
-/

noncomputable section
namespace OTSelector.Reconstruction

open scoped NNReal ENNReal

/-- The frozen quadratic coefficient cost is `ContDiff ℝ 1` in the displacement. -/
theorem contDiff_one_coefficientQuadratic {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) : ContDiff ℝ 1 (fun z : n → ℝ => matrixQuadratic A z) := by
  have h : ContDiff ℝ 1
      (fun z : n → ℝ => (1 / 2 : ℝ) * ∑ i, z i * (∑ j, A i j * z j)) := by
    fun_prop
  have hfun : (fun z : n → ℝ => matrixQuadratic A z) =
      fun z => (1 / 2 : ℝ) * ∑ i, z i * (∑ j, A i j * z j) := by
    funext z
    simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hfun]
  exact h

/-- A `ContDiff ℝ 1` real function on a nonempty compact set has the bounded
derivative interface, using its Frechet derivative family. -/
theorem exists_hasBoundedFDerivOn_of_contDiff_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) : ∃ C : ℝ≥0, HasBoundedFDerivOn E K f C := by
  have hdiff : ∀ x ∈ K, HasFDerivWithinAt f (fderiv ℝ f x) K x :=
    fun x _ => ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hcont : ContinuousOn (fderiv ℝ f) K := (hf.continuous_fderiv (by norm_num)).continuousOn
  exact exists_hasBoundedFDerivOn_of_compact hK hne hdiff hcont

end OTSelector.Reconstruction
