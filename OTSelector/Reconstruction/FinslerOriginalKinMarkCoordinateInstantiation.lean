import OTSelector.Reconstruction.FinslerOriginalKinDifferentiability
import OTSelector.Reconstruction.FinslerOriginalCoefficientSmoothness

/-!
# Mark-coordinate instantiation of kin and g

This module performs the mark-coordinate instantiation left in
`FinslerOriginalKinDifferentiability`: `kin` and `g` are the frozen quadratic
coefficient cost (or a coefficient quadratic form) composed with the population
seed label readout, which on the retained roots is a continuous linear coordinate
map.  Composition of the C1 quadratic form with a continuous linear map is C1, and
the compact extraction then yields `HasBoundedFDerivOn` for both functions, hence
`HasMarkLipschitzConstantsOn` unconditionally on a convex nonempty compact root
family.

Nothing analytic is assumed beyond the linear readout and the coefficient matrix:
the readout being `E →L[ℝ] (n → ℝ)` is exactly the linearity of the seed label
coordinate map.
-/

noncomputable section
namespace OTSelector.Reconstruction

open scoped NNReal ENNReal

/-- The frozen quadratic form composed with a continuous linear readout is C1. -/
theorem contDiff_one_coefficientQuadratic_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (L : E →L[ℝ] (n → ℝ)) :
    ContDiff ℝ 1 (fun z : E => matrixQuadratic A (L z)) := by
  simpa [Function.comp_def] using
    (contDiff_one_coefficientQuadratic A).comp_continuousLinearMap (g := L)

/-- **Unconditional mark-Lipschitz constants from linear mark coordinates.**  On a
convex nonempty compact retained-root family, the quadratic kinetic form and probe
form composed with continuous linear label readouts have the mark-Lipschitz
constants of the mark modulus lane. -/
theorem hasMarkLipschitzConstantsOn_of_quadratic_readouts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (Lk Lg : E →L[ℝ] (n → ℝ)) :
    HasMarkLipschitzConstantsOn E K
      (fun z : E => matrixQuadratic A (Lk z))
      (fun z : E => matrixQuadratic B (Lg z)) := by
  have hck : ContDiff ℝ 1 (fun z : E => matrixQuadratic A (Lk z)) :=
    contDiff_one_coefficientQuadratic_comp A Lk
  have hcg : ContDiff ℝ 1 (fun z : E => matrixQuadratic B (Lg z)) :=
    contDiff_one_coefficientQuadratic_comp B Lg
  obtain ⟨Ck, hCk⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne hck
  obtain ⟨Cg, hCg⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne hcg
  exact hasMarkLipschitzConstantsOn_of_hasBoundedFDerivOn hconv hCk hCg

end OTSelector.Reconstruction
