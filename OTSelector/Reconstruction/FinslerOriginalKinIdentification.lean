import OTSelector.Reconstruction.FinslerOriginalKinMarkCoordinateInstantiation

/-!
# Identification of kin and g with affine quadratic readouts

This module closes the identification step of
`FinslerOriginalKinMarkCoordinateInstantiation`.  In the coefficient lane the
kinetic mark function and the probe are (on the retained roots) the frozen
coefficient quadratic form evaluated at the population seed label readout of the
mark; the label readout is affine (a linear coordinate map plus a constant seed
offset).  The module proves the C1 regularity of the affine composition and the
transfer of the mark-Lipschitz constants to any function that agrees, on the
retained root family, with such an affine quadratic readout.

The identification equality itself (actual `kin`/`g` definitions equal to the
readout composition on the retained roots) is the one remaining named hypothesis;
everything downstream of it is proved.
-/

noncomputable section
namespace OTSelector.Reconstruction

open scoped NNReal ENNReal

/-- The frozen quadratic form composed with an affine label readout is C1. -/
theorem contDiff_one_coefficientQuadratic_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (L : E →L[ℝ] (n → ℝ)) (c : n → ℝ) :
    ContDiff ℝ 1 (fun z : E => matrixQuadratic A (L z + c)) := by
  have hq : ContDiff ℝ 1 (fun v : n → ℝ => matrixQuadratic A v) :=
    contDiff_one_coefficientQuadratic A
  have hL : ContDiff ℝ 1 (fun z : E => L z) := L.contDiff
  have haff : ContDiff ℝ 1 (fun z : E => L z + c) := hL.add contDiff_const
  exact hq.comp haff

/-- **Mark-Lipschitz constants for affine quadratic readouts.**  On a convex
nonempty compact retained-root family, quadratic forms with affine label readouts
have the mark-Lipschitz constants of the mark modulus lane. -/
theorem hasMarkLipschitzConstantsOn_of_affine_quadratic_readouts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (Lk Lg : E →L[ℝ] (n → ℝ)) (ck cg : n → ℝ) :
    HasMarkLipschitzConstantsOn E K
      (fun z : E => matrixQuadratic A (Lk z + ck))
      (fun z : E => matrixQuadratic B (Lg z + cg)) := by
  obtain ⟨Ck, hCk⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne
    (contDiff_one_coefficientQuadratic_affine A Lk ck)
  obtain ⟨Cg, hCg⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne
    (contDiff_one_coefficientQuadratic_affine B Lg cg)
  exact hasMarkLipschitzConstantsOn_of_hasBoundedFDerivOn hconv hCk hCg

/-- **Identification transfer.**  If the actual `kin` and `g` agree on the retained
root family with affine quadratic readouts, they have the mark-Lipschitz constants.
This is the final composition step of the mark-Lipschitz lane; the identification
equalities are the only remaining input. -/
theorem hasMarkLipschitzConstantsOn_of_eqOn_affine_quadratic_readouts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    {kin g : E → ℝ} (A B : Matrix n n ℝ) (Lk Lg : E →L[ℝ] (n → ℝ))
    (ck cg : n → ℝ)
    (hkin : ∀ z ∈ K, kin z = matrixQuadratic A (Lk z + ck))
    (hg : ∀ z ∈ K, g z = matrixQuadratic B (Lg z + cg)) :
    HasMarkLipschitzConstantsOn E K kin g := by
  obtain ⟨⟨Lk', hLk'⟩, ⟨Lg', hLg'⟩⟩ :=
    hasMarkLipschitzConstantsOn_of_affine_quadratic_readouts hK hne hconv A B Lk Lg ck cg
  constructor
  · refine ⟨Lk', hLk'.1, ?_⟩
    intro z hz z' hz'
    rw [hkin z hz, hkin z' hz']
    exact hLk'.2 z hz z' hz'
  · refine ⟨Lg', hLg'.1, ?_⟩
    intro z hz z' hz'
    rw [hg z hz, hg z' hz']
    exact hLg'.2 z hz z' hz'

end OTSelector.Reconstruction
