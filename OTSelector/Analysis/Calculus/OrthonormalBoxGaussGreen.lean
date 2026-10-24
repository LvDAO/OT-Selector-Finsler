import OTSelector.Analysis.Calculus.BoxGaussGreen
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalOrthonormalCubeGaussGreen.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalOrthonormalCubeGaussGreen`; the selected original proof blocks follow. -/
section

/-!
Conditions: C1 scalar/vector fields, an actual orthonormal frame and an ordered coordinate box.

Objects: True normal Gauss–Green formula and its coordinate-gradient/pairing identities.

Proof detail: Pull back by the orthonormal coordinate map, differentiate by the chain rule, apply coordinate FTC/Fubini and identify the face normals through basis pairing.

Sources: D. H. Fremlin, Theorem 475N, p. 75 (Divergence Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=75); Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Box version independently proved by FTC and Fubini. The boundary is an explicit oriented face sum, not the book’s perimeter-measure encoding.
-/

/-! True normal Gauss–Green on an orthonormal-coordinate cube, with coordinate volume. -/

open Set Function MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual orthonormal-basis coordinates, as a continuous linear equivalence to raw reals. -/
def orthonormalCubeCoordinates {q : ℕ} (b : OrthonormalBasis (Fin q) ℝ E) :
    E ≃L[ℝ] (Fin q → ℝ) :=
  b.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin q) ℝ)

/-- The vector field pulled back to the actual orthonormal cube coordinates. -/
def orthonormalCubeVectorPullback {q : ℕ} (b : OrthonormalBasis (Fin q) ℝ E)
    (J : E → E) : (Fin q → ℝ) → (Fin q → ℝ) :=
  fun y ↦ orthonormalCubeCoordinates b (J ((orthonormalCubeCoordinates b).symm y))

/-- A coordinate is the true inner product with its chosen unit normal. -/
theorem orthonormalCubeCoordinates_apply {q : ℕ} (b : OrthonormalBasis (Fin q) ℝ E)
    (x : E) (i : Fin q) : orthonormalCubeCoordinates b x i = ⟪b i, x⟫_ℝ := by
  change b.repr x i = _
  exact b.repr_apply_apply x i

/-- The actual inverse coordinate map sends a raw coordinate direction to the original basis. -/
theorem orthonormalCubeCoordinates_symm_single {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) (i : Fin q) :
    (orthonormalCubeCoordinates b).symm (Pi.single i 1) = b i := by
  apply (orthonormalCubeCoordinates b).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext k
  rw [orthonormalCubeCoordinates_apply]
  simp [b.inner_eq_ite, Pi.single_apply, eq_comm]

/-- The inverse is the literal physical sum of the chosen basis vectors with raw coordinates. -/
theorem orthonormalCubeCoordinates_symm_eq_sum {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) (y : Fin q → ℝ) :
    (orthonormalCubeCoordinates b).symm y = ∑ i : Fin q, y i • b i := by
  classical
  calc
    (orthonormalCubeCoordinates b).symm y =
        ∑ i : Fin q, b.repr ((orthonormalCubeCoordinates b).symm y) i • b i :=
      (b.sum_repr _).symm
    _ = ∑ i : Fin q, y i • b i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      change orthonormalCubeCoordinates b ((orthonormalCubeCoordinates b).symm y) i = y i
      rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Each pulled-back vector component is the original physical field's actual normal readout. -/
theorem orthonormalCubeVectorPullback_apply {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) (J : E → E) (y : Fin q → ℝ) (i : Fin q) :
    orthonormalCubeVectorPullback b J y i =
      ⟪b i, J ((orthonormalCubeCoordinates b).symm y)⟫_ℝ :=
  orthonormalCubeCoordinates_apply b _ i

/-- Actual C¹ fields remain C¹ under the real basis-coordinate pullback. -/
theorem contDiff_orthonormalCubeVectorPullback {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) {J : E → E} (hJ : ContDiff ℝ 1 J) :
    ContDiff ℝ 1 (orthonormalCubeVectorPullback b J) :=
  (orthonormalCubeCoordinates b).contDiff.comp
    (hJ.comp (orthonormalCubeCoordinates b).symm.contDiff)

/-- The pullback's diagonal derivative is the actual physical derivative in the true basis
direction, paired with the same true unit normal. -/
theorem fderiv_orthonormalCubeVectorPullback_diag {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) {J : E → E} (hJ : ContDiff ℝ 1 J)
    (y : Fin q → ℝ) (i : Fin q) :
    fderiv ℝ (orthonormalCubeVectorPullback b J) y (Pi.single i 1) i =
      ⟪b i, fderiv ℝ J ((orthonormalCubeCoordinates b).symm y) (b i)⟫_ℝ := by
  let C := orthonormalCubeCoordinates b
  have hd := C.hasFDerivAt.comp y
    ((hJ.differentiable one_ne_zero (C.symm y)).hasFDerivAt.comp y C.symm.hasFDerivAt)
  change fderiv ℝ (C ∘ J ∘ C.symm) y (Pi.single i 1) i = _
  rw [hd.fderiv]
  change C (fderiv ℝ J (C.symm y) (C.symm (Pi.single i 1))) i = _
  rw [orthonormalCubeCoordinates_symm_single]
  exact orthonormalCubeCoordinates_apply b _ i

private theorem fderiv_orthonormalCubeScalarPullback_apply {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (y : Fin q → ℝ) (i : Fin q) :
    fderiv ℝ (fun y ↦ φ ((orthonormalCubeCoordinates b).symm y)) y (Pi.single i 1) =
      fderiv ℝ φ ((orthonormalCubeCoordinates b).symm y) (b i) := by
  have hd := (hφ.differentiable one_ne_zero
    ((orthonormalCubeCoordinates b).symm y)).hasFDerivAt.comp y
      (orthonormalCubeCoordinates b).symm.hasFDerivAt
  change fderiv ℝ (φ ∘ (orthonormalCubeCoordinates b).symm) y (Pi.single i 1) = _
  rw [hd.fderiv]
  change fderiv ℝ φ ((orthonormalCubeCoordinates b).symm y)
    ((orthonormalCubeCoordinates b).symm (Pi.single i 1)) = _
  rw [orthonormalCubeCoordinates_symm_single]

private theorem sum_basis_dual_pairing {q : ℕ} (b : OrthonormalBasis (Fin q) ℝ E)
    (L : E →L[ℝ] ℝ) (v : E) :
    (∑ i : Fin q, L (b i) * ⟪b i, v⟫_ℝ) = L v := by
  classical
  calc
    (∑ i : Fin q, L (b i) * ⟪b i, v⟫_ℝ) =
        ∑ i : Fin q, L (⟪b i, v⟫_ℝ • b i) := by
      simp only [_root_.map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
    _ = L (∑ i : Fin q, ⟪b i, v⟫_ℝ • b i) := (map_sum _ _ _).symm
    _ = L v := by rw [b.sum_repr']

/-- Genuine normal weighted Gauss–Green on an orthonormal-coordinate box. Volume and face
integrals use their literal raw coordinates. Each normal is the original physical `b i`, and
the weight derivative is applied to the original physical current. -/
theorem smooth_orthonormal_cube_weighted_gauss_green
    {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ E)
    (a c : Fin (n + 1) → ℝ) (hac : a ≤ c)
    {φ : E → ℝ} {J : E → E} (hφ : ContDiff ℝ 1 φ) (hJ : ContDiff ℝ 1 J) :
    (∫ y in Icc a c,
        φ ((orthonormalCubeCoordinates b).symm y) *
          (∑ i : Fin (n + 1),
            ⟪b i, fderiv ℝ J ((orthonormalCubeCoordinates b).symm y) (b i)⟫_ℝ) +
          fderiv ℝ φ ((orthonormalCubeCoordinates b).symm y)
            (J ((orthonormalCubeCoordinates b).symm y))) =
      ∑ i : Fin (n + 1),
        ((∫ t in Icc (a ∘ i.succAbove) (c ∘ i.succAbove),
            φ ((orthonormalCubeCoordinates b).symm (i.insertNth (c i) t)) *
              ⟪b i, J ((orthonormalCubeCoordinates b).symm (i.insertNth (c i) t))⟫_ℝ) -
          ∫ t in Icc (a ∘ i.succAbove) (c ∘ i.succAbove),
            φ ((orthonormalCubeCoordinates b).symm (i.insertNth (a i) t)) *
              ⟪b i, J ((orthonormalCubeCoordinates b).symm (i.insertNth (a i) t))⟫_ℝ) := by
  have h := smooth_box_weighted_gauss_green a c hac
    (φ := fun y ↦ φ ((orthonormalCubeCoordinates b).symm y))
    (j := orthonormalCubeVectorPullback b J)
    (hφ.comp (orthonormalCubeCoordinates b).symm.contDiff)
    (contDiff_orthonormalCubeVectorPullback b hJ)
  simpa only [fderiv_orthonormalCubeVectorPullback_diag b hJ,
    fderiv_orthonormalCubeScalarPullback_apply b hφ, orthonormalCubeVectorPullback_apply,
    sum_basis_dual_pairing] using h

end OTSelector.Reconstruction

end
end
