import OTSelector.Analysis.InnerProductSpace.OrthonormalFaceCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeTraceCompactnessFaceGeometry.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeTraceCompactnessFaceGeometry`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual finite orthonormal frame and nonnegative/positive radius where specified.

Objects: Literal centered-cube face maps, their normal/tangent coordinates, image and dimension.

Proof detail: Evaluate the orthonormal coefficients, solve each tangential affine coordinate and use finite-dimensional basis expansion.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Terence Tao, Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61).
Relation: Elementary face parametrization adapter for the chosen frame.
-/

/-! Literal centered-cube face coordinates in the chosen actual orthonormal frame. -/
open Set Function
open scoped BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual lower-corner shift of a centered physical cube face. -/
def originalCenteredCubeFaceOffset {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) (R : ℝ) : EuclideanSpace ℝ (Fin q) :=
  (-R) • (∑ k : Fin q, b k) + (if j.2 = 0 then 0 else 2*R) • b j.1

/-- A genuine physical centered-cube face point; the parameter lives in
the original unit tangent cube, whose physical side length is 2R. -/
def originalCenteredCubeFacePoint {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) (R : ℝ) (y : {k : Fin q // k ≠ j.1} → ℝ) :
    EuclideanSpace ℝ (Fin q) :=
  originalCenteredCubeFaceOffset b j R + orthonormalFaceMap b j.1 ((2*R) • y)

/-- The literal tangent face map has zero component in the true face normal. -/
theorem inner_orthonormalFaceMap_normal {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (i : Fin q)
    (y : {k : Fin q // k ≠ i} → ℝ) : ⟪b i, orthonormalFaceMap b i y⟫_ℝ = 0 := by
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1
    ((range_orthonormalFaceMap b i) ▸ (show orthonormalFaceMap b i y ∈
      (orthonormalFaceMap b i).range from ⟨y,rfl⟩))

/-- Every other physical coordinate is precisely its original tangent parameter. -/
theorem inner_orthonormalFaceMap_tangent {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (i k : Fin q)
    (hk : k ≠ i) (y : {k : Fin q // k ≠ i} → ℝ) :
    ⟪b k, orthonormalFaceMap b i y⟫_ℝ = y ⟨k,hk⟩ := by
  classical
  change ⟪b k, ∑ a : {k : Fin q // k ≠ i}, y a • b a.1⟫_ℝ = _
  rw [inner_sum, Finset.sum_eq_single ⟨k,hk⟩]
  · simp [inner_smul_right]
  · intro a _ ha
    have hka : k ≠ a.1 := fun h ↦ ha (Subtype.ext h.symm)
    rw [inner_smul_right, b.inner_eq_zero hka, mul_zero]
  · simp

/-- The actual shifted point lies on the correct normal side of the cube. -/
theorem inner_originalCenteredCubeFacePoint_normal {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) (R : ℝ) (y : {k : Fin q // k ≠ j.1} → ℝ) :
    ⟪b j.1, originalCenteredCubeFacePoint b j R y⟫_ℝ =
      if j.2 = 0 then -R else R := by
  rw [originalCenteredCubeFacePoint, inner_add_right, inner_orthonormalFaceMap_normal, add_zero]
  by_cases hside : j.2 = 0
  · simp [originalCenteredCubeFaceOffset, inner_smul_right, inner_sum,
      b.inner_eq_ite, hside]
  · simp [originalCenteredCubeFaceOffset, inner_add_right, inner_smul_right, inner_sum,
      b.inner_eq_ite, hside]
    ring

/-- The physical tangent coordinates use the true affine side scale 2R. -/
theorem inner_originalCenteredCubeFacePoint_tangent {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) (R : ℝ) (y : {k : Fin q // k ≠ j.1} → ℝ)
    (k : Fin q) (hk : k ≠ j.1) :
    ⟪b k, originalCenteredCubeFacePoint b j R y⟫_ℝ = -R + 2*R*y ⟨k,hk⟩ := by
  rw [originalCenteredCubeFacePoint, inner_add_right,
    inner_orthonormalFaceMap_tangent b j.1 k hk]
  by_cases hside : j.2 = 0 <;>
    simp [originalCenteredCubeFaceOffset, inner_add_right, inner_smul_right, inner_sum,
      b.inner_eq_ite, hk, hside]

/-- Original unit-face parameters land in the actual centered physical cube,
with the correct chosen normal face coordinate. -/
theorem originalCenteredCubeFacePoint_mem_cube {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) {R : ℝ} (hR : 0 ≤ R)
    {y : {k : Fin q // k ≠ j.1} → ℝ} (hy : y ∈ Icc 0 1) :
    ∀ k : Fin q, ⟪b k, originalCenteredCubeFacePoint b j R y⟫_ℝ ∈ Icc (-R) R := by
  intro k
  by_cases hk : k = j.1
  · subst k
    rw [inner_originalCenteredCubeFacePoint_normal]
    split_ifs <;> constructor <;> linarith
  · rw [inner_originalCenteredCubeFacePoint_tangent b j R y k hk]
    have h0 : 0 ≤ y ⟨k,hk⟩ := hy.1 ⟨k,hk⟩
    have h1 : y ⟨k,hk⟩ ≤ 1 := hy.2 ⟨k,hk⟩
    constructor <;> nlinarith

/-- Every point of the genuine original orthonormal cube face is obtained
from the literal unit tangent cube; no part of the physical face is omitted. -/
theorem image_originalCenteredCubeFacePoint {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) {R : ℝ} (hR : 0 < R) :
    originalCenteredCubeFacePoint b j R '' Icc (0 : ({k : Fin q // k ≠ j.1} → ℝ)) 1 =
      {x | (∀ k : Fin q, ⟪b k, x⟫_ℝ ∈ Icc (-R) R) ∧
        ⟪b j.1, x⟫_ℝ = if j.2 = 0 then -R else R} := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨originalCenteredCubeFacePoint_mem_cube b j hR.le hy,
      inner_originalCenteredCubeFacePoint_normal b j R y⟩
  · rintro ⟨hxc,hxn⟩
    let y : {k : Fin q // k ≠ j.1} → ℝ := fun k ↦ (⟪b k.1, x⟫_ℝ + R) / (2*R)
    have hy : y ∈ Icc 0 1 := by
      constructor
      · intro k
        change 0 ≤ (⟪b k.1, x⟫_ℝ + R) / (2*R)
        exact div_nonneg (by linarith [(hxc k.1).1]) (by positivity)
      · intro k
        change (⟪b k.1, x⟫_ℝ + R) / (2*R) ≤ 1
        apply (div_le_one (by positivity)).mpr
        linarith [(hxc k.1).2]
    refine ⟨y,hy,?_⟩
    apply b.repr.injective
    ext k
    simp only [b.repr_apply_apply]
    by_cases hk : k = j.1
    · subst k
      rw [inner_originalCenteredCubeFacePoint_normal, hxn]
    · rw [inner_originalCenteredCubeFacePoint_tangent b j R y k hk]
      dsimp only [y]
      field_simp [(show (2*R : ℝ) ≠ 0 by positivity)]
      ring

/-- The actual tangent parameter dimension is exactly the codimension-one
face dimension of the same original ambient cube. -/
theorem card_originalCubeFaceCoordinates {q : ℕ} (i : Fin q) :
    Fintype.card {k : Fin q // k ≠ i} = q - 1 := by
  simpa only [Fintype.card_fin, Fintype.card_unique] using
    Fintype.card_subtype_compl (fun k : Fin q ↦ k = i)

/-- The unit-face representation is the same genuine face as fixed normal
coordinate plus centered physical tangent coordinates. This exact identity
connects the stationary offset convention with literal surface integrals. -/
theorem originalCenteredCubeFacePoint_eq_normal_add_centered_tangent {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) (R : ℝ) (y : {k : Fin q // k ≠ j.1} → ℝ) :
    originalCenteredCubeFacePoint b j R y =
      (if j.2 = 0 then -R else R) • b j.1 +
        orthonormalFaceMap b j.1 ((fun _ ↦ -R) + (2*R) • y) := by
  apply b.repr.injective
  ext k
  simp only [b.repr_apply_apply]
  by_cases hk : k = j.1
  · subst k
    rw [inner_originalCenteredCubeFacePoint_normal, inner_add_right,
      inner_smul_right, b.inner_eq_one, inner_orthonormalFaceMap_normal]
    simp
  · rw [inner_originalCenteredCubeFacePoint_tangent b j R y k hk, inner_add_right,
      inner_smul_right, b.inner_eq_zero hk, inner_orthonormalFaceMap_tangent b j.1 k hk]
    simp

end OTSelector.Reconstruction

end
end
