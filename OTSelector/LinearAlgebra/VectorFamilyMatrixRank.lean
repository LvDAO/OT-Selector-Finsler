import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.VectorFamilyMatrixRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.VectorFamilyMatrixRank`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite-dimensional vector spaces with specified bases and an actual linear family map.

Objects: Coordinate matrix action, kernel correspondence and determinant/injectivity criteria.

Proof detail: Expand in the selected bases, identify matrix multiplication with the linear map and use finite-dimensional rank/inverse equivalences.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Basis and determinant adapters for elementary finite-dimensional linear algebra.
-/

/-!
# Matched-basis position matrices and actual linear rank

A vector-family matrix of a linear map is its ordinary basis matrix. Matrix multiplication
reads the actual image in the target basis, so its determinant is nonzero precisely when
the original map is injective. No geometric rank assumption enters these identities.
-/

open Matrix Module

noncomputable section
namespace OTSelector.Geometry

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]

/-- The vector columns are exactly the ordinary matrix of the original linear map. -/
theorem vectorFamilyMatrix_eq_toMatrix (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (R : W →L[ℝ] V) :
    vectorFamilyMatrix bV (fun j ↦ R (bW j)) = LinearMap.toMatrix bW bV R.toLinearMap := by
  ext i j
  exact (LinearMap.toMatrix_apply bW bV R.toLinearMap i j).symm

/-- Matrix multiplication is the actual image expressed in the target coordinates. -/
theorem vectorFamilyMatrix_mulVec_repr (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (R : W →L[ℝ] V) (w : W) :
    vectorFamilyMatrix bV (fun j ↦ R (bW j)) *ᵥ bW.equivFun w = bV.equivFun (R w) := by
  rw [vectorFamilyMatrix_eq_toMatrix]
  simpa only [Basis.equivFun_apply] using! R.toLinearMap.toMatrix_mulVec_repr bW bV w

/-- The matrix kernel readout is the kernel of the original map in the source basis. -/
theorem vectorFamilyMatrix_mulVec_repr_eq_zero_iff
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) (R : W →L[ℝ] V) (w : W) :
    vectorFamilyMatrix bV (fun j ↦ R (bW j)) *ᵥ bW.equivFun w = 0 ↔ R w = 0 := by
  rw [vectorFamilyMatrix_mulVec_repr]
  exact bV.equivFun.map_eq_zero_iff

/-- A square position matrix is nonsingular exactly when its original map is injective. -/
theorem vectorFamilyMatrix_det_ne_zero_iff_injective
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) (R : W →L[ℝ] V) :
    (vectorFamilyMatrix bV (fun j ↦ R (bW j))).det ≠ 0 ↔ Function.Injective R := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro h u v huv
    apply bW.equivFun.injective
    apply h
    rw [vectorFamilyMatrix_mulVec_repr, vectorFamilyMatrix_mulVec_repr, huv]
  · intro h u v huv
    obtain ⟨a, rfl⟩ := bW.equivFun.surjective u
    obtain ⟨b, rfl⟩ := bW.equivFun.surjective v
    rw [vectorFamilyMatrix_mulVec_repr, vectorFamilyMatrix_mulVec_repr] at huv
    exact congrArg bW.equivFun (h (bV.equivFun.injective huv))

end OTSelector.Geometry

end
end
