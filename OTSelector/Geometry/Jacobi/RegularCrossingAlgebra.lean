import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Geometry.Jacobi.RegularCrossingAlgebra

## Lemma skeleton

* **Conditions:** Real finite square matrices with the Wronskian identity, an injective combined position/momentum frame and positive-definite velocity Hessian.

* **Objects:** A bijective crossing map from the position kernel to the quotient by its range.

* **Proof detail:** The Wronskian sends momentum on kerJ into the annihilator of rangeJ. Positive definiteness makes its pairing with the position derivative positive, so the quotient crossing map is injective. Rank-nullity gives equal dimensions and therefore bijectivity.

## Mathematical sources

- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662): Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T).
- [Matias Dahl, An brief introduction to Finsler geometry (12 July 2006)](https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31): Section 7, Definition 7.5 and Proposition 7.6, pp. 31–32.
- [OTSelector project, Algebra of regular focal crossings](main.tex#lem:regular-focal-crossing): main.tex label lem:regular-focal-crossing, line 9268.

Source relation (composition): Pointwise crossing algebra only; no actual Finsler frame, endpoint rank asymptotics or determinant-order theorem is assumed or claimed.
-/

/-!
# Algebra of regular focal crossings

At a possibly singular position matrix `J`, the Wronskian identity and injectivity of
the phase frame `(J, P)` imply that `P` sends `ker J` into the annihilator of `range J`.
Positivity of the velocity Hessian `C` then makes the position derivative `B * J + C * P`
an isomorphism from `ker J` to the quotient by `range J`.

This is the pointwise algebraic part of the regular-focal-crossing argument. It does not
construct the phase frame from Finsler geometry, establish its endpoint rank, or prove the
subsequent determinant and inverse asymptotics.
-/

open Matrix

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n]

/-- The Wronskian sends a position-kernel vector to the left kernel of the position matrix. -/
theorem wronskian_mulVec_kernel {J P : Matrix n n ℝ}
    (hW : Jᵀ * P = Pᵀ * J) {u : n → ℝ} (hu : J *ᵥ u = 0) :
    Jᵀ *ᵥ (P *ᵥ u) = 0 := by
  rw [Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]

/-- A momentum vector over `ker J` annihilates every position-range vector. -/
theorem wronskian_dotProduct_range {J P : Matrix n n ℝ}
    (hW : Jᵀ * P = Pᵀ * J) {u : n → ℝ} (hu : J *ᵥ u = 0) (v : n → ℝ) :
    (P *ᵥ u) ⬝ᵥ (J *ᵥ v) = 0 := by
  rw [← Matrix.dotProduct_transpose_mulVec, wronskian_mulVec_kernel hW hu]
  simp

/-- Full phase rank and a positive velocity Hessian give a strictly positive crossing pairing. -/
theorem focal_crossing_pairing_pos {J P B C : Matrix n n ℝ}
    (hphase : ∀ u, J *ᵥ u = 0 → P *ᵥ u = 0 → u = 0) (hC : C.PosDef)
    {u : n → ℝ} (hu : J *ᵥ u = 0) (hne : u ≠ 0) :
    0 < (P *ᵥ u) ⬝ᵥ ((B * J + C * P) *ᵥ u) := by
  have hPu : P *ᵥ u ≠ 0 := fun h ↦ hne (hphase u hu h)
  simpa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hu] using
    hC.dotProduct_mulVec_pos hPu

/-- A position-kernel vector whose derivative lies in the position range must vanish. -/
theorem focal_crossing_kernel_eq_zero {J P B C : Matrix n n ℝ}
    (hW : Jᵀ * P = Pᵀ * J)
    (hphase : ∀ u, J *ᵥ u = 0 → P *ᵥ u = 0 → u = 0) (hC : C.PosDef)
    {u : n → ℝ} (hu : J *ᵥ u = 0)
    (hrange : (B * J + C * P) *ᵥ u ∈ LinearMap.range J.mulVecLin) : u = 0 := by
  by_contra hne
  obtain ⟨v, hv⟩ := hrange
  have hp := focal_crossing_pairing_pos hphase hC hu hne (B := B)
  change J *ᵥ v = (B * J + C * P) *ᵥ u at hv
  rw [← hv, wronskian_dotProduct_range hW hu v] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- The derivative crossing, intrinsically valued in the quotient by the position range. -/
def focalCrossingMap (J D : Matrix n n ℝ) :
    LinearMap.ker J.mulVecLin →ₗ[ℝ] (n → ℝ) ⧸ LinearMap.range J.mulVecLin :=
  (LinearMap.range J.mulVecLin).mkQ.comp
    (D.mulVecLin.comp (LinearMap.ker J.mulVecLin).subtype)

/-- The Wronskian and positive velocity Hessian make the crossing map injective. -/
theorem focalCrossingMap_injective {J P B C : Matrix n n ℝ}
    (hW : Jᵀ * P = Pᵀ * J)
    (hphase : ∀ u, J *ᵥ u = 0 → P *ᵥ u = 0 → u = 0) (hC : C.PosDef) :
    Function.Injective (focalCrossingMap J (B * J + C * P)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro u hu
  apply Subtype.ext
  apply focal_crossing_kernel_eq_zero hW hphase hC u.property
  change Submodule.Quotient.mk ((B * J + C * P) *ᵥ (u : n → ℝ)) = 0 at hu
  exact (Submodule.Quotient.mk_eq_zero _).mp hu

/-- Rank-nullity identifies the dimensions of the position kernel and quotient range. -/
theorem finrank_position_kernel_eq_quotient (J : Matrix n n ℝ) :
    Module.finrank ℝ (LinearMap.ker J.mulVecLin) =
      Module.finrank ℝ ((n → ℝ) ⧸ LinearMap.range J.mulVecLin) := by
  have hk := J.mulVecLin.finrank_range_add_finrank_ker
  have hq := (LinearMap.range J.mulVecLin).finrank_quotient_add_finrank
  omega

/-- At full phase rank, every positive-Hessian Hamiltonian position crossing is an isomorphism. -/
theorem focalCrossingMap_bijective {J P B C : Matrix n n ℝ}
    (hW : Jᵀ * P = Pᵀ * J)
    (hphase : ∀ u, J *ᵥ u = 0 → P *ᵥ u = 0 → u = 0) (hC : C.PosDef) :
    Function.Bijective (focalCrossingMap J (B * J + C * P)) := by
  have hi := focalCrossingMap_injective hW hphase hC (B := B)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_position_kernel_eq_quotient J)).mp hi⟩

end OTSelector.Geometry
