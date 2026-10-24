import Mathlib.LinearAlgebra.Matrix.SchurComplement
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CurveGraphJacobian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CurveGraphJacobian`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual differentiable graph coordinate change has nonzero longitudinal derivative and the stated inverse.

Objects: Block determinant formula and speed times graph-position Jacobian factorization.

Proof detail: Use a time-label basis, solve the inverse first differential, eliminate the longitudinal block and apply the Schur determinant identity.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Derived graph-coordinate determinant formula; the actual time correction is retained.
-/

/-!
# Exact determinants of the actual time-label derivatives

The full derivative in time-first coordinates has determinant equal to the
longitudinal velocity times the determinant of the same regraphed position
variation. Both the graph-time change and the supplied source and target bases
remain explicit.
-/

open Set Filter Matrix Module
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]

/-- The fixed product basis with time first and the supplied label basis second. -/
def timeLabelBasis (b : Basis ι ℝ W) : Basis (Unit ⊕ ι) ℝ (ℝ × W) :=
  (Basis.singleton Unit ℝ).prod b

private theorem det_scalar_fromBlocks (c : ℝ) (hc : c ≠ 0)
    (a v : ι → ℝ) (D : Matrix ι ι ℝ) :
    (Matrix.fromBlocks (fun _ _ : Unit ↦ c) (fun (_ : Unit) j ↦ a j)
      (fun i (_ : Unit) ↦ v i) D).det =
      c * (D - (Matrix.of fun i j ↦ v i * (a j / c))).det := by
  let A : Matrix Unit Unit ℝ := fun _ _ ↦ c
  let : Invertible A :=
    { invOf := fun _ _ ↦ c⁻¹
      invOf_mul_self := by
        ext i j
        change (∑ _ : Unit, c⁻¹ * c) = (1 : Matrix Unit Unit ℝ) i j
        simp [hc]
      mul_invOf_self := by
        ext i j
        change (∑ _ : Unit, c * c⁻¹) = (1 : Matrix Unit Unit ℝ) i j
        simp [hc] }
  change (Matrix.fromBlocks A _ _ D).det = _
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_unique]
  apply congrArg (fun N : Matrix ι ι ℝ ↦ c * N.det)
  ext i j
  simp [A, Matrix.mul_apply, div_eq_mul_inv]
  ring

/-- The graph-position parameter derivative has precisely the original tangential
velocity component removed, including its longitudinal-speed denominator. -/
theorem curveGraphPosition_label_fderiv {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) (w : W) :
    fderiv ℝ (fun z ↦ (curveGraphPosition γ e (z, q.2)).2) q.1 w =
      (fderiv ℝ γ (e.symm q) (w, 0)).2 -
        ((fderiv ℝ γ (e.symm q) (w, 0)).1 /
          (fderiv ℝ γ (e.symm q) (0, 1)).1) •
          (fderiv ℝ γ (e.symm q) (0, 1)).2 := by
  have hG : DifferentiableAt ℝ (curveGraphPosition γ e) q := hγ.comp q hi
  have hs : HasFDerivAt (fun z : W ↦ (z, q.2))
      (ContinuousLinearMap.inl ℝ W ℝ) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have hd := hG.hasFDerivAt.snd.comp q.1 hs
  change HasFDerivAt (fun z ↦ (curveGraphPosition γ e (z, q.2)).2) _ q.1 at hd
  rw [hd.fderiv]
  exact congrArg Prod.snd (curveGraphPosition_parameter_fderiv he hq hγ hi hv w)

/-- The exact full time-label determinant is longitudinal velocity times the
actual graph-position label determinant in the same two fixed bases. -/
theorem curveGraph_timeLabel_det (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) :
    (LinearMap.toMatrix (timeLabelBasis bW) (timeLabelBasis bV)
      ((fderiv ℝ γ (e.symm q)).comp
        (ContinuousLinearEquiv.prodComm ℝ ℝ W).toContinuousLinearMap).toLinearMap).det =
      (fderiv ℝ γ (e.symm q) (0, 1)).1 *
        (vectorFamilyMatrix bV (fun i ↦
          fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, q.2)).2) q.1 (bW i))).det := by
  let L := fderiv ℝ γ (e.symm q)
  let c := (L (0, 1)).1
  let a : ι → ℝ := fun i ↦ (L (bW i, 0)).1
  let v : ι → ℝ := fun i ↦ bV.repr (L (0, 1)).2 i
  let D : Matrix ι ι ℝ := fun i j ↦ bV.repr (L (bW j, 0)).2 i
  have hmatrix : LinearMap.toMatrix (timeLabelBasis bW) (timeLabelBasis bV)
      (L.comp (ContinuousLinearEquiv.prodComm ℝ ℝ W).toContinuousLinearMap).toLinearMap =
      Matrix.fromBlocks (fun _ _ : Unit ↦ c) (fun (_ : Unit) j ↦ a j)
        (fun i (_ : Unit) ↦ v i) D := by
    ext i j
    cases i <;> cases j <;>
      simp [timeLabelBasis, LinearMap.toMatrix_apply, Basis.prod_apply,
        Matrix.fromBlocks, L, c, a, v, D]
  have hcorr : D - (Matrix.of fun i j ↦ v i * (a j / c)) =
      vectorFamilyMatrix bV (fun i ↦
        fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, q.2)).2) q.1 (bW i)) := by
    ext i j
    simp only [Matrix.sub_apply, vectorFamilyMatrix]
    rw [curveGraphPosition_label_fderiv he hq hγ hi hv]
    simp [D, a, v, c, L, smul_eq_mul, mul_comm]
  rw [hmatrix, det_scalar_fromBlocks c hv, hcorr]

end OTSelector.Geometry

end
end
