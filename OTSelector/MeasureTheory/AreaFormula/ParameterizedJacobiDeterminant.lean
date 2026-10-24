import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphJacobian
import OTSelector.Geometry.Manifold.CurveGraphTime
import OTSelector.LinearAlgebra.VectorFamilyMatrixRank
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ParameterizedJacobiDeterminant.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ParameterizedJacobiDeterminant`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual graph-coordinate family has nonzero longitudinal speed and the specified differentiable inverse and normalization maps.

Objects: Factorization of its normalized absolute Jacobian into speed, graph-position determinant and normalization determinant.

Proof detail: Use the actual inverse clock derivative and chain rule, write the derivative as a block matrix and apply determinant multiplication.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Derived graph-coordinate determinant identity; constants and parameter Haar normalization are local definitions.
-/

/-!
# Actual parameter Jacobians and graph-position determinants

The parameter Jacobian retains the original longitudinal speed, the graph-position
matrix at the actual graph time, and the fixed determinant of the chosen linear
normalization in the supplied bases. The inverse graph clock is differentiated
explicitly, so no change of time or measure normalization is suppressed.
-/

open Set Filter Matrix Module
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]

/-- The actual parameter Jacobian equals the graph-position determinant multiplied
by longitudinal speed and the full fixed inverse-normalization basis determinant. -/
theorem parameterizedJacobian_eq_graphPosition_det
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) (ℓ : (ℝ × W) ≃L[ℝ] (ℝ × V))
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) :
    parameterizedJacobian (fun p : ℝ × W ↦ γ (p.2, p.1)) ℓ
        ((e.symm q).2, (e.symm q).1) =
      |(fderiv ℝ γ (e.symm q) (0, 1)).1| *
        |(vectorFamilyMatrix bV (fun i ↦
          fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, q.2)).2) q.1 (bW i))).det| *
        |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
          ℓ.symm.toLinearEquiv.toLinearMap).det| := by
  let S := ContinuousLinearEquiv.prodComm ℝ ℝ W
  have hd : fderiv ℝ (fun p : ℝ × W ↦ γ (p.2, p.1))
      ((e.symm q).2, (e.symm q).1) = (fderiv ℝ γ (e.symm q)).comp
        S.toContinuousLinearMap :=
    (hγ.hasFDerivAt.comp ((e.symm q).2, (e.symm q).1) S.hasFDerivAt).fderiv
  have hdet := curveGraph_timeLabel_det bW bV he hq hγ hi hv
  rw [vectorFamilyMatrix_eq_toMatrix bW bV] at hdet ⊢
  unfold parameterizedJacobian
  rw [hd]
  change |LinearMap.det (((fderiv ℝ γ (e.symm q)).comp
    S.toContinuousLinearMap).toLinearMap.comp ℓ.symm.toLinearEquiv.toLinearMap)| = _
  rw [← LinearMap.det_toMatrix (timeLabelBasis bV),
    LinearMap.toMatrix_comp (timeLabelBasis bV) (timeLabelBasis bW) (timeLabelBasis bV),
    Matrix.det_mul, hdet, abs_mul, abs_mul]

/-- At original time `t`, the actual graph time is the first position coordinate.
The recovered old-time derivative and normalized Jacobian retain the same speed
and graph-position matrix, together with the fixed normalization determinant. -/
theorem parameterizedJacobian_graphTime_data
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) (ℓ : (ℝ × W) ≃L[ℝ] (ℝ × V))
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {w : W} {t : ℝ} (hz : (w, t) ∈ e.source)
    (hγ : DifferentiableAt ℝ γ (w, t))
    (hi : DifferentiableAt ℝ e.symm (w, (γ (w, t)).1))
    (hv : (fderiv ℝ γ (w, t) (0, 1)).1 ≠ 0) :
    let s := (γ (w, t)).1
    let c := (fderiv ℝ γ (w, t) (0, 1)).1
    HasDerivAt (fun r ↦ (e.symm (w, r)).2) c⁻¹ s ∧
      parameterizedJacobian (fun p : ℝ × W ↦ γ (p.2, p.1)) ℓ (t, w) =
        |c| * |(vectorFamilyMatrix bV (fun i ↦
          fderiv ℝ (fun z ↦ (curveGraphPosition γ e (z, s)).2) w (bW i))).det| *
          |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
            ℓ.symm.toLinearEquiv.toLinearMap).det| := by
  have heval : e (w, t) = (w, (γ (w, t)).1) := by rw [he]; rfl
  have hq : (w, (γ (w, t)).1) ∈ e.target := heval ▸ e.map_source hz
  have hinverse : e.symm (w, (γ (w, t)).1) = (w, t) := by
    rw [← heval]
    exact e.left_inv hz
  have hγ' : DifferentiableAt ℝ γ (e.symm (w, (γ (w, t)).1)) := by
    rwa [hinverse]
  have hv' : (fderiv ℝ γ (e.symm (w, (γ (w, t)).1)) (0, 1)).1 ≠ 0 := by
    rwa [hinverse]
  refine ⟨?_, ?_⟩
  · simpa only [hinverse] using curveGraphTime_hasDerivAt he hq hγ' hi hv'
  · simpa only [hinverse] using
      parameterizedJacobian_eq_graphPosition_det bW bV ℓ he hq hγ' hi hv'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Changing the model coordinates and the parameter normalization together
conjugates the same square derivative and preserves its absolute determinant. -/
theorem parameterizedJacobian_linearEquiv_comp
    (A : E ≃L[ℝ] V) (ℓ : W ≃L[ℝ] E) (f : W → E) (q : W) :
    parameterizedJacobian (A ∘ f) (ℓ.trans A) q = parameterizedJacobian f ℓ q := by
  unfold parameterizedJacobian
  rw [A.comp_fderiv]
  change |LinearMap.det (A.toLinearEquiv.toLinearMap.comp
    ((((fderiv ℝ f q).comp ℓ.symm.toContinuousLinearMap).toLinearMap).comp
      A.symm.toLinearEquiv.toLinearMap))| = _
  exact congrArg abs (LinearMap.det_conj
    ((fderiv ℝ f q).comp ℓ.symm.toContinuousLinearMap).toLinearMap A.toLinearEquiv)

/-- The original-model Jacobian has the same graph-position formula in any fixed
adapted linear coordinates. The graph clock, longitudinal velocity and determinant
of the combined coordinate and parameter normalization all remain explicit. -/
theorem parameterizedJacobian_adaptedGraphTime_data
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) (ℓ : (ℝ × W) ≃L[ℝ] E)
    {γ : W × ℝ → E} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (A ∘ γ))
    {w : W} {t : ℝ} (hz : (w, t) ∈ e.source)
    (hγ : DifferentiableAt ℝ γ (w, t))
    (hi : DifferentiableAt ℝ e.symm (w, (A (γ (w, t))).1))
    (hv : (fderiv ℝ (A ∘ γ) (w, t) (0, 1)).1 ≠ 0) :
    let s := (A (γ (w, t))).1
    let c := (fderiv ℝ (A ∘ γ) (w, t) (0, 1)).1
    HasDerivAt (fun r ↦ (e.symm (w, r)).2) c⁻¹ s ∧
      parameterizedJacobian (fun p : ℝ × W ↦ γ (p.2, p.1)) ℓ (t, w) =
        |c| * |(vectorFamilyMatrix bV (fun i ↦
          fderiv ℝ (fun z ↦ (curveGraphPosition (A ∘ γ) e (z, s)).2) w (bW i))).det| *
          |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
            (ℓ.trans A).symm.toLinearEquiv.toLinearMap).det| := by
  have hγA : DifferentiableAt ℝ (A ∘ γ) (w, t) := A.differentiableAt.comp (w, t) hγ
  have hdata := parameterizedJacobian_graphTime_data bW bV (ℓ.trans A) he hz hγA hi hv
  refine ⟨hdata.1, ?_⟩
  exact (parameterizedJacobian_linearEquiv_comp A ℓ
    (fun p : ℝ × W ↦ γ (p.2, p.1)) (t, w)).symm.trans hdata.2

end OTSelector.Geometry

end
end
