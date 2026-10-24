import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ParameterizedJacobianTransfer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ParameterizedJacobianTransfer`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two parameterized maps have the same actual first derivative at the point, with the specified linear normalization.

Objects: Equality of normalized Jacobians and the time/label-swapped adapters.

Proof detail: Replace the derivative by the equal derivative, compose with the normalization equivalence and simplify determinant and absolute value.

Sources: D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37).
Relation: Lean adapter for determinant invariance under equality of actual first jets; no area formula is needed.
-/

/-!
# Actual parameter Jacobians of maps with the same first jet

Equal ordinary first derivatives give equal normalized physical Jacobians. The
label-first to time-first change is applied to both actual maps, retaining the same
fixed linear parameter normalization.
-/

open Set
open scoped Topology

namespace OTSelector.Geometry

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Equal actual first jets give equal normalized parameter Jacobians. -/
theorem parameterizedJacobian_eq_of_hasFDerivAt
    {f g : V → E} {D : V →L[ℝ] E} {q : V}
    (hf : HasFDerivAt f D q) (hg : HasFDerivAt g D q) (ℓ : V ≃L[ℝ] E) :
    parameterizedJacobian f ℓ q = parameterizedJacobian g ℓ q := by
  simp only [parameterizedJacobian, hf.fderiv, hg.fderiv]

/-- The same joint position jet gives the same physical Jacobian with time first. -/
theorem parameterizedJacobian_timeFirst_eq_of_hasFDerivAt
    {γ Γ : W × ℝ → E} {D : (W × ℝ) →L[ℝ] E} {w : W} {t : ℝ}
    (hγ : HasFDerivAt γ D (w, t)) (hΓ : HasFDerivAt Γ D (w, t))
    (ℓ : (ℝ × W) ≃L[ℝ] E) :
    parameterizedJacobian (fun q : ℝ × W ↦ γ (q.2, q.1)) ℓ (t, w) =
      parameterizedJacobian (fun q : ℝ × W ↦ Γ (q.2, q.1)) ℓ (t, w) := by
  let S := ContinuousLinearEquiv.prodComm ℝ ℝ W
  exact parameterizedJacobian_eq_of_hasFDerivAt
    (hγ.comp (t, w) S.hasFDerivAt) (hΓ.comp (t, w) S.hasFDerivAt) ℓ

end OTSelector.Geometry

end
