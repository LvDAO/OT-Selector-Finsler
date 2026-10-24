import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ParameterizedJacobianMeasurable.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ParameterizedJacobianMeasurable`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite-dimensional normalized parameter spaces and the stated totalized Fréchet derivative convention.

Objects: Measurability of the normalized absolute determinant of the actual derivative.

Proof detail: Use measurability of the totalized derivative and continuous composition, determinant and absolute value.

Sources: D. H. Fremlin, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher) (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17); D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22).
Relation: Measurable-derivative/determinant adapter; it does not require unmentioned measurability of the original map away from its differentiability set.
-/

/-!
# Measurability of the actual normalized parameter Jacobian

The ordinary derivative is Borel for an arbitrary map with complete codomain.
Continuous composition with the chosen linear normalization, determinant and
absolute value therefore makes the actual parameter Jacobian Borel, without
assuming that an arbitrary off-domain extension of the map is measurable.
-/

open MeasureTheory

noncomputable section
namespace OTSelector.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V]

/-- The actual normalized derivative determinant is Borel for every original map. -/
theorem measurable_parameterizedJacobian (f : V → E) (ℓ : V ≃L[ℝ] E) :
    Measurable (parameterizedJacobian f ℓ) := by
  have hc : Continuous (fun A : V →L[ℝ] E ↦ A.comp ℓ.symm.toContinuousLinearMap) := by
    fun_prop
  exact (ContinuousLinearMap.continuous_det.comp hc).abs.measurable.comp
    (measurable_fderiv ℝ f)

end OTSelector.Geometry

end
end
