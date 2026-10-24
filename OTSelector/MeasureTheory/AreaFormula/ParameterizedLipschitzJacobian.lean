import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.LipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ParameterizedLipschitzJacobian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ParameterizedLipschitzJacobian`; the selected original proof blocks follow. -/
section

/-!
Conditions: A Lipschitz parameter map, a specified linear normalization equivalence and injectivity on the integrated subset.

Objects: Normalized parameter Jacobian and change of variables for the explicitly transported Haar measure.

Proof detail: Transfer to standard coordinates by the equivalence, use the actual derivative chain rule and determinant scaling, then apply the area formula.

Sources: D. H. Fremlin, Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17 (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26); D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22).
Relation: Parameterized area-formula adapter; the reference measure and determinant normalization are explicit.
-/

/-!
# Actual Jacobians with linear parameter normalization

An actual map between equal-dimensional parameter and model spaces is normalized
by a continuous linear equivalence before taking its derivative determinant.
Lipschitz control on an open domain and injectivity on the measured subset suffice
for exact change of variables. The reference measure retains the normalization.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual square derivative determinant after the chosen parameter normalization. -/
def parameterizedJacobian (f : V → E) (ℓ : V ≃L[ℝ] E) (q : V) : ℝ :=
  |((fderiv ℝ f q).comp ℓ.symm.toContinuousLinearMap).det|

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace V] [BorelSpace V] (m : Measure E) [m.IsAddHaarMeasure]

/-- Injectivity is required only on the measured parameter set. The integrand can
be any nonnegative function, and the derivative is the actual ordinary derivative. -/
theorem lintegral_image_parameterizedJacobian (ℓ : V ≃L[ℝ] E)
    {f : V → E} {U s : Set V} {C : ℝ≥0}
    (hU : IsOpen U) (hLip : LipschitzOnWith C f U) (hinj : InjOn f s)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (g : E → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y ∂m) =
      ∫⁻ q in s, ENNReal.ofReal (parameterizedJacobian f ℓ q) * g (f q)
        ∂(tubeParameterMeasure ℓ m) := by
  let fhat : E → E := f ∘ ℓ.symm
  have hU' : IsOpen (ℓ.symm ⁻¹' U) := hU.preimage ℓ.symm.continuous
  have hLip' := hLip.comp ℓ.symm.lipschitzWith.lipschitzOnWith
    (show MapsTo ℓ.symm (ℓ.symm ⁻¹' U) U from fun _ h ↦ h)
  have hs' : MeasurableSet (ℓ '' s) :=
    ℓ.toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs
  have hsU' : ℓ '' s ⊆ ℓ.symm ⁻¹' U := by
    rintro _ ⟨q, hq, rfl⟩
    simpa using hsU hq
  have hinj' : InjOn fhat (ℓ '' s) := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩ heq
    apply congrArg ℓ
    apply hinj hq hr
    simpa [fhat] using heq
  have himg : fhat '' (ℓ '' s) = f '' s := by
    simp only [fhat, image_image, Function.comp_def, ℓ.symm_apply_apply]
  have hchange := lintegral_image_abs_det_fderiv_of_lipschitzOnWith_injOn m
    hU' hLip' hinj' hs' hsU' g
  rw [himg] at hchange
  rw [hchange, ← (measurePreserving_tubeNormalization ℓ m).setLIntegral_comp_emb
    ℓ.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z ↦ ENNReal.ofReal |(fderiv ℝ fhat z).det| * g (fhat z)) s]
  simp only [fhat, ContinuousLinearEquiv.comp_right_fderiv,
    ℓ.symm_apply_apply, Function.comp_apply, parameterizedJacobian]

/-- The actual image volume is the integral of its normalized parameter Jacobian. -/
theorem measure_image_parameterizedJacobian (ℓ : V ≃L[ℝ] E)
    {f : V → E} {U s : Set V} {C : ℝ≥0}
    (hU : IsOpen U) (hLip : LipschitzOnWith C f U) (hinj : InjOn f s)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    m (f '' s) = ∫⁻ q in s, ENNReal.ofReal (parameterizedJacobian f ℓ q)
      ∂(tubeParameterMeasure ℓ m) := by
  simpa using lintegral_image_parameterizedJacobian m ℓ hU hLip hinj hs hsU (fun _ ↦ 1)

end OTSelector.Geometry

end
end
