import Mathlib.Analysis.Calculus.MeanValue
import OTSelector.MeasureTheory.NonatomicAbsolutelyContinuous
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.AffineDerivativeAtomlessness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.AffineDerivativeAtomlessness`; the selected original proof blocks follow. -/
section

/-!
Conditions: A real map has actual affine differential Ax+p, is nonconstant as specified, and the input law is absolutely continuous with respect to Haar.

Objects: Null level sets and atomless pushforward for quadratic/affine-gradient maps.

Proof detail: If A is nonzero, its affine zero set is null; otherwise use the nonzero constant differential. Apply the density-point fiber criterion.

Sources: Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22); D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Elementary affine-gradient consequence combined with measure differentiation; infinite restricted measures retain their actual assumptions.
-/

/-!
# Atomlessness for nonconstant functions with an affine derivative

An affine derivative either has nonzero linear part, so its zero fibre is Haar
null, or is a nonzero constant. Applying the existing differential criterion
again proves atomlessness of the original function, for every absolutely
continuous source measure, including restrictions of infinite measures.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A nonconstant scalar function whose derivative is affine has atomless
pushforward under every measure absolutely continuous with respect to Haar. -/
theorem nullSingletonClass_map_of_affine_fderiv
    (m : Measure E) [m.IsAddHaarMeasure] {μ : Measure E} (hμ : μ ≪ m)
    {f : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (p : E →L[ℝ] ℝ)
    (hd : ∀ x, HasFDerivAt f (A x + p) x)
    (hnonconstant : ∃ x y, f x ≠ f y) : NullSingletonClass (μ.map f) := by
  have hf : Differentiable ℝ f := fun x ↦ (hd x).differentiableAt
  apply nullSingletonClass_map_of_ac_ae_fderiv_ne_zero m hμ hf.continuous.measurable
    (Eventually.of_forall hf)
  by_cases hA : A = 0
  · have hp : p ≠ 0 := by
      intro hp
      obtain ⟨x, y, hxy⟩ := hnonconstant
      apply hxy
      exact is_const_of_fderiv_eq_zero hf (fun z ↦ by simp [(hd z).fderiv, hA, hp]) x y
    exact Eventually.of_forall (fun x ↦ by simpa [(hd x).fderiv, hA] using hp)
  · let g : E → E →L[ℝ] ℝ := fun x ↦ A x + p
    let : MeasurableSpace (E →L[ℝ] ℝ) := borel _
    have : BorelSpace (E →L[ℝ] ℝ) := ⟨rfl⟩
    have hg (x : E) : HasFDerivAt g A x := (A.hasFDerivAt).add_const p
    have hgm : Measurable g := (A.continuous.add continuous_const).measurable
    have hatom : NullSingletonClass (μ.map g) :=
      nullSingletonClass_map_of_ac_ae_fderiv_ne_zero m hμ hgm
        (Eventually.of_forall (fun x ↦ (hg x).differentiableAt))
        (Eventually.of_forall (fun x ↦ by simpa [(hg x).fderiv] using hA))
    have hnull := measure_singleton (μ := μ.map g) (0 : E →L[ℝ] ℝ)
    rw [Measure.map_apply hgm (measurableSet_singleton _)] at hnull
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    simpa only [(hd x).fderiv, mem_preimage, mem_singleton_iff, g] using hx

end OTSelector.Geometry

end
end
