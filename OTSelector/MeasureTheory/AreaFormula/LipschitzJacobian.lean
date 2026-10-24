import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian
import OTSelector.MeasureTheory.HaarLipschitzDistortion
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.LipschitzJacobian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.LipschitzJacobian`; the selected original proof blocks follow. -/
section

/-!
Conditions: A Lipschitz map on the stated finite-dimensional open set, injective on the measured subset for the area formula.

Objects: Almost-everywhere differentiability, null-image transfer and Jacobian integration over measurable subsets.

Proof detail: Apply Rademacher and Lipschitz null-image preservation, then the injective Jacobian change-of-variables theorem with the actual derivative.

Sources: D. H. Fremlin, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher) (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17); D. H. Fremlin, Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17 (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26); D. H. Fremlin, Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41 (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38).
Relation: Specialization/adapter for Haar and totalized derivative conventions; only the integrand measurability assumptions in each actual signature are used.
-/

/-!
# Change of variables for injective Lipschitz maps

On an open domain, Rademacher supplies the actual ordinary derivative almost
everywhere. Lipschitz control preserves null exceptional sets in the image, so
the exact Jacobian formulas hold on every measurable subset of the domain.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [m.IsAddHaarMeasure]
  {f : E → E} {U s : Set E} {C : ℝ≥0}

private theorem exists_differentiable_subset_image_ae_eq
    (hU : IsOpen U) (hLip : LipschitzOnWith C f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    ∃ t : Set E, t ⊆ s ∧ MeasurableSet t ∧
      (∀ x ∈ t, DifferentiableAt ℝ f x) ∧ t =ᵐ[m] s ∧ f '' t =ᵐ[m] f '' s := by
  classical
  have hae : ∀ᵐ x ∂m, x ∈ U → DifferentiableAt ℝ f x := by
    filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := m)] with x hx hxU
    exact (hx hxU).differentiableAt (hU.mem_nhds hxU)
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  let t := s \ N
  have hts : t ⊆ s := sdiff_subset
  have hdiff : ∀ x ∈ t, DifferentiableAt ℝ f x := by
    intro x hx
    have hg : x ∈ U → DifferentiableAt ℝ f x := by
      by_contra h
      exact hx.2 (hN h)
    exact hg (hsU hx.1)
  have ht : t =ᵐ[m] s := sdiff_null_ae_eq_self hN0
  have hnull : m (f '' (s \ t)) = 0 := by
    apply le_antisymm _ bot_le
    calc
      m (f '' (s \ t)) ≤ (C : ℝ≥0∞) ^ Module.finrank ℝ E * m (s \ t) :=
        haar_image_le_of_lipschitzOnWith m hLip (sdiff_subset.trans hsU)
      _ = 0 := by rw [(ae_eq_set.mp ht).2, mul_zero]
  have himg : f '' s =ᵐ[m] f '' t := by
    have he : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left hts]
    conv_lhs => rw [he, image_union]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hnull)
  exact ⟨t, hts, hs.diff hNm, hdiff, ht, himg.symm⟩

/-- The exact measure-map formula needs injectivity only on the measured subset. -/
theorem map_withDensity_abs_det_fderiv_of_lipschitzOnWith_injOn
    (hU : IsOpen U) (hLip : LipschitzOnWith C f U) (hinj : InjOn f s)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    Measure.map f ((m.restrict s).withDensity
      (fun x ↦ ENNReal.ofReal |(fderiv ℝ f x).det|)) = m.restrict (f '' s) := by
  obtain ⟨t, hts, ht, hdiff, htsae, himgae⟩ :=
    exists_differentiable_subset_image_ae_eq m hU hLip hs hsU
  have hchange := map_withDensity_abs_det_fderiv_eq_addHaar m ht.nullMeasurableSet
    (fun x hx ↦ (hdiff x hx).hasFDerivAt.hasFDerivWithinAt) (hinj.mono hts)
  simpa only [Measure.restrict_congr_set htsae, Measure.restrict_congr_set himgae]
    using hchange

/-- The exact nonnegative image integral needs injectivity only on the measured subset. -/
theorem lintegral_image_abs_det_fderiv_of_lipschitzOnWith_injOn
    (hU : IsOpen U) (hLip : LipschitzOnWith C f U) (hinj : InjOn f s)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (g : E → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y ∂m) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * g (f x) ∂m := by
  obtain ⟨t, hts, ht, hdiff, htsae, himgae⟩ :=
    exists_differentiable_subset_image_ae_eq m hU hLip hs hsU
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul m ht
    (fun x hx ↦ (hdiff x hx).hasFDerivAt.hasFDerivWithinAt) (hinj.mono hts) g
  simpa only [Measure.restrict_congr_set htsae, Measure.restrict_congr_set himgae]
    using hchange


/-- Actual derivative weights push Haar measure forward on every measurable subset
of an open injective Lipschitz domain; exceptional nondifferentiable points are null. -/
theorem map_withDensity_abs_det_fderiv_of_lipschitzOnWith
    (hU : IsOpen U) (hLip : LipschitzOnWith C f U) (hinj : InjOn f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    Measure.map f ((m.restrict s).withDensity
      (fun x ↦ ENNReal.ofReal |(fderiv ℝ f x).det|)) = m.restrict (f '' s) :=
  map_withDensity_abs_det_fderiv_of_lipschitzOnWith_injOn m hU hLip (hinj.mono hsU) hs hsU

/-- The exact image integral formula holds for arbitrary nonnegative integrands,
without requiring differentiability at every source point. -/
theorem lintegral_image_abs_det_fderiv_of_lipschitzOnWith
    (hU : IsOpen U) (hLip : LipschitzOnWith C f U) (hinj : InjOn f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (g : E → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y ∂m) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * g (f x) ∂m :=
  lintegral_image_abs_det_fderiv_of_lipschitzOnWith_injOn m hU hLip (hinj.mono hsU) hs hsU g

end OTSelector.Geometry

end
end
