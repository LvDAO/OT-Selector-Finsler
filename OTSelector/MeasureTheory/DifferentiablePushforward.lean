import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import OTSelector.Analysis.Calculus.DensityOneDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.NonatomicDifferentiablePushforward.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.NonatomicDifferentiablePushforward`; the selected original proof blocks follow. -/
section

/-!
Conditions: A real map is differentiable with nonzero differential almost everywhere for Haar measure; the Lipschitz version uses Rademacher and the explicitly stated dimension hypotheses.

Objects: Null level sets and atomless pushforward for an absolutely continuous input law.

Proof detail: At a density-one point of a constant fiber the derivative vanishes; differentiation of measures therefore makes each fiber null, and absolute continuity transfers this to the input law.

Sources: D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22); D. H. Fremlin, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher) (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17); D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Derived density-point criterion for atomlessness, with the actual almost-everywhere and absolute-continuity hypotheses retained.
-/

/-!
# Null fibers from nonzero actual differentials

Lebesgue density and the uniqueness of differentials on density-one sets show that a
constant level set has zero Haar measure wherever the actual differential is nonzero.
Absolutely continuous input laws therefore have atomless pushforwards. The local
Lipschitz consumer supplies differentiability by Rademacher on an open chart domain.

The nonzero-differential hypothesis is explicit: this module does not yet prove it
for the difference of two original Finsler distance functions.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (m : Measure E) [IsAddHaarMeasure m]

/-- A measurable constant set is Haar null if the actual differential exists and is
nonzero almost everywhere on that set. No regular-level or lower-gradient bound is used. -/
theorem measure_eq_zero_of_eqOn_const_of_ae_fderiv_ne_zero {s : Set E}
    (hs : MeasurableSet s) {f : E → F} {c : F} (heq : EqOn f (fun _ ↦ c) s)
    (hdiff : ∀ᵐ x ∂m.restrict s, DifferentiableAt ℝ f x)
    (hne : ∀ᵐ x ∂m.restrict s, fderiv ℝ f x ≠ 0) : m s = 0 := by
  have hfalse : ∀ᵐ x ∂m.restrict s, False := by
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div m s,
      ae_restrict_mem hs, hdiff, hne] with x hx hxs hdx hnx
    exact hnx (fderiv_eq_zero_of_eqOn_const_of_density_one m hx hxs hdx heq)
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ] using hfalse

variable [MeasurableSpace F] [BorelSpace F]

/-- Every fiber in a measurable domain is Haar null when the actual differential is
nonzero almost everywhere in that domain. The exceptional set may depend on the fiber. -/
theorem measure_fiber_eq_zero_of_ae_fderiv_ne_zero {s : Set E}
    (hs : MeasurableSet s) {f : E → F} (hf : Measurable f)
    (hdiff : ∀ᵐ x ∂m.restrict s, DifferentiableAt ℝ f x)
    (hne : ∀ᵐ x ∂m.restrict s, fderiv ℝ f x ≠ 0) (c : F) :
    m (s ∩ f ⁻¹' {c}) = 0 := by
  apply measure_eq_zero_of_eqOn_const_of_ae_fderiv_ne_zero m (f := f) (c := c)
    (hs.inter (hf (measurableSet_singleton c)))
  · intro x hx
    exact hx.2
  · exact ae_restrict_of_ae_restrict_of_subset inter_subset_left hdiff
  · exact ae_restrict_of_ae_restrict_of_subset inter_subset_left hne

/-- Any law absolutely continuous with respect to Haar measure and carried by the domain
has null singleton pushforward masses under a measurable map with nonzero differential. -/
theorem nullSingletonClass_map_of_ae_fderiv_ne_zero {s : Set E}
    (hs : MeasurableSet s) {f : E → F} (hf : Measurable f)
    (hdiff : ∀ᵐ x ∂m.restrict s, DifferentiableAt ℝ f x)
    (hne : ∀ᵐ x ∂m.restrict s, fderiv ℝ f x ≠ 0)
    (μ : Measure E) (hμ : μ ≪ m) (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    NullSingletonClass (μ.map f) := by
  refine ⟨fun c ↦ ?_⟩
  rw [Measure.map_apply hf (measurableSet_singleton c)]
  rw [← Measure.restrict_eq_self_of_ae_mem hμs,
    Measure.restrict_apply (hf (measurableSet_singleton c))]
  exact hμ (by simpa only [inter_comm] using
    measure_fiber_eq_zero_of_ae_fderiv_ne_zero m hs hf hdiff hne c)

/-- Rademacher supplies the differentiability input for a map Lipschitz on an open domain.
The source law may have zeros in its density and need not be finite. -/
theorem nullSingletonClass_map_of_lipschitzOnWith [FiniteDimensional ℝ F]
    {s : Set E} (hs : IsOpen s) {f : E → F} (hf : Measurable f)
    {L : ℝ≥0} (hLip : LipschitzOnWith L f s)
    (hne : ∀ᵐ x ∂m.restrict s, fderiv ℝ f x ≠ 0)
    (μ : Measure E) (hμ : μ ≪ m) (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    NullSingletonClass (μ.map f) := by
  apply nullSingletonClass_map_of_ae_fderiv_ne_zero m hs.measurableSet hf _ hne μ hμ hμs
  filter_upwards [hLip.ae_differentiableWithinAt (μ := m) hs.measurableSet,
    ae_restrict_mem hs.measurableSet] with x hx hxs
  exact hx.differentiableAt (hs.mem_nhds hxs)

end OTSelector.Geometry

end
end
