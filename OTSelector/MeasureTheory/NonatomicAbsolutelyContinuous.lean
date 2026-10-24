import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import OTSelector.Analysis.Calculus.DensityOneDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.NonatomicAbsolutelyContinuous.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.NonatomicAbsolutelyContinuous`; the selected original proof blocks follow. -/
section

/-!
Conditions: A measure is absolutely continuous with respect to Haar and the real map has a nonzero actual differential almost everywhere only for that input measure.

Objects: Null fibers and an atomless pushed-forward law.

Proof detail: Apply the density-one constant-fiber argument on the absolutely continuous input support and transfer the null conclusion to every level set.

Sources: D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22); D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Local strengthening of the density-point criterion to an input-measure almost-everywhere derivative hypothesis; no Haar-a.e. assertion away from that support.
-/

/-!
# Atomless pushforwards from source-almost-everywhere differentials

For a measure absolutely continuous with respect to Haar measure, differentiability and
a nonzero derivative are needed only almost everywhere for the source measure. On each
measurable constant set, Haar density one transfers to the restricted source measure.
The derivative then vanishes at almost every such point, so the constant set is source null.
Applying this separately to every fiber proves that the pushforward has no atoms.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (m : Measure E) [IsAddHaarMeasure m]

/-- A measurable constant set is null for an absolutely continuous source law if the
actual derivative exists and is nonzero almost everywhere for that restricted law. -/
theorem measure_eq_zero_of_eqOn_const_of_ac_ae_fderiv_ne_zero {μ : Measure E}
    (hμ : μ ≪ m) {s : Set E} (hs : MeasurableSet s) {f : E → F} {c : F}
    (heq : EqOn f (fun _ ↦ c) s)
    (hdiff : ∀ᵐ x ∂μ.restrict s, DifferentiableAt ℝ f x)
    (hne : ∀ᵐ x ∂μ.restrict s, fderiv ℝ f x ≠ 0) : μ s = 0 := by
  have hdensity := (hμ.restrict s).ae_le (Besicovitch.ae_tendsto_measure_inter_div m s)
  have hfalse : ∀ᵐ x ∂μ.restrict s, False := by
    filter_upwards [hdensity, ae_restrict_mem hs, hdiff, hne] with x hx hxs hdx hnx
    exact hnx (fderiv_eq_zero_of_eqOn_const_of_density_one m hx hxs hdx heq)
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ]
    using hfalse

variable [MeasurableSpace F] [BorelSpace F]

/-- An absolutely continuous law has an atomless measurable pushforward when the actual
derivative exists and is nonzero source-almost everywhere. Neither condition is required
Haar-almost everywhere, and the source law need not be finite. -/
theorem nullSingletonClass_map_of_ac_ae_fderiv_ne_zero {μ : Measure E}
    (hμ : μ ≪ m) {f : E → F} (hf : Measurable f)
    (hdiff : ∀ᵐ x ∂μ, DifferentiableAt ℝ f x)
    (hne : ∀ᵐ x ∂μ, fderiv ℝ f x ≠ 0) : NullSingletonClass (μ.map f) := by
  refine ⟨fun c ↦ ?_⟩
  rw [Measure.map_apply hf (measurableSet_singleton c)]
  exact measure_eq_zero_of_eqOn_const_of_ac_ae_fderiv_ne_zero m hμ
    (hf (measurableSet_singleton c)) (fun _ hx ↦ hx)
    (ae_restrict_of_ae hdiff) (ae_restrict_of_ae hne)

end OTSelector.Geometry

end
