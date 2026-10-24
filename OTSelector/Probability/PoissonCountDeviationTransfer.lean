import OTSelector.Probability.PoissonSingleDeviation

/-!
Conditions: A measurable original natural-count readout with an explicit Poisson HasLaw.

Objects: Absolute centered-count integrability and original mean deviation≤sqrt(a).

Proof detail: Use the supplied law equality to transport the already proved single-count deviation estimate and its integrability.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.2, p. 29.
Relation: A genuine law-transfer wrapper, with the original population observable retained.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalReservePoissonCountDeviation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalReservePoissonCountDeviation`; the selected original proof blocks follow. -/
section

/-! Transfer the genuine single-count Poisson deviation through its exact law. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Exact-law transfer keeps the true surrounding experiment and its correlations. -/
theorem poissonCount_deviation_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℕ) (hf : Measurable f) (a : ℝ≥0)
    (hlaw : HasLaw f (poissonMeasure a) P) :
    Integrable (fun p ↦ |(f p : ℝ) - (a : ℝ)|) P ∧
    (∫ p, |(f p : ℝ) - (a : ℝ)| ∂P) ≤ Real.sqrt (a : ℝ) := by
  have hm : MeasurePreserving f P (poissonMeasure a) := ⟨hf, hlaw.map_eq⟩
  have hI : Integrable (fun n : ℕ ↦ |(n : ℝ) - (a : ℝ)|) (poissonMeasure a) :=
    ((integrable_id_poissonMeasure a).sub (integrable_const (a : ℝ))).abs
  have hg : Measurable (fun n : ℕ ↦ |(n : ℝ) - (a : ℝ)|) := by fun_prop
  refine ⟨hm.integrable_comp_of_integrable hI, ?_⟩
  calc
    _ = ∫ n : ℕ, |(n : ℝ) - (a : ℝ)| ∂poissonMeasure a := hlaw.integral_comp hg.aestronglyMeasurable
    _ ≤ _ := integral_abs_sub_id_poissonMeasure_le a

end OTSelector.Reconstruction

end
end
