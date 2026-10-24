import OTSelector.Probability.PoissonCountDiscrepancy

/-!
Conditions: A measurable original pair readout with an explicit HasLaw equal to the product of two equal-rate Poisson laws.

Objects: Original-law absolute pair-difference integrability and mean≤sqrt(2a).

Proof detail: Transport both integrability and the proved independent Poisson pair discrepancy through the exact supplied pushforward law.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: An exact-law transfer. No marginal-law-only shortcut supplies the product law or its color independence.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalReservePoissonPairDiscrepancy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalReservePoissonPairDiscrepancy`; the selected original proof blocks follow. -/
section

/-! A reusable exact-law transfer for the genuine two-color Poisson discrepancy. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Transfer the actual Poisson-pair discrepancy through its proved law. This
preserves arbitrary correlations of the surrounding experiment. -/
theorem poissonPair_discrepancy_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℕ × ℕ) (hf : Measurable f) (a : ℝ≥0)
    (hlaw : HasLaw f ((poissonMeasure a).prod (poissonMeasure a)) P) :
    Integrable (fun p ↦ |((f p).1 : ℝ) - ((f p).2 : ℝ)|) P ∧
    (∫ p, |((f p).1 : ℝ) - ((f p).2 : ℝ)| ∂P) ≤ Real.sqrt (2 * (a : ℝ)) := by
  have hm : MeasurePreserving f P ((poissonMeasure a).prod (poissonMeasure a)) := ⟨hf, hlaw.map_eq⟩
  have hI : Integrable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|)
      ((poissonMeasure a).prod (poissonMeasure a)) :=
    (((integrable_id_poissonMeasure a).comp_fst _).sub
      ((integrable_id_poissonMeasure a).comp_snd _)).abs
  have hg : Measurable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|) := by fun_prop
  refine ⟨hm.integrable_comp_of_integrable hI, ?_⟩
  calc
    _ = ∫ z : ℕ × ℕ, |(z.1 : ℝ) - (z.2 : ℝ)| ∂((poissonMeasure a).prod (poissonMeasure a)) :=
      hlaw.integral_comp hg.aestronglyMeasurable
    _ ≤ _ := integral_abs_sub_poissonPair_le a

end OTSelector.Reconstruction

end
end
