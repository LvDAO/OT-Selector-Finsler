import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map

/-!
## Lemma skeleton

* **Conditions:** An integrable real function, a measurable map with exact marginal pushforward, and measurable marginal sets whose masses tend to zero along any filter.
* **Objects:** Integrals of the function on the pulled-back marginal sets tend to zero.
* **Proof detail:** The exact pushforward identifies pullback masses; absolute continuity of the integral bounds their absolute set integrals.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3B, Theorem 3.28, pp. 90–91.
  https://measure.axler.net/MIRA.pdf#page=105
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Arbitrary-filter and pullback-set consequence of the small-set integral theorem.
-/

/-! Integrable losses on pullbacks of small marginal sets. -/
open Filter MeasureTheory
noncomputable section
namespace OTSelector.Probability

/-- A small set of the exact marginal removes a vanishing integral from the
original joint measure; no independence or nesting of the sets is needed. -/
theorem tendsto_setIntegral_preimage_zero_of_marginal_mass_zero
    {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (c : X → Y) (hc : Measurable c)
    (hpush : μ.map c = ν) (w : X → ℝ) (hw : Integrable w μ)
    (S : I → Set Y) (hS : ∀ n, MeasurableSet (S n))
    (l : Filter I) (hsmall : Tendsto (fun n ↦ ν (S n)) l (nhds 0)) :
    Tendsto (fun n ↦ ∫ x in c ⁻¹' S n, w x ∂μ) l (nhds 0) := by
  have heq (n : I) : μ (c ⁻¹' S n) = ν (S n) := by
    rw [← hpush, Measure.map_apply hc (hS n)]
  exact hw.tendsto_setIntegral_nhds_zero (by simpa only [Function.comp_def, heq] using hsmall)

end OTSelector.Probability
