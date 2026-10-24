import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
## Lemma skeleton

* **Conditions:** A measurable contributing set V and an extended nonnegative u vanishing almost everywhere outside V.
* **Objects:** Equality of the restricted lower integral and the full lower integral.
* **Proof detail:** The indicator of V is almost everywhere equal to u; use lower-integral congruence and the restriction identity.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93

**Relationship to the sources:** Null-modification/indicator identity. Measurability of u itself is not required.
-/

/-! Restriction to actual contributing atoms requires vanishing almost everywhere,
not a restriction on every potential unoccupied edge in the ambient carrier. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- A same-measure AE zero condition outside a measurable contributor set is
sufficient to identify its restricted and full nonnegative readouts. -/
theorem setLIntegral_eq_of_ae_zero_outside
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : X → ℝ≥0∞} {V : Set X} (hV : MeasurableSet V)
    (hzero : ∀ᵐ x ∂μ, x ∉ V → u x = 0) :
    (∫⁻ x in V, u x ∂μ) = ∫⁻ x, u x ∂μ := by
  rw [← lintegral_indicator hV]
  apply lintegral_congr_ae
  filter_upwards [hzero] with x hx
  by_cases h : x ∈ V
  · exact indicator_of_mem h u
  · rw [indicator_of_notMem h, hx h]

end OTSelector.Probability
