import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
## Lemma skeleton

* **Conditions:** An extended nonnegative double sequence with uniformly bounded total row sums and a componentwise pressure bound by each column liminf.
* **Objects:** Total countable pressure sum bounded by the same global budget.
* **Proof detail:** Apply Fatou under counting measure and compare with the uniform row budget.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Exercise 17(b), p. 86 (Fatou’s lemma).
  https://measure.axler.net/MIRA.pdf#page=101

**Relationship to the sources:** Direct countable nonnegative Fatou inequality; no domination or uniform integrability is assumed.
-/

/-! Countably many local lower bounds preserve one original global energy
budget under Fatou. Neither domination nor uniform integrability is needed. -/
open MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A local liminf lower bound on every actual seed energy preserves the single
global budget after summing all seeds. This allows singular energy concentration. -/
theorem tsum_le_of_local_liminf_and_global_energy_budget
    (energy : ℕ → ℕ → ℝ≥0∞) (pressure : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hbudget : ∀ n, ∑' j, energy n j ≤ C)
    (hlower : ∀ j, pressure j ≤ liminf (fun n ↦ energy n j) atTop) :
    ∑' j, pressure j ≤ C := by
  have hfatou := lintegral_liminf_le' (u := (atTop : Filter ℕ))
    (μ := (Measure.count : Measure ℕ))
    (fun n ↦ (measurable_of_countable (energy n)).aemeasurable)
  simp only [lintegral_count] at hfatou
  exact (ENNReal.tsum_le_tsum hlower).trans (hfatou.trans
    (liminf_le_of_frequently_le' (Frequently.of_forall hbudget)))

end OTSelector.Reconstruction
