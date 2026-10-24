import OTSelector.MeasureTheory.DyadicClockBandPartition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClockBandRealEnergyBudget.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClockBandRealEnergyBudget`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ClockBandRealEnergyBudget

## Lemma skeleton

* **Conditions:** Measurable real clock, disjoint deterministic half-open bands and a finite total extended nonnegative energy integral.
* **Objects:** Every band energy is finite and the sum of their real readouts is bounded by the one shared total energy.
* **Proof detail:** Use finite disjoint lower-integral additivity and domination by the full integral, then convert finite ENNReal terms to real values.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Finite-energy real-readout adapter preserving the literal disjoint clock partition.
-/

/-! The literal disjoint original clock bands carry one shared finite energy
budget, also after taking real readouts for quantitative L2 band summation. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Real values of the same original nonnegative band energies sum to at most
the original whole energy, preserving correlations between clock and momentum. -/
theorem clockGridBand_realEnergy_budget
    {Z : Type*} [MeasurableSpace Z] (η : Measure Z)
    {clock : Z → ℝ} (hclock : Measurable clock)
    (energy : Z → ℝ≥0∞) (hfinite : (∫⁻ z, energy z ∂η) ≠ ∞)
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    (∀ i : ℕ, (∫⁻ z in clock ⁻¹' clockGridBand a h i, energy z ∂η) ≠ ∞) ∧
    (∑ i ∈ Finset.range N,
      (∫⁻ z in clock ⁻¹' clockGridBand a h i, energy z ∂η).toReal) ≤
        (∫⁻ z, energy z ∂η).toReal := by
  have hband (i : ℕ) : (∫⁻ z in clock ⁻¹' clockGridBand a h i, energy z ∂η) ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (setLIntegral_le_lintegral _ _)
  refine ⟨hband, ?_⟩
  rw [← ENNReal.toReal_sum (fun i _ ↦ hband i)]
  exact ENNReal.toReal_mono hfinite (sum_clockGridBand_energy_le η hclock energy a hh N)

end OTSelector.Reconstruction

end
end
