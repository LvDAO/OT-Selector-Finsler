import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalVariationNullSet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalVariationNullSet`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.VariationNullSet

## Lemma skeleton

* **Conditions:** Finite measures converging to a finite law in full total variation and one measurable event null for every approximating measure.
* **Objects:** The same event is null for the limiting original law.
* **Proof detail:** Bound its limiting mass by the full variation discrepancy and let that discrepancy tend to zero.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).

Source relation (composition): Eventwise variation convergence consequence; no weak-convergence boundary condition is used.
-/

/-! Actual full-law variation preserves every common original null set. -/
open Set Function MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- A common null set for original finite laws remains null under actual
signed total-variation convergence. -/
theorem original_null_set_of_variation_tendsto
    {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] (ν : Measure X) [IsFiniteMeasure ν]
    (hvariation : Tendsto (fun n ↦
      ((μ n).toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ) atTop (𝓝 0))
    {S : Set X} (hS : MeasurableSet S) (hzero : ∀ n, μ n S = 0) : ν S = 0 := by
  have hbound n : ν.real S ≤ ((μ n).toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ := by
    have hn := SignedMeasure.norm_le_totalVariation ((μ n).toSignedMeasure - ν.toSignedMeasure) S
    rw [Measure.toSignedMeasure_sub_apply hS] at hn
    have hrealzero : (μ n).real S = 0 := by simp only [measureReal_def,hzero n,ENNReal.toReal_zero]
    rw [hrealzero,zero_sub,norm_neg,Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg] at hn
    have hmono : ((μ n).toSignedMeasure - ν.toSignedMeasure).totalVariation.real S ≤
        ((μ n).toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ S))
    exact hn.trans hmono
  have hle : ν.real S ≤ 0 := ge_of_tendsto hvariation (Filter.Eventually.of_forall hbound)
  exact (measureReal_eq_zero_iff).mp (le_antisymm hle measureReal_nonneg)

end OTSelector.Reconstruction

end
end
