import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.NonproperProbeCutoffLoss.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.NonproperProbeCutoffLoss`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.NonproperProbeCutoffLoss

## Lemma skeleton

* **Conditions:** An arbitrary plan, bounded source-supported real probe and [0,1] target cutoff equal to one on a measurable compact carrier; sample maps may be arbitrary.
* **Objects:** Cutoff error bounded by the actual source-window target-escape mass, pointwise and in lower-integral expectation.
* **Proof detail:** The error vanishes inside the target carrier and off the source window; compare it with the constant times the rectangle indicator and integrate twice.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Lower-integral comparison permits infinite plan mass and requires no extra sample-map measurability.
-/

/-!
# Nonproper target-cutoff error for a bounded original probe

The whole plan may have infinite total mass and a nonproper projection. Only
the actual escape mass over the source-localized probe enters the estimate.
-/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Removing a target cutoff costs the actual escape mass, even for a whole
plan of infinite total mass. No finiteness of either projected marginal is used. -/
theorem lintegral_bounded_probe_cutoff_error_le_escape
    (π : Measure (X × Y))
    (H : X × Y → ℝ) (C : ℝ) (hbound : ∀ e, |H e| ≤ C)
    (U : Set X) (hU : MeasurableSet U) (hsource : ∀ e, e.1 ∉ U → H e = 0)
    (χ : Y → ℝ) (hχ : ∀ y, χ y ∈ Icc 0 1)
    (K : Set Y) (hK : MeasurableSet K) (hχK : EqOn χ 1 K) :
    (∫⁻ e, ENNReal.ofReal |H e - H e * χ e.2| ∂π) ≤
      ENNReal.ofReal C * π (U ×ˢ Kᶜ) := by
  have he (e : X × Y) : ENNReal.ofReal |H e - H e * χ e.2| ≤
      (U ×ˢ Kᶜ).indicator (fun _ ↦ ENNReal.ofReal C) e := by
    by_cases hu : e.1 ∈ U
    · by_cases hk : e.2 ∈ K
      · have hχe : χ e.2 = 1 := hχK hk
        rw [hχe, mul_one, sub_self, abs_zero, ENNReal.ofReal_zero]
        exact zero_le
      · rw [indicator_of_mem (show e ∈ U ×ˢ Kᶜ from ⟨hu, hk⟩)]
        apply ENNReal.ofReal_le_ofReal
        have hf : |1 - χ e.2| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr (hχ e.2).2)]
          linarith [(hχ e.2).1]
        calc
          _ = |H e| * |1 - χ e.2| := by rw [← abs_mul]; congr 1; ring
          _ ≤ |H e| * 1 := mul_le_mul_of_nonneg_left hf (abs_nonneg _)
          _ ≤ C := by simpa only [mul_one] using hbound e
    · simp only [hsource e hu, zero_mul, sub_self, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  calc
    _ ≤ ∫⁻ e, (U ×ˢ Kᶜ).indicator (fun _ ↦ ENNReal.ofReal C) e ∂π := lintegral_mono he
    _ = _ := by rw [lintegral_indicator (hU.prod hK.compl), lintegral_const,
      Measure.restrict_apply_univ]

/-- The same cutoff error passes directly to the original experiment's
expectation. Measurability and integrability of the uncut probe are not premises. -/
theorem lintegral_expected_bounded_probe_cutoff_error_le_escape
    (P : Measure Ω) (π : Ω → Measure (X × Y))
    (H : Ω → X × Y → ℝ) (C : ℝ)
    (hbound : ∀ ω e, |H ω e| ≤ C)
    (U : Set X) (hU : MeasurableSet U)
    (hsource : ∀ ω e, e.1 ∉ U → H ω e = 0)
    (χ : Y → ℝ) (hχ : ∀ y, χ y ∈ Icc 0 1)
    (K : Set Y) (hK : MeasurableSet K) (hχK : EqOn χ 1 K) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal |H ω e - H ω e * χ e.2| ∂π ω ∂P) ≤
      ENNReal.ofReal C * ∫⁻ ω, π ω (U ×ˢ Kᶜ) ∂P := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal C * π ω (U ×ˢ Kᶜ) ∂P :=
      lintegral_mono fun ω ↦ lintegral_bounded_probe_cutoff_error_le_escape
        (π ω) (H ω) C (hbound ω) U hU (hsource ω) χ hχ K hK hχK
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end OTSelector.Probability

end
end
