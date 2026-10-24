import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
## Lemma skeleton

* **Conditions:** A measurable window, good set and guard carrier; a cutoff<=1 supported on the guard, an energy bounded by a measurable majorant on the good window, and a clipping height.
* **Objects:** Clipped guarded energy integral bounded by the majorant plus clipping height times guarded bad mass.
* **Proof detail:** Split the window into its good and bad parts; compare pointwise with the majorant on the first and with the clipped constant on the second.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Elementary lower-integral comparison; no integrability or measurability of the target energy/cutoff is added beyond the actual header.
-/

/-!
# Guarded clipped readouts on the same measured window

A cutoff carried by C pays the measurable upper energy on the good part of W.
The remaining clipped energy costs at most the clipping height times the
actual guarded bad mass, without replacing or enlarging the underlying law.
-/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A guarded clipped window readout is bounded by its true upper readout
and the clipping height times the actual bad mass within the cutoff carrier. -/
theorem lintegral_guarded_window_clipped_le
    (Γ : Measure Ω) (W A C : Set Ω)
    (hW : MeasurableSet W) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (ψ energy upper : Ω → ℝ≥0∞) (hupper : Measurable upper)
    (hψ : ∀ x, ψ x ≤ 1) (hψzero : ∀ x, x ∉ C → ψ x = 0)
    (henergy : ∀ x ∈ W ∩ A, energy x ≤ upper x) (B : ℝ≥0∞) :
    (∫⁻ x, W.indicator (fun x ↦ ψ x * min B (energy x)) x ∂Γ) ≤
      (∫⁻ x, W.indicator upper x ∂Γ) + B * Γ ((W \ A) ∩ C) := by
  classical
  let bad := (W \ A) ∩ C
  have hbad : MeasurableSet bad := (hW.diff hA).inter hC
  calc
    _ ≤ ∫⁻ x, W.indicator upper x + bad.indicator (fun _ ↦ B) x ∂Γ := by
      apply lintegral_mono
      intro x
      by_cases hxW : x ∈ W
      · simp only [indicator_of_mem hxW]
        by_cases hxC : x ∈ C
        · have hweight : ψ x * min B (energy x) ≤ min B (energy x) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hψ x)
              (show (0 : ℝ≥0∞) ≤ min B (energy x) from bot_le)
          apply hweight.trans
          by_cases hxA : x ∈ A
          · exact (min_le_right _ _).trans
              ((henergy x ⟨hxW,hxA⟩).trans (le_add_right le_rfl))
          · rw [indicator_of_mem (show x ∈ bad from ⟨⟨hxW,hxA⟩,hxC⟩)]
            exact (min_le_left _ _).trans (le_add_left le_rfl)
        · rw [hψzero x hxC,zero_mul]
          exact bot_le
      · simp only [indicator_of_notMem hxW]
        exact bot_le
    _ = _ := by
      rw [lintegral_add_left (hupper.indicator hW),lintegral_indicator_const hbad]

/-- The same estimate expressed as restricted window integrals. -/
theorem setLIntegral_guarded_window_clipped_le
    (Γ : Measure Ω) (W A C : Set Ω)
    (hW : MeasurableSet W) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (ψ energy upper : Ω → ℝ≥0∞) (hupper : Measurable upper)
    (hψ : ∀ x, ψ x ≤ 1) (hψzero : ∀ x, x ∉ C → ψ x = 0)
    (henergy : ∀ x ∈ W ∩ A, energy x ≤ upper x) (B : ℝ≥0∞) :
    (∫⁻ x in W, ψ x * min B (energy x) ∂Γ) ≤
      (∫⁻ x in W, upper x ∂Γ) + B * Γ ((W \ A) ∩ C) := by
  simpa only [lintegral_indicator hW] using
    lintegral_guarded_window_clipped_le Γ W A C hW hA hC ψ energy upper
      hupper hψ hψzero henergy B

end OTSelector.Probability

