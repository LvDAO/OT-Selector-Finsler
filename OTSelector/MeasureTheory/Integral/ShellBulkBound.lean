import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
## Lemma skeleton

* **Conditions:** Measurable W and W0, and a nonnegative Z bounded by full on W and by tail on W0.
* **Objects:** Integral over W bounded by full*mu(W minus W0)+tail*mu(W).
* **Proof detail:** Split into W minus W0 and W intersect W0; bound the first piece by full and the second by tail and the full window mass.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93

**Relationship to the sources:** Elementary nonnegative shell/bulk comparison. W0 need not be a subset of W.
-/

/-! # An exact collar-and-bulk integral estimate -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A field bounded globally by its full budget and in the inner region by its
tail budget has precisely a collar-volume plus bulk-tail integral bound. -/
theorem lintegral_on_le_shell_and_bulk
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {W W₀ : Set X}
    (hW : MeasurableSet W) (hW₀ : MeasurableSet W₀)
    {Z : X → ℝ≥0∞} {full tail : ℝ≥0∞}
    (hfull : ∀ z ∈ W, Z z ≤ full) (hdeep : ∀ z ∈ W₀, Z z ≤ tail) :
    (∫⁻ z in W, Z z ∂μ) ≤ full * μ (W \ W₀) + tail * μ W := by
  classical
  calc
    _ ≤ ∫⁻ z in W, ((W \ W₀).indicator (fun _ ↦ full) z + tail) ∂μ := by
      apply setLIntegral_mono' hW
      intro z hz
      by_cases hinner : z ∈ W₀
      · simpa only [indicator_of_notMem (show z ∉ W \ W₀ from fun h ↦ h.2 hinner), zero_add]
          using hdeep z hinner
      · simpa only [indicator_of_mem (show z ∈ W \ W₀ from ⟨hz, hinner⟩)]
          using (hfull z hz).trans (le_add_right le_rfl)
    _ = (∫⁻ z in W, (W \ W₀).indicator (fun _ ↦ full) z ∂μ) + tail * μ W := by
      rw [lintegral_add_left (measurable_const.indicator (hW.diff hW₀)), setLIntegral_const]
    _ = _ := by
      rw [lintegral_indicator (hW.diff hW₀), setLIntegral_const,
        Measure.restrict_apply (hW.diff hW₀), inter_eq_left.mpr sdiff_subset]

end OTSelector.Reconstruction
