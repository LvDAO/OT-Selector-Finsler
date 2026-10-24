import OTSelector.Probability.CavitySemidiscreteRootedWitness
import Mathlib.MeasureTheory.Group.Measure

/-!
# Actual spatial-root averaging of local transport energy

Integrating one translated source window counts each original edge by the Haar
mass of the window. The original mass scaling cancels the uniform-root density.
This gives local energy control and escape tails from the actual global cost.
-/

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {E Z : Type*} [AddCommGroup E] [MeasurableSpace E]
  [MeasurableAdd₂ E] [MeasurableNeg E] [MeasurableSub₂ E] [MeasurableSpace Z]

/-- Local weighted edge mass in the original source window translated by the root. -/
def cavityRootWindowReadout (π : Measure Z) (loc : Z → E) (w : Z → ℝ≥0∞)
    (B : Set E) (z : E) : ℝ≥0∞ :=
  ∫⁻ e, B.indicator (fun _ ↦ w e) (loc e - z) ∂π

/-- Actual Haar averaging counts each edge once per unit window volume. -/
theorem lintegral_cavityRootWindowReadout
    (β : Measure E) [SFinite β] [β.IsAddLeftInvariant] [β.IsNegInvariant]
    (π : Measure Z) [SFinite π] (loc : Z → E) (hloc : Measurable loc)
    (w : Z → ℝ≥0∞) (hw : Measurable w) (B : Set E) (hB : MeasurableSet B) :
    (∫⁻ z, cavityRootWindowReadout π loc w B z ∂β) =
      β B * ∫⁻ e, w e ∂π := by
  have hm : Measurable (fun v : E × Z ↦ B.indicator (fun _ ↦ w v.2) (loc v.2 - v.1)) := by
    change Measurable (fun v : E × Z ↦ if loc v.2 - v.1 ∈ B then w v.2 else 0)
    exact Measurable.ite (hB.preimage ((hloc.comp measurable_snd).sub measurable_fst))
      (hw.comp measurable_snd) measurable_const
  unfold cavityRootWindowReadout
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have heq (e : Z) : (∫⁻ z, B.indicator (fun _ ↦ w e) (loc e - z) ∂β) = w e * β B := by
    change (∫⁻ z, ((fun z ↦ loc e - z) ⁻¹' B).indicator (fun _ ↦ w e) z ∂β) = _
    rw [lintegral_indicator_const (hB.preimage (show Measurable (fun z : E ↦ loc e - z) from
      measurable_const.sub measurable_id))]
    rw [(β.measurePreserving_sub_left (loc e)).measure_preimage hB.nullMeasurableSet]
  simp only [heq]
  rw [lintegral_mul_const _ hw, mul_comm]

/-- The original scale N and root normalization 1/N cancel before local energy
is bounded. Cutting the root domain can only decrease the nonnegative readout. -/
theorem lintegral_cavityRoot_scaled_window_le
    (β : Measure E) [SFinite β] [β.IsAddLeftInvariant] [β.IsNegInvariant]
    (π : Measure Z) [SFinite π] (loc : Z → E) (hloc : Measurable loc)
    (w : Z → ℝ≥0∞) (hw : Measurable w) (B : Set E) (hB : MeasurableSet B)
    (D : Set E) (N : ℝ) (hN : 0 < N) :
    (∫⁻ z, ENNReal.ofReal N * cavityRootWindowReadout π loc w B z
      ∂cavityRootMeasure β D N) ≤ β B * ∫⁻ e, w e ∂π := by
  rw [cavityRootMeasure, lintegral_smul_measure,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hN)) ENNReal.ofReal_ne_top,
    one_mul]
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_eq
    (lintegral_cavityRootWindowReadout β π loc hloc w hw B hB)

/-- Escape mass from an original source window is controlled by the actual global
nonnegative energy, with exact root normalization and no finite-domain boundary error. -/
theorem lintegral_cavityRoot_scaled_window_tail_le
    (β : Measure E) [SFinite β] [β.IsAddLeftInvariant] [β.IsNegInvariant]
    (π : Measure Z) [SFinite π] (loc : Z → E) (hloc : Measurable loc)
    (w : Z → ℝ≥0∞) (hw : Measurable w) (B : Set E) (hB : MeasurableSet B)
    (D : Set E) (N : ℝ) (hN : 0 < N) (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    (∫⁻ z, ENNReal.ofReal N * cavityRootWindowReadout π loc
      (fun e ↦ if r ≤ w e then 1 else 0) B z ∂cavityRootMeasure β D N) ≤
      (β B * ∫⁻ e, w e ∂π) / r := by
  have hlocal (z : E) : r * cavityRootWindowReadout π loc
      (fun e ↦ if r ≤ w e then 1 else 0) B z ≤ cavityRootWindowReadout π loc w B z := by
    unfold cavityRootWindowReadout
    rw [← lintegral_const_mul' _ _ hrt]
    apply lintegral_mono
    intro e
    by_cases hBz : loc e - z ∈ B
    · simp only [indicator_of_mem hBz]
      split_ifs with hr
      · simpa only [mul_one] using hr
      · simp
    · simp only [indicator_of_notMem hBz, mul_zero, le_refl]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hr0) (Or.inl hrt)).mpr
  rw [mul_comm, ← lintegral_const_mul' _ _ hrt]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal N * cavityRootWindowReadout π loc w B z
        ∂cavityRootMeasure β D N := by
      apply lintegral_mono
      intro z
      change r * (ENNReal.ofReal N * cavityRootWindowReadout π loc
        (fun e ↦ if r ≤ w e then 1 else 0) B z) ≤ _
      rw [mul_left_comm]
      exact mul_le_mul_right (hlocal z) _
    _ ≤ _ := lintegral_cavityRoot_scaled_window_le β π loc hloc w hw B hB D N hN

end OTSelector.Probability
