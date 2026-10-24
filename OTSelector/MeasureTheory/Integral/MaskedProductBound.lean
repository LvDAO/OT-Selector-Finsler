import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
## Lemma skeleton

* **Conditions:** Two arbitrary measures, measurable rectangular mask and measurable nonnegative energy/volume majorants; the target u vanishes off the mask and has the stated pointwise bound.
* **Objects:** A masked iterated lower integral bounded by the actual band-energy and band-volume integrals.
* **Proof detail:** Compare u to the measurable rectangular majorant, integrate the clock indicator, and distribute scalar constants and the nonnegative sum.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19

**Relationship to the sources:** Lower-integral comparison corollary of Tonelli. The target u need not itself be measurable and no product independence is asserted.
-/

/-! Tonelli bounds for arbitrary correlated edge masks, retaining the actual
finite-band energy rather than replacing it by a full-energy bound per band. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- A pointwise energy bound on the same mark band and clock window gives its
literal iterated nonnegative integral. No independence of marks and clocks or
measurability of a dominating mask is required for this upper bound. -/
theorem lintegral_masked_band_product_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (κ : Measure Y) {B : Set X} {I : Set Y}
    (hB : MeasurableSet B) (hI : MeasurableSet I)
    (u : X × Y → ℝ≥0∞) {e v : X → ℝ≥0∞} (he : Measurable e) (hv : Measurable v)
    (A b d : ℝ≥0∞)
    (hpoint : ∀ m ∈ B, ∀ c ∈ I, u (m, c) ≤ A * (b * e m + d * v m))
    (hzero : ∀ m c, m ∉ B ∨ c ∉ I → u (m, c) = 0) :
    (∫⁻ m, ∫⁻ c, u (m, c) ∂κ ∂ν) ≤
      κ I * A * (b * (∫⁻ m in B, e m ∂ν) + d * (∫⁻ m in B, v m ∂ν)) := by
  have hm : Measurable (fun m ↦ A * (b * e m + d * v m)) :=
    (he.const_mul b |>.add (hv.const_mul d)).const_mul A
  have hsum : Measurable (fun m ↦ b * e m + d * v m) :=
    (he.const_mul b).add (hv.const_mul d)
  calc
    _ ≤ ∫⁻ m, B.indicator (fun z ↦ κ I * (A * (b * e z + d * v z))) m ∂ν := by
      apply lintegral_mono
      intro m
      by_cases hmb : m ∈ B
      · rw [indicator_of_mem hmb]
        calc
          _ ≤ ∫⁻ c, I.indicator (fun _ ↦ A * (b * e m + d * v m)) c ∂κ := by
            apply lintegral_mono
            intro c
            by_cases hci : c ∈ I
            · simpa only [indicator_of_mem hci] using hpoint m hmb c hci
            · simp only [hzero m c (Or.inr hci), indicator_of_notMem hci, le_refl]
          _ = _ := by rw [lintegral_indicator_const hI]; exact mul_comm _ _
      · simp only [hzero m _ (Or.inl hmb), lintegral_zero, indicator_of_notMem hmb, le_refl]
    _ = _ := by
      rw [lintegral_indicator hB, lintegral_const_mul (κ I) hm,
        lintegral_const_mul A hsum,
        lintegral_add_left (he.const_mul b), lintegral_const_mul b he,
        lintegral_const_mul d hv]
      ring

end OTSelector.Probability
