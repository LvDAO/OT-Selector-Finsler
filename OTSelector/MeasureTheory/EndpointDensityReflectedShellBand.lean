import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.EndpointDensityReflectedShellBand.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.EndpointDensityReflectedShellBand`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.EndpointDensityReflectedShellBand

## Lemma skeleton

* **Conditions:** The same interval density representation and right endpoint order-k bound, now for reflected Ico bands and their exact width.
* **Objects:** Reflected half-open interval and right-shell bounds with constant 2^k K t^k s.
* **Proof detail:** Bound the reflected distance-to-endpoint by 2t, then apply the constant density-envelope times interval-length estimate.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Ico counterpart of the elementary shell estimate; no boundary mass is silently discarded outside the supplied density region.
-/

/-! Local clock bands inherit the endpoint density order with their actual width.
The original measure is retained, including half-open partition boundaries. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A density bound on a reflected half-open interior band controls its original mass. -/
theorem measure_Ico_le_of_restrict_density_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h a b K : ℝ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun t ↦ ENNReal.ofReal (f t)))
    (hsub : Ico a b ⊆ Ioo l h)
    (hbound : ∀ t ∈ Ico a b, f t ≤ K) :
    μ (Ico a b) ≤ ENNReal.ofReal K * ENNReal.ofReal (b - a) := by
  calc
    μ (Ico a b) = (μ.restrict (Ioo l h)) (Ico a b) := by
      rw [Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hsub]
    _ = ((volume.restrict (Ioo l h)).withDensity
        (fun t ↦ ENNReal.ofReal (f t))) (Ico a b) := congrArg (fun η ↦ η (Ico a b)) hμ
    _ = ∫⁻ t in Ico a b, ENNReal.ofReal (f t) := by
      rw [withDensity_apply _ measurableSet_Ico, Measure.restrict_restrict_of_subset hsub]
    _ ≤ ∫⁻ _t in Ico a b, ENNReal.ofReal K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      exact ENNReal.ofReal_le_ofReal (hbound t ht)
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]

/-- The inward right dyadic shell obeys the same literal band-width estimate. -/
theorem measure_Ico_right_shell_le_of_density_power_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h ε K t a b s : ℝ} {k : ℕ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hεh : ε < h - l) (hK : 0 ≤ K)
    (hbound : ∀ r ∈ Ioo 0 ε, f (h - r) ≤ K * r ^ k)
    (ht : 0 < t) (h2t : 2 * t < ε)
    (ha : h - 2 * t ≤ a) (hb : b ≤ h - t) (hwidth : b - a ≤ s) :
    μ (Ico a b) ≤ ENNReal.ofReal (((2 : ℝ) ^ k * K) * t ^ k * s) := by
  have hsub : Ico a b ⊆ Ioo l h := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlocal : ∀ x ∈ Ico a b, f x ≤ K * (2 * t) ^ k := by
    intro x hx
    have hr : h - x ∈ Ioo 0 ε := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hfx := hbound (h - x) hr
    rw [sub_sub_cancel] at hfx
    exact hfx.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.1.le (by linarith [hx.1]) k) hK)
  calc
    μ (Ico a b) ≤ ENNReal.ofReal (K * (2 * t) ^ k) * ENNReal.ofReal (b - a) :=
      measure_Ico_le_of_restrict_density_bound hμ hsub hlocal
    _ ≤ ENNReal.ofReal (K * (2 * t) ^ k) * ENNReal.ofReal s :=
      by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (pow_nonneg (by positivity) k))]
      congr 1
      rw [mul_pow]
      ring

end OTSelector.Reconstruction

end
end
