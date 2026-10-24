import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.EndpointDensityShellBand.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.EndpointDensityShellBand`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.EndpointDensityShellBand

## Lemma skeleton

* **Conditions:** A scalar density representation on an open interval, an endpoint order-k upper bound and half-open bands lying within distances t and 2t, with width at most s.
* **Objects:** Half-open interval mass and left/right shell mass at most 2^k K t^k s.
* **Proof detail:** Bound the density on the actual band by K(2t)^k and integrate this constant over its length.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Coarse density-times-actual-width estimate retaining Ioc boundary conventions.
-/

/-! Local clock bands inherit the endpoint density order with their actual width.
The original measure is retained, including half-open partition boundaries. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A density bound on a half-open interior band controls its original mass. -/
theorem measure_Ioc_le_of_restrict_density_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h a b K : ℝ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun t ↦ ENNReal.ofReal (f t)))
    (hsub : Ioc a b ⊆ Ioo l h)
    (hbound : ∀ t ∈ Ioc a b, f t ≤ K) :
    μ (Ioc a b) ≤ ENNReal.ofReal K * ENNReal.ofReal (b - a) := by
  calc
    μ (Ioc a b) = (μ.restrict (Ioo l h)) (Ioc a b) := by
      rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hsub]
    _ = ((volume.restrict (Ioo l h)).withDensity
        (fun t ↦ ENNReal.ofReal (f t))) (Ioc a b) := congrArg (fun η ↦ η (Ioc a b)) hμ
    _ = ∫⁻ t in Ioc a b, ENNReal.ofReal (f t) := by
      rw [withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict_of_subset hsub]
    _ ≤ ∫⁻ _t in Ioc a b, ENNReal.ofReal K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ENNReal.ofReal_le_ofReal (hbound t ht)
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]

/-- A width-`s` source band inside the left dyadic shell has mass at most
`2^k K t^k s`; no lower density bound or prescribed band balance is used. -/
theorem measure_Ioc_left_shell_le_of_density_power_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h ε K t a b s : ℝ} {k : ℕ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hεh : ε < h - l) (hK : 0 ≤ K)
    (hbound : ∀ r ∈ Ioo 0 ε, f (l + r) ≤ K * r ^ k)
    (ht : 0 < t) (h2t : 2 * t < ε)
    (ha : l + t ≤ a) (hb : b ≤ l + 2 * t) (hwidth : b - a ≤ s) :
    μ (Ioc a b) ≤ ENNReal.ofReal (((2 : ℝ) ^ k * K) * t ^ k * s) := by
  have hsub : Ioc a b ⊆ Ioo l h := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlocal : ∀ x ∈ Ioc a b, f x ≤ K * (2 * t) ^ k := by
    intro x hx
    have hr : x - l ∈ Ioo 0 ε := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hfx := hbound (x - l) hr
    rw [add_sub_cancel] at hfx
    exact hfx.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.1.le (by linarith [hx.2]) k) hK)
  calc
    μ (Ioc a b) ≤ ENNReal.ofReal (K * (2 * t) ^ k) * ENNReal.ofReal (b - a) :=
      measure_Ioc_le_of_restrict_density_bound hμ hsub hlocal
    _ ≤ ENNReal.ofReal (K * (2 * t) ^ k) * ENNReal.ofReal s :=
      by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (pow_nonneg (by positivity) k))]
      congr 1
      rw [mul_pow]
      ring

/-- The inward right dyadic shell obeys the same literal band-width estimate. -/
theorem measure_Ioc_right_shell_le_of_density_power_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h ε K t a b s : ℝ} {k : ℕ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hεh : ε < h - l) (hK : 0 ≤ K)
    (hbound : ∀ r ∈ Ioo 0 ε, f (h - r) ≤ K * r ^ k)
    (ht : 0 < t) (h2t : 2 * t < ε)
    (ha : h - 2 * t ≤ a) (hb : b ≤ h - t) (hwidth : b - a ≤ s) :
    μ (Ioc a b) ≤ ENNReal.ofReal (((2 : ℝ) ^ k * K) * t ^ k * s) := by
  have hsub : Ioc a b ⊆ Ioo l h := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlocal : ∀ x ∈ Ioc a b, f x ≤ K * (2 * t) ^ k := by
    intro x hx
    have hr : h - x ∈ Ioo 0 ε := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hfx := hbound (h - x) hr
    rw [sub_sub_cancel] at hfx
    exact hfx.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.1.le (by linarith [hx.1]) k) hK)
  calc
    μ (Ioc a b) ≤ ENNReal.ofReal (K * (2 * t) ^ k) * ENNReal.ofReal (b - a) :=
      measure_Ioc_le_of_restrict_density_bound hμ hsub hlocal
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
