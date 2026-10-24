import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
## Lemma skeleton

* **Conditions:** The original scalar law has the stated density representation on an open interval; density is bounded by K on a subinterval or by K times distance-to-endpoint to natural order k.
* **Objects:** Subinterval mass bound and left/right endpoint mass of order r^(k+1).
* **Proof detail:** Bound the density by its constant upper envelope on the r-interval and multiply by its length.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Coarse density-times-length estimate, with constant K rather than the sharp K/(k+1). It does not presume density positivity beyond the ofReal representation.
-/

/-! A physical conditional density with endpoint order `k` gives original
endpoint mass of order `k+1`. The estimates use the unchanged physical measure. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A uniform density bound on an interior interval bounds its actual mass. -/
theorem measure_interval_le_of_restrict_density_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h a b K : ℝ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun t ↦ ENNReal.ofReal (f t)))
    (hsub : Ioo a b ⊆ Ioo l h)
    (hbound : ∀ t ∈ Ioo a b, f t ≤ K) :
    μ (Ioo a b) ≤ ENNReal.ofReal K * ENNReal.ofReal (b - a) := by
  calc
    μ (Ioo a b) = (μ.restrict (Ioo l h)) (Ioo a b) := by
      rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub]
    _ = ((volume.restrict (Ioo l h)).withDensity
        (fun t ↦ ENNReal.ofReal (f t))) (Ioo a b) := congrArg (fun η ↦ η (Ioo a b)) hμ
    _ = ∫⁻ t in Ioo a b, ENNReal.ofReal (f t) := by
      rw [withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict_of_subset hsub]
    _ ≤ ∫⁻ _t in Ioo a b, ENNReal.ofReal K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ENNReal.ofReal_le_ofReal (hbound t ht)
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]

/-- Original left endpoint mass is at most `K r^(k+1)` when its literal physical
density is at most `K s^k` on the endpoint neighborhood. -/
theorem measure_left_endpoint_le_of_density_power_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h ε K : ℝ} {k : ℕ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun t ↦ ENNReal.ofReal (f t)))
    (hεh : ε < h - l) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Ioo 0 ε, f (l + s) ≤ K * s ^ k)
    {r : ℝ} (hr : r ∈ Ioo 0 ε) :
    μ (Ioo l (l + r)) ≤ ENNReal.ofReal (K * r ^ (k + 1)) := by
  have hsub : Ioo l (l + r) ⊆ Ioo l h := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2, hr.2]⟩
  have hb : ∀ t ∈ Ioo l (l + r), f t ≤ K * r ^ k := by
    intro t ht
    have hs : t - l ∈ Ioo 0 ε := ⟨by linarith [ht.1], by linarith [ht.2, hr.2]⟩
    have hlocal := hbound (t - l) hs
    rw [add_sub_cancel] at hlocal
    exact hlocal.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hs.1.le (by linarith [ht.2]) k) hK)
  have hi := measure_interval_le_of_restrict_density_bound hμ hsub hb
  have heq : ENNReal.ofReal (K * r ^ k) * ENNReal.ofReal (l + r - l) =
      ENNReal.ofReal (K * r ^ (k + 1)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hK (pow_nonneg hr.1.le k))]
    congr 1
    rw [pow_succ]
    ring
  exact hi.trans_eq heq

/-- The actual right endpoint mass has the same inward power estimate. -/
theorem measure_right_endpoint_le_of_density_power_bound
    {μ : Measure ℝ} {f : ℝ → ℝ} {l h ε K : ℝ} {k : ℕ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun t ↦ ENNReal.ofReal (f t)))
    (hεh : ε < h - l) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Ioo 0 ε, f (h - s) ≤ K * s ^ k)
    {r : ℝ} (hr : r ∈ Ioo 0 ε) :
    μ (Ioo (h - r) h) ≤ ENNReal.ofReal (K * r ^ (k + 1)) := by
  have hsub : Ioo (h - r) h ⊆ Ioo l h := by
    intro t ht
    exact ⟨by linarith [ht.1, hr.2], ht.2⟩
  have hb : ∀ t ∈ Ioo (h - r) h, f t ≤ K * r ^ k := by
    intro t ht
    have hs : h - t ∈ Ioo 0 ε := ⟨by linarith [ht.2], by linarith [ht.1, hr.2]⟩
    have hlocal := hbound (h - t) hs
    rw [sub_sub_cancel] at hlocal
    exact hlocal.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hs.1.le (by linarith [ht.1]) k) hK)
  have hi := measure_interval_le_of_restrict_density_bound hμ hsub hb
  have heq : ENNReal.ofReal (K * r ^ k) * ENNReal.ofReal (h - (h - r)) =
      ENNReal.ofReal (K * r ^ (k + 1)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hK (pow_nonneg hr.1.le k))]
    congr 1
    rw [pow_succ]
    ring
  exact hi.trans_eq heq

end OTSelector.Reconstruction
