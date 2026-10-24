import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
## Lemma skeleton

* **Conditions:** Any locally finite Borel coordinate measure tau, measurable retained K, positive scale s_n tending to infinity, and positive fixed radius R.
* **Objects:** For Lebesgue-almost every root in K, s_n^q times tau mass in the shrinking closed ball outside K tends to zero; volume is a special case.
* **Proof detail:** Differentiate tau restricted to K-complement relative to volume. Its RN density is zero on K. Substitute radius R/s_n and multiply by the exact product-norm ball volume (2R/s_n)^q.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Exercise 472Y(g)(i)–(ii), p. 26 (differentiation of two Radon measures); Theorem 472D, pp. 22–24.
  https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=26

**Relationship to the sources:** Derived scaled consequence of general measure differentiation, including a possible singular tau. The Euclidean-ball source transfers its zero limit to product-norm balls by norm comparison. No retained-set interior or pointwise density bound is needed.
-/

/-!
# Vanishing microscopic boundary mass at almost every retained root

Lebesgue density, the exact coordinate-ball volume and the original spatial
scaling show that missing retained-cell mass disappears inside every fixed
microscopic window. No interior-point assumption on the retained set is used.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace OTSelector.Probability

/-- Every locally finite coordinate mass outside a measurable retained core has
vanishing scaled local mass at almost every retained coordinate root. This also
controls original population mass beyond a compact core without a pointwise
upper density bound. -/
theorem ae_tendsto_scaled_missing_mass {q : ℕ}
    (τ : Measure (Fin q → ℝ)) [IsLocallyFiniteMeasure τ]
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(volume : Measure (Fin q → ℝ)).restrict K,
      Tendsto (fun n ↦ s n ^ q *
        (τ (closedBall x (R / s n) \ K)).toReal) atTop (𝓝 0) := by
  have hrad : Tendsto (fun n ↦ R / s n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlarge.const_div_atTop R,
      Filter.Eventually.of_forall fun n ↦ div_pos hR (hs n)⟩
  have hden := Besicovitch.ae_tendsto_rnDeriv (τ.restrict Kᶜ)
    (volume : Measure (Fin q → ℝ))
  have hrn := Measure.rnDeriv_restrict τ (volume : Measure (Fin q → ℝ)) hK.compl
  filter_upwards [ae_restrict_mem hK, hden.filter_mono ae_restrict_le,
    hrn.filter_mono ae_restrict_le] with x hx hdx hrnx
  have hzero : Tendsto (fun r ↦
      τ (closedBall x r \ K) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    have hz : (τ.restrict Kᶜ).rnDeriv (volume : Measure (Fin q → ℝ)) x = 0 := by
      rw [hrnx, Set.indicator_of_notMem (show x ∉ Kᶜ from fun h ↦ h hx)]
    have hset (r : ℝ) : closedBall x r ∩ Kᶜ = closedBall x r \ K := by
      ext y
      simp
    simpa only [hz, Measure.restrict_apply isClosed_closedBall.measurableSet, hset] using hdx
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
    (hzero.comp hrad)
  simp only [ENNReal.toReal_zero] at hreal
  have hlim := hreal.const_mul ((2 * R) ^ q)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro n
  change (2 * R) ^ q *
    (τ (closedBall x (R / s n) \ K) / volume (closedBall x (R / s n))).toReal = _
  rw [ENNReal.toReal_div, Real.volume_pi_closedBall x (div_pos hR (hs n)).le]
  simp only [Fintype.card_fin]
  rw [ENNReal.toReal_ofReal
    (pow_nonneg (mul_nonneg (by norm_num) (div_pos hR (hs n)).le) q)]
  have heq : 2 * (R / s n) = (2 * R) / s n := by ring
  rw [heq, div_pow]
  field_simp [ne_of_gt (hs n), ne_of_gt hR]

/-- A measurable retained core loses vanishing scaled mass in a fixed local window
at almost every retained root, even when the core has empty interior. -/
theorem ae_tendsto_scaled_missing_volume {q : ℕ}
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(volume : Measure (Fin q → ℝ)).restrict K,
      Tendsto (fun n ↦ s n ^ q *
        (volume (closedBall x (R / s n) \ K)).toReal) atTop (𝓝 0) :=
  ae_tendsto_scaled_missing_mass volume hK s hs hlarge hR

end OTSelector.Probability
