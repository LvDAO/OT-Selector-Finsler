import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.GCongr

/-!
## Lemma skeleton

* **Conditions:** Extended nonnegative functions on a measure space, u<=B almost everywhere, mass<=K W, and W<=C p almost everywhere; W and C are finite.
* **Objects:** Square of total u integral bounded by B K C times the p-weighted u integral, also on a restriction.
* **Proof detail:** Use the bounded amplitude and mass bound to control one integral factor, then integrate the pointwise weight lower bound and combine the factors.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Locally derived nonnegative amplitude/mass/weight estimate, not a named independence or covariance theorem; zero and infinite integral cases remain in ENNReal.
-/

/-! The actual finite contributor count controls nonnegative traffic before any
Fubini step. Extended-real integrals avoid assuming the weighted traffic finite. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Pointwise bounded per-edge traffic, an actual contributor count, and an
actual weight bound give the weighted traffic-square inequality. -/
theorem lintegral_sq_le_of_count_and_weight
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u p : X → ℝ≥0∞} {B K W C : ℝ≥0∞}
    (hW : W ≠ ∞) (hC : C ≠ ∞)
    (huB : ∀ᵐ x ∂μ, u x ≤ B)
    (hcount : μ univ ≤ K * W)
    (hweight : ∀ᵐ x ∂μ, W ≤ C * p x) :
    (∫⁻ x, u x ∂μ) ^ 2 ≤ B * K * C * ∫⁻ x, p x * u x ∂μ := by
  have hT : (∫⁻ x, u x ∂μ) ≤ B * μ univ := by
    exact (lintegral_mono_ae huB).trans_eq (lintegral_const B)
  have hWT : W * (∫⁻ x, u x ∂μ) ≤ C * ∫⁻ x, p x * u x ∂μ := by
    rw [← lintegral_const_mul' _ _ hW, ← lintegral_const_mul' _ _ hC]
    apply lintegral_mono_ae
    filter_upwards [hweight] with x hx
    calc
      W * u x ≤ (C * p x) * u x := by gcongr
      _ = _ := by rw [mul_assoc]
  calc
    _ = (∫⁻ x, u x ∂μ) * (∫⁻ x, u x ∂μ) := pow_two _
    _ ≤ (B * μ univ) * (∫⁻ x, u x ∂μ) := by gcongr
    _ ≤ (B * (K * W)) * (∫⁻ x, u x ∂μ) := by gcongr
    _ = (B * K) * (W * ∫⁻ x, u x ∂μ) := by ac_rfl
    _ ≤ (B * K) * (C * ∫⁻ x, p x * u x ∂μ) := by gcongr
    _ = _ := by ac_rfl

/-- The same bound applies directly to a measurable family of actual original
contributors, using its own restricted original measure. -/
theorem setLIntegral_sq_le_of_count_and_weight
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : Set X}
    {u p : X → ℝ≥0∞} {B K W C : ℝ≥0∞}
    (hW : W ≠ ∞) (hC : C ≠ ∞)
    (huB : ∀ᵐ x ∂μ.restrict S, u x ≤ B)
    (hcount : μ S ≤ K * W)
    (hweight : ∀ᵐ x ∂μ.restrict S, W ≤ C * p x) :
    (∫⁻ x in S, u x ∂μ) ^ 2 ≤ B * K * C * ∫⁻ x in S, p x * u x ∂μ := by
  apply lintegral_sq_le_of_count_and_weight hW hC huB _ hweight
  simpa only [Measure.restrict_apply_univ] using hcount

end OTSelector.Probability
