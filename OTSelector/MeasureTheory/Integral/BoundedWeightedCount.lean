import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
## Lemma skeleton

* **Conditions:** A finite measured carrier, a measurable nonnegative u<=B, mass<=K W, W<=C p almost everywhere, and integrable p u; B,K are nonnegative.
* **Objects:** Integrability of u and the real weighted count inequality, globally or on a finite-mass restriction.
* **Proof detail:** Use boundedness for L1, integrate the pointwise weight inequality against u, and multiply by the amplitude/mass estimate, separating degenerate sign/zero cases.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Real finite-integral version of the locally derived count-weight estimate; the statement does not separately assume C or W positive.
-/

/-!
# The weighted good-event traffic bound from an actual finite count

All quantities belong to the same original measure. The field amplitude may
control the actual count and the pointwise momentum without independence.
-/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 1800000
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- A bounded nonnegative per-edge traffic has square bounded by its original
finite count and the weighted momentum traffic integral. -/
theorem integral_sq_le_of_count_and_pointwise_weight
    {u p : X → ℝ} (hu : AEStronglyMeasurable u μ)
    {B K W C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hu0 : ∀ᵐ x ∂μ, 0 ≤ u x) (huB : ∀ᵐ x ∂μ, u x ≤ B)
    (hcount : μ.real Set.univ ≤ K * W)
    (hweight : ∀ᵐ x ∂μ, W ≤ C * p x)
    (hpu : Integrable (fun x ↦ p x * u x) μ) :
    Integrable u μ ∧ (∫ x, u x ∂μ) ^ 2 ≤ B * K * C * ∫ x, p x * u x ∂μ := by
  have huI : Integrable u μ := (integrable_const B).mono' hu (by
    filter_upwards [hu0, huB] with x hx0 hxB
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hxB)
  have hT0 : 0 ≤ ∫ x, u x ∂μ := integral_nonneg_of_ae hu0
  have hT : ∫ x, u x ∂μ ≤ B * μ.real Set.univ := by
    have h := integral_mono_ae huI (integrable_const B) huB
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  have hWT : W * (∫ x, u x ∂μ) ≤ C * ∫ x, p x * u x ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono_ae (huI.const_mul W) (hpu.const_mul C)
    filter_upwards [hu0, hweight] with x hx0 hxW
    have h := mul_le_mul_of_nonneg_right hxW hx0
    simpa only [mul_assoc] using h
  refine ⟨huI, ?_⟩
  calc
    _ ≤ (B * μ.real Set.univ) * (∫ x, u x ∂μ) := by nlinarith
    _ ≤ (B * (K * W)) * (∫ x, u x ∂μ) := by gcongr
    _ = (B * K) * (W * ∫ x, u x ∂μ) := by ring
    _ ≤ (B * K) * (C * ∫ x, p x * u x ∂μ) :=
      mul_le_mul_of_nonneg_left hWT (mul_nonneg hB hK)
    _ = _ := by ring

/-- The same weighted traffic estimate uses a literal measurable edge family inside
an arbitrary original measure, requiring only its actual finite count. -/
theorem setIntegral_sq_le_of_count_and_pointwise_weight
    {ν : Measure X} {V : Set X} (hfinite : ν V < ∞)
    {u p : X → ℝ} (hu : AEStronglyMeasurable u (ν.restrict V))
    {B K W C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hu0 : ∀ᵐ x ∂ν.restrict V, 0 ≤ u x) (huB : ∀ᵐ x ∂ν.restrict V, u x ≤ B)
    (hcount : ν.real V ≤ K * W)
    (hweight : ∀ᵐ x ∂ν.restrict V, W ≤ C * p x)
    (hpu : IntegrableOn (fun x ↦ p x * u x) V ν) :
    IntegrableOn u V ν ∧
      (∫ x in V, u x ∂ν) ^ 2 ≤ B * K * C * ∫ x in V, p x * u x ∂ν := by
  have : IsFiniteMeasure (ν.restrict V) := ⟨by simpa using hfinite⟩
  apply integral_sq_le_of_count_and_pointwise_weight hu hB hK hu0 huB _ hweight hpu
  simpa only [Measure.real, Measure.restrict_apply_univ] using hcount

end OTSelector.Probability
