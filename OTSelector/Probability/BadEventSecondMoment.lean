import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
## Lemma skeleton

* **Conditions:** A measurable bad event and an integrable fourth moment.
* **Objects:** The event-restricted second moment.
* **Proof detail:** Apply Hölder to the indicator and the squared random variable, then use pointwise domination.

## Mathematical sources

* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.1, Theorem 1.6.3 (Hölder), p. 29.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37

**Relationship to the sources:** The finite-measure and normed-target variants are explicit formal generalizations of the textbook inequality.
-/

/-! # Actual second-moment control on a bad event from a fourth moment -/
open Set Function MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 500000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The fourth moment controls the actual indicator-restricted L2 norm,
without any independence between the count and its bad event. -/
theorem eLpNorm_two_indicator_le_four_mul_event
    {E : Type*} [NormedAddCommGroup E] {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) {A : Set Ω} (hA : MeasurableSet A) :
    eLpNorm (A.indicator f) 2 μ ≤ eLpNorm f 4 μ * (μ A) ^ (1 / 4 : ℝ) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hA]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := f) (μ := μ.restrict A) (p := 2) (q := 4) (by norm_num) hf.restrict
  norm_num only [ENNReal.toReal_ofNat, one_div, invOf_eq_inv,
    show (2 : ℝ)⁻¹ - (4 : ℝ)⁻¹ = 1 / 4 by norm_num,
    Measure.restrict_apply_univ] at h
  exact h.trans (by
    gcongr
    exact Measure.restrict_le_self)

/-- The actual mean-square contribution of an arbitrary measurable bad event
is bounded by the square roots of the original fourth moment and its probability. -/
theorem integrable_indicator_sq_and_integral_le_fourth
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω ↦ f ω ^ 4) μ)
    {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun ω ↦ (A.indicator f ω) ^ 2) μ ∧
      (∫ ω, (A.indicator f ω) ^ 2 ∂μ) ≤
        (∫ ω, f ω ^ 4 ∂μ) ^ (1 / 2 : ℝ) * (μ.real A) ^ (1 / 2 : ℝ) := by
  have hf2 : MemLp (fun ω ↦ f ω ^ 2) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hf.pow 2)).mpr
    simpa only [Pi.pow_apply, ← pow_mul] using h4
  have hg : MemLp (A.indicator (fun _ : Ω ↦ (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hA
  have hprod : MemLp (fun ω ↦ f ω ^ 2 * A.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ := hg.mul' hf2
  have heq : (fun ω ↦ (A.indicator f ω) ^ 2) =
      (fun ω ↦ f ω ^ 2 * A.indicator (fun _ ↦ (1 : ℝ)) ω) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  have hi : Integrable (fun ω ↦ (A.indicator f ω) ^ 2) μ := by
    rw [heq]
    exact memLp_one_iff_integrable.mp hprod
  refine ⟨hi, ?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (Eventually.of_forall (fun ω ↦ sq_nonneg (f ω)))
    (Eventually.of_forall (fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω))
    (by norm_num at hf2 ⊢; exact hf2) (by norm_num at hg ⊢; exact hg)
  rw [heq]
  have hgeq : (∫ ω, (A.indicator (fun _ : Ω ↦ (1 : ℝ)) ω) ^ 2 ∂μ) = μ.real A := by
    calc
      _ = ∫ ω, A.indicator (fun _ : Ω ↦ (1 : ℝ)) ω ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun ω ↦ by
          by_cases hω : ω ∈ A <;> simp [hω])
      _ = μ.real A := by rw [integral_indicator hA, setIntegral_const]; simp
  simpa only [Real.rpow_two, hgeq, ← pow_mul] using h

/-- A later selected count or error dominated by the same complete original
count inherits its bad-event second-moment estimate. -/
theorem integrable_indicator_sq_and_integral_le_of_domination
    {f N : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {A : Set Ω} (hA : MeasurableSet A)
    (hN : Integrable (fun ω ↦ (A.indicator N ω) ^ 2) μ)
    (hdom : ∀ᵐ ω ∂μ, ω ∈ A → |f ω| ≤ |N ω|) :
    Integrable (fun ω ↦ (A.indicator f ω) ^ 2) μ ∧
      (∫ ω, (A.indicator f ω) ^ 2 ∂μ) ≤ ∫ ω, (A.indicator N ω) ^ 2 ∂μ := by
  have hsq : ∀ᵐ ω ∂μ, (A.indicator f ω) ^ 2 ≤ (A.indicator N ω) ^ 2 := by
    filter_upwards [hdom] with ω hω
    by_cases hωA : ω ∈ A
    · simp only [Set.indicator_of_mem hωA]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f ω)) (hω hωA) 2
    · simp only [Set.indicator_of_notMem hωA, le_refl]
  have hi : Integrable (fun ω ↦ (A.indicator f ω) ^ 2) μ := by
    apply hN.mono' ((hf.indicator hA).pow 2)
    filter_upwards [hsq] with ω hω
    change ‖(A.indicator f ω) ^ 2‖ ≤ (A.indicator N ω) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  exact ⟨hi, integral_mono_ae hi hN hsq⟩

end OTSelector.Probability
