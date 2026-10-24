import OTSelector.Probability.PoissonMaskedCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Original count-weighted exceptional quadratic costs

The same original Poisson counts control any measurable selected bad event.
For dimensions greater than four, their square-root discrepancy is negligible
after the physical squared-distance normalization. No event/count independence
or exponential-tail callback is needed.
-/
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 800000

/-- A bad-event probability negligible on the physical quadratic scale remains
negligible after weighting by the actual two original Poisson counts. -/
theorem tendsto_masked_count_exception_cost_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ≥0 → Measure Ω) [∀ r, IsProbabilityMeasure (P r)]
    (N : ℝ≥0 → Ω → ℝ) (hN : ∀ r, Integrable (N r) (P r))
    (hN0 : ∀ r ω, 0 ≤ N r ω)
    (hdev : ∀ r, (∫ ω, |N r ω - 2 * (r : ℝ)| ∂P r) ≤ 2 * Real.sqrt (r : ℝ))
    (bad : ℝ≥0 → Set Ω) (hbad : ∀ r, MeasurableSet (bad r))
    {a : ℝ} (ha : a < 1 / 2)
    (hprob : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ a * (P r).real (bad r)) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ (a - 1) *
      ∫ ω, (bad r).indicator (N r) ω ∂P r) atTop (𝓝 0) := by
  have hcoe : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hdecay : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ (a - 1 / 2)) atTop (𝓝 0) := by
    have he : -(1 / 2 - a) = a - 1 / 2 := by ring
    simpa only [Function.comp_def, he] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp hcoe
  have hupper := (hprob.const_mul 2).add (hdecay.const_mul 2)
  simp only [mul_zero, zero_add] at hupper
  have hnonneg (r : ℝ≥0) : 0 ≤ (r : ℝ) ^ (a - 1) *
      ∫ ω, (bad r).indicator (N r) ω
        ∂P r := by
    apply mul_nonneg (Real.rpow_nonneg r.coe_nonneg _)
    apply integral_nonneg
    intro ω
    exact Set.indicator_nonneg
      (fun z _ ↦ hN0 r z) ω
  apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ hupper
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with r hr
  have hrR : 0 < (r : ℝ) := hr
  have hcount := (integral_indicator_le_center_mass_add_abs (P r) (hN r)
    (2 * (r : ℝ)) (bad r) (hbad r)).trans (add_le_add le_rfl (hdev r))
  have hmul := mul_le_mul_of_nonneg_left hcount (Real.rpow_nonneg r.coe_nonneg (a - 1))
  have hpow : (r : ℝ) ^ (a - 1) * (r : ℝ) = (r : ℝ) ^ a := by
    rw [← Real.rpow_add_one hrR.ne']
    congr 1
    ring
  have hsqrt : (r : ℝ) ^ (a - 1) * Real.sqrt (r : ℝ) =
      (r : ℝ) ^ (a - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hrR]
    congr 1
    ring
  calc
    _ ≤ (r : ℝ) ^ (a - 1) *
        (2 * (r : ℝ) * (P r).real (bad r) +
          2 * Real.sqrt (r : ℝ)) := hmul
    _ = 2 * ((r : ℝ) ^ a * (P r).real (bad r)) +
        2 * (r : ℝ) ^ (a - 1 / 2) := by
      calc
        _ = 2 * (((r : ℝ) ^ (a - 1) * (r : ℝ)) *
              (P r).real (bad r)) +
            2 * ((r : ℝ) ^ (a - 1) * Real.sqrt (r : ℝ)) := by ring
        _ = _ := by rw [hpow, hsqrt]

/-- The original two-cloud law supplies every first-moment input of the
shared selected-event cost estimate. -/
theorem tendsto_original_count_exception_cost_zero
    (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (bad : ℝ≥0 → Set (TwoMarkedCloudSpace q A B)) (hbad : ∀ r, MeasurableSet (bad r))
    {a : ℝ} (ha : a < 1 / 2)
    (hprob : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ a *
      (twoMarkedCloudLaw q A B α β r).real (bad r)) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ (a - 1) *
      ∫ ω, (bad r).indicator (fun z ↦ (mSourceCount z : ℝ) + (mTargetCount z : ℝ)) ω
        ∂twoMarkedCloudLaw q A B α β r) atTop (𝓝 0) := by
  apply tendsto_masked_count_exception_cost_zero
    (fun r ↦ twoMarkedCloudLaw q A B α β r)
    (fun _ z ↦ (mSourceCount z : ℝ) + (mTargetCount z : ℝ))
    (fun r ↦ (integrable_mSourceCount q α β r).add (integrable_mTargetCount q α β r))
    (fun _ _ ↦ add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ bad hbad ha hprob
  intro r
  have hs := ((integrable_mSourceCount q α β r).sub (integrable_const (r : ℝ))).abs
  have ht := ((integrable_mTargetCount q α β r).sub (integrable_const (r : ℝ))).abs
  calc
    _ ≤ ∫ z, |(mSourceCount z : ℝ) - (r : ℝ)| +
        |(mTargetCount z : ℝ) - (r : ℝ)| ∂twoMarkedCloudLaw q A B α β r := by
      apply integral_mono
        ((((integrable_mSourceCount q α β r).add (integrable_mTargetCount q α β r)).sub
          (integrable_const (2 * (r : ℝ)))).abs) (hs.add ht)
      intro z
      change |(mSourceCount z : ℝ) + (mTargetCount z : ℝ) - 2 * (r : ℝ)| ≤
        |(mSourceCount z : ℝ) - (r : ℝ)| + |(mTargetCount z : ℝ) - (r : ℝ)|
      have he : (mSourceCount z : ℝ) + (mTargetCount z : ℝ) - 2 * (r : ℝ) =
          ((mSourceCount z : ℝ) - (r : ℝ)) + ((mTargetCount z : ℝ) - (r : ℝ)) := by ring
      rw [he]
      exact abs_add_le _ _
    _ = (∫ z, |(mSourceCount z : ℝ) - (r : ℝ)| ∂twoMarkedCloudLaw q A B α β r) +
        (∫ z, |(mTargetCount z : ℝ) - (r : ℝ)| ∂twoMarkedCloudLaw q A B α β r) :=
      integral_add hs ht
    _ ≤ 2 * Real.sqrt (r : ℝ) := by
      linarith [integral_abs_mSourceCount_sub_le q α β r,
        integral_abs_mTargetCount_sub_le q α β r]

/-- The original finite comparator's squared spatial scale is admissible in
every effective dimension at least five. -/
theorem tendsto_original_quadratic_count_exception_cost_zero
    (q : ℕ) (hq : 4 < q)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (bad : ℝ≥0 → Set (TwoMarkedCloudSpace q A B)) (hbad : ∀ r, MeasurableSet (bad r))
    (hprob : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ (2 / (q : ℝ)) *
      (twoMarkedCloudLaw q A B α β r).real (bad r)) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ (2 / (q : ℝ) - 1) *
      ∫ ω, (bad r).indicator (fun z ↦ (mSourceCount z : ℝ) + (mTargetCount z : ℝ)) ω
        ∂twoMarkedCloudLaw q A B α β r) atTop (𝓝 0) := by
  apply tendsto_original_count_exception_cost_zero q α β bad hbad ?_ hprob
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_trans (by norm_num) hqR
  rw [div_lt_iff₀ hq0]
  linarith

end OTSelector.Probability
