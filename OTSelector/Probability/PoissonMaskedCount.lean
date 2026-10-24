import OTSelector.Probability.MarkedDePoissonization
import Mathlib.MeasureTheory.Measure.Real

/-!
# Actual Poisson counts on arbitrary selected exceptional events

The event may depend on both entire original clouds.  Original count deviations
control the count-weighted exceptional cost without any event/count independence.
-/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- A centered first moment bounds the mass of any measurable selected event. -/
theorem integral_indicator_le_center_mass_add_abs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : Ω → ℝ} (hN : Integrable N P) (r : ℝ) (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω, E.indicator N ω ∂P) ≤ r * P.real E + ∫ ω, |N ω - r| ∂P := by
  have hD : Integrable (fun ω ↦ |N ω - r|) P := (hN.sub (integrable_const r)).abs
  calc
    _ ≤ ∫ ω, E.indicator (fun _ ↦ r) ω + |N ω - r| ∂P := by
      apply integral_mono (hN.indicator hE) (((integrable_const r).indicator hE).add hD)
      intro ω
      by_cases hω : ω ∈ E
      · simp only [Pi.add_apply, indicator_of_mem hω]
        linarith [le_abs_self (N ω - r)]
      · simp only [Pi.add_apply, indicator_of_notMem hω, zero_add]
        exact abs_nonneg _
    _ = _ := by
      rw [integral_add ((integrable_const r).indicator hE) hD, integral_indicator_const _ hE]
      simp only [smul_eq_mul, mul_comm]

/-- Both actual original counts on a selected event cost only their true volume
mass plus the original square-root count discrepancy. -/
theorem integral_indicator_original_counts_le
    (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (E : Set (TwoMarkedCloudSpace q A B)) (hE : MeasurableSet E) :
    (∫ ω, E.indicator (fun z ↦ (mSourceCount z : ℝ) + (mTargetCount z : ℝ)) ω
      ∂twoMarkedCloudLaw q A B α β r) ≤
      2 * (r : ℝ) * (twoMarkedCloudLaw q A B α β r).real E + 2 * Real.sqrt (r : ℝ) := by
  let P := twoMarkedCloudLaw q A B α β r
  have hs := integral_indicator_le_center_mass_add_abs P
    (integrable_mSourceCount q α β r) (r : ℝ) E hE
  have ht := integral_indicator_le_center_mass_add_abs P
    (integrable_mTargetCount q α β r) (r : ℝ) E hE
  have hsb := integral_abs_mSourceCount_sub_le q α β r
  have htb := integral_abs_mTargetCount_sub_le q α β r
  have heq : E.indicator (fun z ↦ (mSourceCount z : ℝ) + (mTargetCount z : ℝ)) =
      E.indicator (fun z ↦ (mSourceCount z : ℝ)) +
        E.indicator (fun z ↦ (mTargetCount z : ℝ)) := by
    exact Set.indicator_add _ _ _
  rw [heq]
  simp only [Pi.add_apply]
  rw [integral_add ((integrable_mSourceCount q α β r).indicator hE)
    ((integrable_mTargetCount q α β r).indicator hE)]
  change _ ≤ 2 * (r : ℝ) * P.real E + 2 * Real.sqrt (r : ℝ)
  linarith

/-- A square-root event probability bound remains square-root after weighting
by the actual unchanged original random counts. -/
theorem integral_indicator_original_counts_le_sqrtRate
    (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (hr : 0 < r) (E : Set (TwoMarkedCloudSpace q A B)) (hE : MeasurableSet E)
    (C : ℝ) (hprob : (twoMarkedCloudLaw q A B α β r).real E ≤ C / Real.sqrt (r : ℝ)) :
    (∫ ω, E.indicator (fun z ↦ (mSourceCount z : ℝ) + (mTargetCount z : ℝ)) ω
      ∂twoMarkedCloudLaw q A B α β r) ≤ (2 * C + 2) * Real.sqrt (r : ℝ) := by
  have hrR : 0 < (r : ℝ) := hr
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrR
  calc
    _ ≤ 2 * (r : ℝ) * (twoMarkedCloudLaw q A B α β r).real E +
        2 * Real.sqrt (r : ℝ) := integral_indicator_original_counts_le q α β r E hE
    _ ≤ 2 * (r : ℝ) * (C / Real.sqrt (r : ℝ)) + 2 * Real.sqrt (r : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hprob
        (show 0 ≤ 2 * (r : ℝ) from mul_nonneg (by norm_num) r.coe_nonneg)) le_rfl
    _ = _ := by
      have heq := Real.sq_sqrt hrR.le
      have hC := congrArg (fun x : ℝ ↦ x * C) heq
      field_simp
      nlinarith [hC]

/-- Any continuum bad event has a measurable envelope with the same original
outer probability and the same actual count-weighted square-root bound. -/
theorem exists_measurable_original_count_exception_envelope
    (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (hr : 0 < r) (bad : Set (TwoMarkedCloudSpace q A B))
    (C : ℝ) (hprob : (twoMarkedCloudLaw q A B α β r).real bad ≤ C / Real.sqrt (r : ℝ)) :
    ∃ E : Set (TwoMarkedCloudSpace q A B), MeasurableSet E ∧ bad ⊆ E ∧
      (twoMarkedCloudLaw q A B α β r).real E =
        (twoMarkedCloudLaw q A B α β r).real bad ∧
      (∫ ω, E.indicator (fun z ↦ (mSourceCount z : ℝ) + (mTargetCount z : ℝ)) ω
        ∂twoMarkedCloudLaw q A B α β r) ≤ (2 * C + 2) * Real.sqrt (r : ℝ) := by
  let P := twoMarkedCloudLaw q A B α β r
  let E := toMeasurable P bad
  have hE : MeasurableSet E := measurableSet_toMeasurable P bad
  have heq : P.real E = P.real bad := congrArg ENNReal.toReal (measure_toMeasurable bad)
  refine ⟨E, hE, subset_toMeasurable P bad, heq, ?_⟩
  apply integral_indicator_original_counts_le_sqrtRate q α β r hr E hE C
  exact heq.trans_le hprob

end OTSelector.Probability
