import OTSelector.Probability.FractionalCountMoment
import OTSelector.Probability.MarkedPoissonCube

/-! The actual marked Poisson reserve count supplies the genuine rate parameter
for fractional moments of itself and every original retained subcount. -/

open MeasureTheory
open OTSelector.Probability
open scoped NNReal

noncomputable section
namespace OTSelector.Reconstruction

private theorem markedPoisson_originalCount_mean
    {A : Type*} [MeasurableSpace A] (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (a : ℝ≥0) :
    (∫ ω : MarkedCloudSpace q A, (ω.1 : ℝ) ∂markedPoissonLaw q A α a) = (a : ℝ) := by
  rw [markedPoissonLaw, integral_fun_fst]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact ProbabilityTheory.integral_id_poissonMeasure a

/-- The actual original marked Poisson reserve count has fractional moment
at most its true intensity to that power, including zero intensity. -/
theorem markedPoisson_count_rpow_integrable_and_integral_le
    {A : Type*} [MeasurableSpace A] (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (a : ℝ≥0)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Integrable (fun ω : MarkedCloudSpace q A ↦ (ω.1 : ℝ) ^ r)
      (markedPoissonLaw q A α a) ∧
    (∫ ω : MarkedCloudSpace q A, (ω.1 : ℝ) ^ r ∂markedPoissonLaw q A α a) ≤ (a : ℝ) ^ r := by
  have hNI : Integrable (fun ω : MarkedCloudSpace q A ↦ (ω.1 : ℝ))
      (markedPoissonLaw q A α a) := (ProbabilityTheory.integrable_id_poissonMeasure a).comp_fst _
  simpa only [markedPoisson_originalCount_mean] using
    count_rpow_integrable_and_integral_le (markedPoissonLaw q A α a)
      Prod.fst measurable_fst hNI hr₀ hr₁

/-- Any measurable original retained reserve count bounded by the actual
Poisson count inherits the genuine intensity bound without an input rate callback. -/
theorem markedPoisson_retainedCount_rpow_integrable_and_integral_le
    {A : Type*} [MeasurableSpace A] (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (a : ℝ≥0)
    (K : MarkedCloudSpace q A → ℕ) (hK : Measurable K) (hle : ∀ ω, K ω ≤ ω.1)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Integrable (fun ω ↦ (K ω : ℝ) ^ r) (markedPoissonLaw q A α a) ∧
    (∫ ω, (K ω : ℝ) ^ r ∂markedPoissonLaw q A α a) ≤ (a : ℝ) ^ r := by
  have hNI : Integrable (fun ω : MarkedCloudSpace q A ↦ (ω.1 : ℝ))
      (markedPoissonLaw q A α a) := (ProbabilityTheory.integrable_id_poissonMeasure a).comp_fst _
  simpa only [markedPoisson_originalCount_mean] using
    retainedCount_rpow_integrable_and_integral_le (markedPoissonLaw q A α a)
      Prod.fst K measurable_fst hK hNI hle hr₀ hr₁

/-- At actual zero reserve intensity, every retained fractional count moment
vanishes exactly, without a separate nonzero-intensity assumption. -/
theorem markedPoisson_retainedCount_rpow_integral_zero
    {A : Type*} [MeasurableSpace A] (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α]
    (K : MarkedCloudSpace q A → ℕ) (hK : Measurable K) (hle : ∀ ω, K ω ≤ ω.1)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    (∫ ω, (K ω : ℝ) ^ r ∂markedPoissonLaw q A α 0) = 0 := by
  have h := (markedPoisson_retainedCount_rpow_integrable_and_integral_le
    q α 0 K hK hle hr₀ hr₁).2
  simp only [NNReal.coe_zero, Real.zero_rpow hr₀.ne'] at h
  exact le_antisymm h (integral_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)

end OTSelector.Reconstruction
