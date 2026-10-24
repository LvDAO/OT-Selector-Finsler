import OTSelector.Probability.PoissonPrefixMoments
import OTSelector.Probability.BinomialDeviation

/-! Original iid prefix moments with any independent integrable count law.
Binomial counts are retained exactly, including varying sample and shape data. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X]

/-- A bounded original point test is integrable up to any independent original
count with a finite first moment. -/
theorem integrable_randomPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable (poissonPrefixSum f) (κ.prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  refine ((hκ.comp_fst (Measure.infinitePi (fun _ : ℕ ↦ ν))).mul_const B).mono'
    (measurable_poissonPrefixSum hf).aestronglyMeasurable ?_
  filter_upwards with z
  simpa only [Real.norm_eq_abs] using abs_poissonPrefixSum_le hB z

/-- Its exact expectation uses the original count mean and original point law;
no thinning or limiting count distribution is substituted. -/
theorem integral_randomPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (∫ z, poissonPrefixSum f z ∂κ.prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) =
      (∫ n : ℕ, (n : ℝ) ∂κ) * ∫ x, f x ∂ν := by
  have hfi : Integrable f ν := (integrable_const B).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hB x)
  have hterm (i : ℕ) : Integrable (fun x : ℕ → X ↦ f (x i))
      (Measure.infinitePi (fun _ : ℕ ↦ ν)) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ ν) i).integrable_comp_of_integrable hfi
  have hmean (i : ℕ) : (∫ x : ℕ → X, f (x i) ∂Measure.infinitePi (fun _ : ℕ ↦ ν)) =
      ∫ x, f x ∂ν := by
    calc
      _ = ∫ x, f x ∂((Measure.infinitePi (fun _ : ℕ ↦ ν)).map
          (fun x : ℕ → X ↦ x i)) :=
        (integral_map_of_stronglyMeasurable (measurable_pi_apply i) hf.stronglyMeasurable).symm
      _ = _ := by rw [Measure.infinitePi_map_eval]
  have hfixed (n : ℕ) : (∫ x : ℕ → X, ∑ i : Fin n, f (x i)
      ∂Measure.infinitePi (fun _ : ℕ ↦ ν)) = (n : ℝ) * ∫ x, f x ∂ν := by
    rw [integral_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hterm (i : ℕ))]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_prod _ (integrable_randomPrefixSum ν κ hκ hf hB)]
  change (∫ n, ∫ x, ∑ i : Fin n, f (x i)
    ∂Measure.infinitePi (fun _ : ℕ ↦ ν) ∂κ) = _
  simp_rw [hfixed]
  rw [integral_mul_const]

/-- The actual used prefix count in any measurable set is integrable. -/
theorem integrable_randomPrefixCount
    (ν : Measure X) [IsProbabilityMeasure ν] (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ) {S : Set X} (hS : MeasurableSet S) :
    Integrable (fun z ↦ (poissonPrefixCount S z : ℝ))
      (κ.prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  simp_rw [poissonPrefixCount_cast]
  exact integrable_randomPrefixSum ν κ hκ (measurable_const.indicator hS)
    (B := 1) (fun x ↦ by by_cases hx : x ∈ S <;> simp [hx])

/-- The expected number of omitted original points equals the original count
mean times the original hole mass, for every shape at every finite sample size. -/
theorem integral_randomPrefixCount
    (ν : Measure X) [IsProbabilityMeasure ν] (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ) {S : Set X} (hS : MeasurableSet S) :
    (∫ z, (poissonPrefixCount S z : ℝ) ∂κ.prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) =
      (∫ n : ℕ, (n : ℝ) ∂κ) * (ν S).toReal := by
  simp_rw [poissonPrefixCount_cast]
  rw [integral_randomPrefixSum ν κ hκ (measurable_const.indicator hS)
    (B := 1) (fun x ↦ by by_cases hx : x ∈ S <;> simp [hx])]
  simp [integral_indicator hS, measureReal_def]

/-- In the actual binomial experiment the deleted-point mean is exactly
N*p times the original spatial hole probability. -/
theorem integral_binomialPrefixCount (ν : Measure X) [IsProbabilityMeasure ν]
    (N : ℕ) (p : I) {S : Set X} (hS : MeasurableSet S) :
    (∫ z, (poissonPrefixCount S z : ℝ)
      ∂(ProbabilityTheory.binomial N p).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) =
      ((N : ℝ) * (p : ℝ)) * (ν S).toReal := by
  rw [integral_randomPrefixCount ν _ (integrable_binomial _), integral_binomial_id]
  exact hS

end OTSelector.Probability
