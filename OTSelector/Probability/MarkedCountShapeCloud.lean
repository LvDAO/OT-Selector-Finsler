import OTSelector.Probability.RandomPrefixMoments
import OTSelector.Probability.MarkedShapeCloud

/-! Original marked prefix laws with arbitrary independent count distribution.
The binomial mean and all original spatial deletion counts remain exact. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Read the actual original count and only that prefix of the original iid
marked point sequence. -/
def markedCountLaw (q : ℕ) {A : Type*} [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (κ : Measure ℕ) :
    Measure (MarkedCloudSpace q A) := κ.prod (markedSeqLaw q A α)

instance isProbabilityMeasure_markedCountLaw (q : ℕ) {A : Type*} [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (κ : Measure ℕ) [IsProbabilityMeasure κ] :
    IsProbabilityMeasure (markedCountLaw q α κ) := by unfold markedCountLaw; infer_instance

/-- Two original independent colors with their original common count law. -/
def twoMarkedCountLaw (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (κ : Measure ℕ) : Measure (TwoMarkedCloudSpace q A B) :=
  (markedCountLaw q α κ).prod (markedCountLaw q β κ)

instance isProbabilityMeasure_twoMarkedCountLaw (q : ℕ) {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (κ : Measure ℕ) [IsProbabilityMeasure κ] :
    IsProbabilityMeasure (twoMarkedCountLaw q α β κ) := by unfold twoMarkedCountLaw; infer_instance

/-- A positive Poisson law has no nonempty null set of counts. This transfers
only almost-everywhere point carriers, never expectations or count laws. -/
theorem natMeasure_absolutelyContinuous_poisson_one (κ : Measure ℕ) :
    κ ≪ poissonMeasure 1 := by
  intro S hS
  have he : S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hpos : 0 < poissonMeasure 1 {n} := by rw [poissonMeasure_singleton]; positivity
    have hle : poissonMeasure 1 {n} ≤ poissonMeasure 1 S :=
      measure_mono (singleton_subset_iff.mpr hn)
    exact (not_le_of_gt hpos) (hS ▸ hle)
  simp [he]

theorem markedCountLaw_absolutelyContinuous_poisson_one (q : ℕ) {A : Type*}
    [MeasurableSpace A] (α : Measure A) [IsProbabilityMeasure α] (κ : Measure ℕ) :
    markedCountLaw q α κ ≪ markedPoissonLaw q A α 1 :=
  (natMeasure_absolutelyContinuous_poisson_one κ).prod Measure.AbsolutelyContinuous.rfl

theorem twoMarkedCountLaw_absolutelyContinuous_poisson_one (q : ℕ) {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (κ : Measure ℕ) : twoMarkedCountLaw q α β κ ≪ twoMarkedCloudLaw q A B α β 1 :=
  (markedCountLaw_absolutelyContinuous_poisson_one q α κ).prod
    (markedCountLaw_absolutelyContinuous_poisson_one q β κ)

/-- Actual shape deletion counts are integrable for any original finite mean. -/
theorem integrable_markedCount_shape_missing (q : ℕ) {A : Type*} [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    Integrable (fun z : MarkedCloudSpace q A ↦ ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ))
      (markedCountLaw q α κ) := by
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  simpa only [markedCountLaw, markedSeqLaw, shapeCloud_missing_count] using
    integrable_randomPrefixCount ((cubeMeasure (Fin q) 1).prod α) κ hκ
      (hS.compl.preimage measurable_fst)

/-- Exact original finite-count filling/deletion first moment. -/
theorem integral_markedCount_shape_missing (q : ℕ) {A : Type*} [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (∫ z : MarkedCloudSpace q A, ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ)
      ∂markedCountLaw q α κ) =
      (∫ n : ℕ, (n : ℝ) ∂κ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := integral_randomPrefixCount ((cubeMeasure (Fin q) 1).prod α) κ hκ
    (hS.compl.preimage measurable_fst)
  have heval : ((cubeMeasure (Fin q) 1).prod α) (Prod.fst ⁻¹' Sᶜ) =
      (cubeMeasure (Fin q) 1) Sᶜ := by
    rw [show Prod.fst ⁻¹' Sᶜ = Sᶜ ×ˢ (univ : Set A) by ext p; simp,
      Measure.prod_prod, measure_univ, mul_one]
  simpa only [markedCountLaw, markedSeqLaw, shapeCloud_missing_count, heval] using h

/-- In particular, the original binomial deleted-point mean is N*p*hole. -/
theorem integral_binomial_marked_shape_missing (q : ℕ) {A : Type*} [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (N : ℕ) (p : I)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (∫ z : MarkedCloudSpace q A, ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ)
      ∂markedCountLaw q α (ProbabilityTheory.binomial N p)) =
      ((N : ℝ) * (p : ℝ)) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
  rw [integral_markedCount_shape_missing q α _ (integrable_binomial _) hS,
    integral_binomial_id]

end OTSelector.Probability
