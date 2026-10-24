import OTSelector.Probability.PoissonBlockSetCounts
import OTSelector.Probability.PoissonCountDiscrepancy
import OTSelector.Probability.MarkedPoissonCube

/-! Genuine fixed-mark block counts of the original reserve clouds have their
thinned Poisson laws and the exact square-root discrepancy bound. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Count only original observed reserve indices whose actual mark belongs to S. -/
def originalReserveObservedBlockCount (S : Set A) (z : MarkedCloudSpace q A) : ℕ :=
  blockSetCount (Prod.snd ⁻¹' S) ⟨z.1, fun i ↦ z.2 i⟩

private theorem measurable_reservePrefix : Measurable
    (fun z : MarkedCloudSpace q A ↦ (⟨z.1, fun i ↦ z.2 i⟩ : BlockData ((Fin q → ℝ) × A))) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_sigma_mk n).comp
    (measurable_pi_lambda _ fun i : Fin n ↦ measurable_pi_apply (i : ℕ))

theorem measurable_originalReserveObservedBlockCount {S : Set A} (hS : MeasurableSet S) :
    Measurable (originalReserveObservedBlockCount (q := q) S) :=
  (measurable_blockSetCount (hS.preimage measurable_snd)).comp measurable_reservePrefix

/-- The literal marked reserve count has its true thinned Poisson law, including
zero rates and null blocks. No selected-cloud law is assumed. -/
theorem hasLaw_originalReserveObservedBlockCount_poisson
    (α : Measure A) [IsProbabilityMeasure α] (rate : ℝ≥0)
    {S : Set A} (hS : MeasurableSet S) :
    HasLaw (originalReserveObservedBlockCount (q := q) S)
      (poissonMeasure (rate * (α S).toNNReal)) (markedPoissonLaw q A α rate) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  let law := (cubeMeasure (Fin q) 1).prod α
  have hmass : restrictionWeight law (Prod.snd ⁻¹' S) = (α S).toNNReal := by
    unfold restrictionWeight law
    congr 1
    rw [← Measure.map_apply measurable_snd hS, Measure.map_snd_prod, measure_univ, one_smul]
  refine ⟨(measurable_originalReserveObservedBlockCount hS).aemeasurable, ?_⟩
  change (((poissonMeasure rate).prod (Measure.infinitePi (fun _ : ℕ ↦ law))).map
    (blockSetCount (Prod.snd ⁻¹' S) ∘ fun z ↦ ⟨z.1, fun i ↦ z.2 i⟩)) = _
  rw [← Measure.map_map (measurable_blockSetCount (hS.preimage measurable_snd))
    measurable_reservePrefix, ← blockDataLaw_eq_map_cloud]
  rw [(hasLaw_blockSetCount_poisson law rate (hS.preimage measurable_snd)).map_eq, hmass]

/-- The two original reserve block counts are genuinely independent Poisson
counts with their own actual masses. -/
theorem hasLaw_originalReserveObservedBlockCount_pair
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (rate : ℝ≥0) {S : Set A} {T : Set B} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    HasLaw (Prod.map (originalReserveObservedBlockCount (q := q) S) (originalReserveObservedBlockCount T))
      ((poissonMeasure (rate * (α S).toNNReal)).prod
        (poissonMeasure (rate * (β T).toNNReal))) (twoMarkedCloudLaw q A B α β rate) := by
  refine ⟨((measurable_originalReserveObservedBlockCount hS).prodMap
    (measurable_originalReserveObservedBlockCount hT)).aemeasurable, ?_⟩
  rw [twoMarkedCloudLaw, ← Measure.map_prod_map _ _
    (measurable_originalReserveObservedBlockCount hS) (measurable_originalReserveObservedBlockCount hT),
    (hasLaw_originalReserveObservedBlockCount_poisson α rate hS).map_eq,
    (hasLaw_originalReserveObservedBlockCount_poisson β rate hT).map_eq]

/-- Equal actual block masses give the sharp square-root discrepancy rate for
the same two original reserve prefixes. The L2 Poisson estimate is internal. -/
theorem originalReserveObservedBlockCount_abs_sub_integrable_and_integral_le
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (rate : ℝ≥0) {S : Set A} {T : Set B} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hbal : α S = β T) :
    Integrable (fun z ↦ |(originalReserveObservedBlockCount (q := q) S z.1 : ℝ) -
      (originalReserveObservedBlockCount T z.2 : ℝ)|) (twoMarkedCloudLaw q A B α β rate) ∧
    (∫ z, |(originalReserveObservedBlockCount (q := q) S z.1 : ℝ) -
      (originalReserveObservedBlockCount T z.2 : ℝ)| ∂twoMarkedCloudLaw q A B α β rate) ≤
        Real.sqrt (2 * (rate : ℝ) * α.real S) := by
  let a := rate * (α S).toNNReal
  have hlaw := hasLaw_originalReserveObservedBlockCount_pair (q := q) α β rate hS hT
  rw [← hbal] at hlaw
  have hm : MeasurePreserving
      (Prod.map (originalReserveObservedBlockCount (q := q) S) (originalReserveObservedBlockCount T))
      (twoMarkedCloudLaw q A B α β rate) ((poissonMeasure a).prod (poissonMeasure a)) :=
    ⟨(measurable_originalReserveObservedBlockCount hS).prodMap (measurable_originalReserveObservedBlockCount hT), hlaw.map_eq⟩
  have hI : Integrable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|)
      ((poissonMeasure a).prod (poissonMeasure a)) :=
    (((integrable_id_poissonMeasure a).comp_fst _).sub
      ((integrable_id_poissonMeasure a).comp_snd _)).abs
  have hf : Measurable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|) := by fun_prop
  refine ⟨hm.integrable_comp_of_integrable hI, ?_⟩
  have heq := hlaw.integral_comp hf.aestronglyMeasurable
  change (∫ z, |(originalReserveObservedBlockCount (q := q) S z.1 : ℝ) -
    (originalReserveObservedBlockCount T z.2 : ℝ)| ∂twoMarkedCloudLaw q A B α β rate) = _ at heq
  rw [heq]
  convert integral_abs_sub_poissonPair_le a using 1
  simp only [a, NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, measureReal_def]
  congr 1
  ring

end OTSelector.Probability
