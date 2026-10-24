import OTSelector.Probability.MarkedPoissonCube
import Mathlib.Probability.ProductMeasure

/-! Original mark laws simultaneously control every used finite cloud prefix. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem map_markedPoissonLaw_mark (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (r : ℝ≥0) (i : ℕ) :
    (markedPoissonLaw q A α r).map (fun z ↦ (z.2 i).2) = α := by
  let _inst : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := (measurePreserving_snd (μ := cubeMeasure (Fin q) 1) (ν := α)).comp
    ((measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α) i).comp
      (measurePreserving_snd (μ := poissonMeasure r) (ν := markedSeqLaw q A α)))
  exact h.map_eq

theorem map_twoMarkedCloudLaw_markPair (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (i j : ℕ) :
    (twoMarkedCloudLaw q A B α β r).map
      (fun ξ ↦ (mSourceMark ξ i, mTargetMark ξ j)) = α.prod β := by
  change ((markedPoissonLaw q A α r).prod (markedPoissonLaw q B β r)).map
    (Prod.map (fun z ↦ (z.2 i).2) (fun z ↦ (z.2 j).2)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    map_markedPoissonLaw_mark, map_markedPoissonLaw_mark]

/-- Every original almost-everywhere mark property holds at all source indices
on one common full-probability event. -/
theorem ae_all_mSourceMark (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {P : A → Prop} (hP : ∀ᵐ a ∂α, P a) :
    ∀ᵐ ξ ∂twoMarkedCloudLaw q A B α β r, ∀ i : ℕ, P (mSourceMark ξ i) := by
  rw [ae_all_iff]
  intro i
  have hmap : (twoMarkedCloudLaw q A B α β r).map (fun ξ ↦ mSourceMark ξ i) = α := by
    change ((markedPoissonLaw q A α r).prod (markedPoissonLaw q B β r)).map
      ((fun z ↦ (z.2 i).2) ∘ Prod.fst) = _
    rw [← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul, map_markedPoissonLaw_mark]
  exact ae_of_ae_map (measurable_mSourceMark q i).aemeasurable (by rw [hmap]; exact hP)

/-- Every original product-almost-everywhere pair property holds at all source
and target index pairs simultaneously; the original colors remain independent. -/
theorem ae_all_mMarkPair (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {P : A → B → Prop} (hP : ∀ᵐ p ∂α.prod β, P p.1 p.2) :
    ∀ᵐ ξ ∂twoMarkedCloudLaw q A B α β r,
      ∀ i j : ℕ, P (mSourceMark ξ i) (mTargetMark ξ j) := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  exact ae_of_ae_map (μ := twoMarkedCloudLaw q A B α β r)
    (p := fun p : A × B ↦ P p.1 p.2)
    (((measurable_mSourceMark q i).prodMk (measurable_mTargetMark q j)).aemeasurable)
    (by rw [map_twoMarkedCloudLaw_markPair]; exact hP)

end OTSelector.Probability
