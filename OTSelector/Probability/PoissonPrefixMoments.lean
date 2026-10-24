import OTSelector.Probability.MarkedPoissonCube
import Mathlib.MeasureTheory.Integral.Prod

/-! Bounded finite-prefix observables of the original Poissonized iid sequence. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [MeasurableSpace X]

/-- Sum a test over the actual used prefix, leaving all unused points unread. -/
def poissonPrefixSum (f : X → ℝ) (z : ℕ × (ℕ → X)) : ℝ :=
  ∑ i : Fin z.1, f (z.2 i)

theorem measurable_poissonPrefixSum {f : X → ℝ} (hf : Measurable f) :
    Measurable (poissonPrefixSum f) := by
  intro S hS
  have hpre : poissonPrefixSum f ⁻¹' S =
      ⋃ n : ℕ, {z : ℕ × (ℕ → X) | z.1 = n} ∩
        (fun z ↦ ∑ i : Fin n, f (z.2 i)) ⁻¹' S := by
    ext z
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨z.1, rfl, h⟩
    · rintro ⟨n, hn, h⟩
      subst n
      exact h
  rw [hpre]
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_eq_fun measurable_fst measurable_const).inter
    ((Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hf.comp
      ((measurable_pi_apply (i : ℕ)).comp measurable_snd))) hS)

omit [MeasurableSpace X] in
theorem abs_poissonPrefixSum_le {f : X → ℝ} {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (z : ℕ × (ℕ → X)) :
    |poissonPrefixSum f z| ≤ (z.1 : ℝ) * B := by
  calc
    _ ≤ ∑ i : Fin z.1, |f (z.2 i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin z.1, B := Finset.sum_le_sum fun i _ ↦ hB _
    _ = _ := by simp

theorem integrable_poissonPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable (poissonPrefixSum f)
      ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  refine (((integrable_id_poissonMeasure r).comp_fst
    (Measure.infinitePi (fun _ : ℕ ↦ ν))).mul_const B).mono'
      (measurable_poissonPrefixSum hf).aestronglyMeasurable ?_
  filter_upwards with z
  simpa only [Real.norm_eq_abs] using abs_poissonPrefixSum_le hB z

/-- The exact first moment is the original count mean times the original point
mean. Boundedness supplies integrability, with no filtered-cloud law assumed. -/
theorem integral_poissonPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (∫ z, poissonPrefixSum f z
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
      (r : ℝ) * ∫ x, f x ∂ν := by
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
        (integral_map_of_stronglyMeasurable (measurable_pi_apply i)
          hf.stronglyMeasurable).symm
      _ = _ := by rw [Measure.infinitePi_map_eval]
  have hfixed (n : ℕ) :
      (∫ x : ℕ → X, ∑ i : Fin n, f (x i) ∂Measure.infinitePi (fun _ : ℕ ↦ ν)) =
      (n : ℝ) * ∫ x, f x ∂ν := by
    rw [integral_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hterm (i : ℕ))]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_prod _ (integrable_poissonPrefixSum ν r hf hB)]
  change (∫ n, ∫ x, ∑ i : Fin n, f (x i) ∂Measure.infinitePi (fun _ : ℕ ↦ ν)
    ∂poissonMeasure r) = _
  simp_rw [hfixed]
  rw [integral_mul_const, integral_id_poissonMeasure]

/-- The actual number of points in a measurable region of the used prefix. -/
def poissonPrefixCount (S : Set X) (z : ℕ × (ℕ → X)) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin z.1 ↦ z.2 i ∈ S).card

omit [MeasurableSpace X] in
theorem poissonPrefixCount_cast (S : Set X) (z : ℕ × (ℕ → X)) :
    (poissonPrefixCount S z : ℝ) = poissonPrefixSum (S.indicator (fun _ ↦ 1)) z := by
  classical
  simp only [poissonPrefixCount, poissonPrefixSum, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z.2 i ∈ S <;> simp [hi]

theorem integrable_poissonPrefixCount
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {S : Set X} (hS : MeasurableSet S) :
    Integrable (fun z ↦ (poissonPrefixCount S z : ℝ))
      ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  simp_rw [poissonPrefixCount_cast]
  exact integrable_poissonPrefixSum ν r (measurable_const.indicator hS)
    (B := 1) (fun x ↦ by by_cases hx : x ∈ S <;> simp [hx])

theorem integral_poissonPrefixCount
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {S : Set X} (hS : MeasurableSet S) :
    (∫ z, (poissonPrefixCount S z : ℝ)
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
      (r : ℝ) * (ν S).toReal := by
  simp_rw [poissonPrefixCount_cast]
  rw [integral_poissonPrefixSum ν r (measurable_const.indicator hS)
    (B := 1) (fun x ↦ by by_cases hx : x ∈ S <;> simp [hx])]
  simp [integral_indicator hS, measureReal_def]

end OTSelector.Probability
