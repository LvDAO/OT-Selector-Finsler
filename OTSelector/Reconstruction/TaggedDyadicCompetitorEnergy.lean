import OTSelector.Reconstruction.TaggedDyadicEnergyRate

/-!
# The actual full hierarchy competitor has controlled total cost

This transfers the simultaneous type-attribution bound to the cost of the same
full permutation, retaining its measurability and original sample law.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Selecting the target index measurably preserves integrability of a uniformly
bounded nonnegative original finite edge cost. -/
theorem integrable_measurable_assignmentCost
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (cost : Ω → Fin n → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j))
    (σ : Ω → Assignment n) (hσ : ∀ i, Measurable (fun ξ ↦ σ ξ i)) {B : ℝ}
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B) :
    Integrable (fun ξ ↦ assignmentCost (cost ξ) (σ ξ)) P := by
  unfold assignmentCost
  apply integrable_finsetSum
  intro i _
  have hm : Measurable (fun ξ ↦ cost ξ i (σ ξ i)) :=
    (measurable_from_prod_countable_left (f := fun p : Ω × Fin n ↦ cost p.1 i p.2)
      (fun j ↦ hc i j)).comp (measurable_id.prodMk (hσ i))
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  filter_upwards [hcn, hbound] with ξ hn hb
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hn i (σ ξ i))] using hb i (σ ξ i)

/-- A simultaneous all-type attribution estimate bounds the same full
permutation's cost, rather than replacing it by a separately chosen optimizer. -/
theorem expected_assignmentCost_le_all_type_energy
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (cost : Ω → Fin n → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j))
    (σ : Ω → Assignment n) (hσ : ∀ i, Measurable (fun ξ ↦ σ ξ i)) {B a R : ℝ}
    (ha : 0 ≤ a) (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hi : Integrable (fun ξ ↦ attributedTypesEnergy Finset.univ
      (fun i ↦ xs i ξ) (fun i ↦ ys i ξ) (cost ξ) (σ ξ)) P)
    (hb : a * (∫ ξ, attributedTypesEnergy Finset.univ
      (fun i ↦ xs i ξ) (fun i ↦ ys i ξ) (cost ξ) (σ ξ) ∂P) ≤ R) :
    Integrable (fun ξ ↦ assignmentCost (cost ξ) (σ ξ)) P ∧
      a * (∫ ξ, assignmentCost (cost ξ) (σ ξ) ∂P) ≤ R := by
  have hci := integrable_measurable_assignmentCost P cost hc σ hσ hcn hbound
  refine ⟨hci, (mul_le_mul_of_nonneg_left (integral_mono_ae hci hi ?_) ha).trans hb⟩
  filter_upwards [hcn] with ξ hξ
  exact assignmentCost_le_attributedTypesEnergy_univ
    (fun i ↦ xs i ξ) (fun i ↦ ys i ξ) (cost ξ) (σ ξ) hξ

end OTSelector.Reconstruction
