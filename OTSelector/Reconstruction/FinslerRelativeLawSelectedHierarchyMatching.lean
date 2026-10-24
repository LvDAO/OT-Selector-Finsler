import OTSelector.Reconstruction.PopulationTypedSubplanPressure
import OTSelector.Finite.MaxCardValueAssignment
import OTSelector.Finite.MatchingUnion

/-! The true-flag part of the same original hierarchy is a small-energy
partial matching. Only original type count discrepancies remain unmatched. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Keep exactly the hierarchy edges internal to a prescribed original type. -/
def selectedSameTypeMatching {T : Type*} [DecidableEq T] {n : ℕ}
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n) : OTSelector.PartialMatching n n where
  edges := (Finset.univ.filter (fun i ↦ x i ∈ S ∧ x i = y (σ i))).image (fun i ↦ (i, σ i))
  row_inj := by
    intro e he e' he' h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he'
    exact congrArg (fun i ↦ (i, σ i)) h
  col_inj := by
    intro e he e' he' h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he'
    exact congrArg (fun i ↦ (i, σ i)) (σ.injective h)

theorem selectedSameTypeMatching_mem {T : Type*} [DecidableEq T] {n : ℕ}
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n) {e : Fin n × Fin n}
    (he : e ∈ (selectedSameTypeMatching S x y σ).edges) :
    x e.1 ∈ S ∧ y e.2 ∈ S ∧ x e.1 = y e.2 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  have h := (Finset.mem_filter.mp hi).2
  exact ⟨h.1, h.2 ▸ h.1, h.2⟩

theorem card_selectedSameTypeMatching {T : Type*} [DecidableEq T] {n : ℕ}
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n) :
    ((selectedSameTypeMatching S x y σ).card : ℝ) =
      ∑ i : Fin n, if x i ∈ S ∧ x i = y (σ i) then (1 : ℝ) else 0 := by
  rw [OTSelector.PartialMatching.card, selectedSameTypeMatching,
    Finset.card_image_of_injective _ (fun i j h ↦ congrArg Prod.fst h),
    Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]

theorem cost_selectedSameTypeMatching {T : Type*} [DecidableEq T] {n : ℕ}
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n) (c : Fin n → Fin n → ℝ) :
    (selectedSameTypeMatching S x y σ).cost c =
      ∑ i : Fin n, if x i ∈ S ∧ x i = y (σ i) then c i (σ i) else 0 := by
  unfold OTSelector.PartialMatching.cost selectedSameTypeMatching
  rw [Finset.sum_image]
  · simp only [Finset.sum_filter]
  · intro i hi j hj h
    exact congrArg Prod.fst h

/-- The selected original source count loses only its type discrepancy under
an optimizer saturating each type. This is a deterministic count estimate. -/
theorem selectedSameTypeMatching_source_defect_le
    {T : Type*} [DecidableEq T] {n : ℕ}
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n)
    (hsat : ∀ i j, x i = y (σ j) → x i ≠ y (σ i) → x j = y (σ j)) :
    (∑ t ∈ S, partitionCount x t) - (selectedSameTypeMatching S x y σ).card ≤
      ∑ t ∈ S, |partitionCount x t - partitionCount y t| := by
  have hpoint (a b t : T) :
      partitionIndicator a t - (if a = t ∧ a = b then (1 : ℝ) else 0) ≤ typeCrossingCharge t a b := by
    by_cases ha : a = t <;> by_cases hb : b = t <;>
      simp [partitionIndicator, typeCrossingCharge, ha, hb, eq_comm]
  have hsum (a b : T) :
      (∑ t ∈ S, if a = t ∧ a = b then (1 : ℝ) else 0) =
        if a ∈ S ∧ a = b then (1 : ℝ) else 0 := by
    by_cases hab : a = b
    · simp [hab]
    · simp [hab]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    Finset.sum_le_sum (s := S) (fun t _ ↦ hpoint (x i) (y (σ i)) t))
  simp_rw [Finset.sum_sub_distrib, hsum] at h
  have hcount : (∑ i : Fin n, ∑ t ∈ S, partitionIndicator (x i) t) =
      ∑ t ∈ S, partitionCount x t := by rw [Finset.sum_comm]; rfl
  have hcross : (∑ i : Fin n, ∑ t ∈ S, typeCrossingCharge t (x i) (y (σ i))) =
      ∑ t ∈ S, |partitionCount x t - partitionCount y t| := by
    rw [Finset.sum_comm]
    simp_rw [sum_typeCrossingCharge_eq x y σ hsat]
  rw [hcount, hcross, ← card_selectedSameTypeMatching S x y σ] at h
  exact h

/-- The kept true-type edges cost no more than the already controlled original
attributed subplan energy. No new sampling law is assigned to their endpoints. -/
theorem selectedSameTypeMatching_cost_le_attributed
    {T : Type*} [DecidableEq T] {q n : ℕ}
    (S : Finset T) (x y : Fin n → T × DyadicUnitCube q) (σ : Assignment n)
    (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 ≤ c i j) :
    (selectedSameTypeMatching S (fun i ↦ (x i).1) (fun j ↦ (y j).1) σ).cost c ≤
      attributedTypesEnergy S x y c σ := by
  rw [cost_selectedSameTypeMatching]
  unfold attributedTypesEnergy attributedTypeEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : (x i).1 ∈ S ∧ (x i).1 = (y (σ i)).1
  · rw [ite_eq_left h]
    have ht := Finset.single_le_sum (fun t _ ↦ mul_nonneg
      (typeTouchIndicator_bounds t (x i).1 (y (σ i)).1).1 (hc i (σ i))) h.1
    simpa [typeTouchIndicator] using ht
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg fun t ht ↦ mul_nonneg
      (typeTouchIndicator_bounds t (x i).1 (y (σ i)).1).1 (hc i (σ i))

end OTSelector.Reconstruction
