import OTSelector.Reconstruction.TaggedDyadicEnergyRate

/-!
# Bounded probes on the same small-mass recovery competitor

The original type marginals control the probe correction even after the
full matching is selected from all original samples.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Bounded marks touching one type are controlled by its two original counts,
for every full matching, even one selected after seeing all samples. -/
theorem attributedTypeEnergy_le_typeCounts
    {T : Type*} {q n : ℕ} (t : T) (x y : Fin n → T × DyadicUnitCube q)
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ i j, cost i j ≤ B) :
    attributedTypeEnergy t x y cost σ ≤
      B * (partitionCount (fun i ↦ (x i).1) t + partitionCount (fun i ↦ (y i).1) t) := by
  classical
  have ht (a b : T) : typeTouchIndicator t a b ≤ partitionIndicator a t + partitionIndicator b t := by
    by_cases ha : a = t <;> by_cases hb : b = t <;>
      simp [typeTouchIndicator, partitionIndicator, ha, hb]
  calc
    _ ≤ ∑ i, B * (partitionIndicator (x i).1 t + partitionIndicator (y (σ i)).1 t) := by
      apply Finset.sum_le_sum
      intro i _
      exact ((mul_le_mul_of_nonneg_left (hc i (σ i)) (typeTouchIndicator_bounds _ _ _).1).trans
        (mul_le_mul_of_nonneg_right (ht _ _) hB)).trans_eq (by ring)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        Equiv.sum_comp σ (fun i ↦ partitionIndicator (y i).1 t)]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The bounded-probe correction on any selected subplan is linear in its raw
mass. It uses the same measurable full permutation as the energy estimate. -/
theorem expected_taggedHierarchy_bounded_probe
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (K : ℕ) (S : Finset T) (g : Ω → Fin n → Fin n → ℝ)
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j)) {G ε : ℝ} (hG : 0 ≤ G)
    (hmass : (∑ t ∈ S, μ.real {x | x.1 = t}) = ε)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, |g ξ i j| ≤ G) :
    Integrable (fun ξ ↦ attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (fun i j ↦ |g ξ i j|) (taggedHierarchyAssignment K xs ys ξ)) P ∧
    (∫ ξ, attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (fun i j ↦ |g ξ i j|) (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤ 2 * G * n * ε := by
  classical
  have hm (t : T) : MeasurableSet {x : T × DyadicUnitCube q | x.1 = t} :=
    measurable_fst (measurableSet_singleton t)
  have hxm (t : T) := iidTypeCount_moments P μ xs hx hxi hxl (hm t)
  have hym (t : T) := iidTypeCount_moments P μ ys hy hyi hyl (hm t)
  have hEi (t : T) := integrable_attributedTypeEnergy P t xs ys hx hy
    (fun ξ i j ↦ |g ξ i j|) (fun i j ↦ by simpa only [Real.norm_eq_abs] using (hg i j).norm)
    (taggedHierarchyAssignment K xs ys)
    (measurable_taggedHierarchyAssignment_eval K xs ys hx hy)
    (Filter.Eventually.of_forall (fun _ _ _ ↦ abs_nonneg _)) hbound
  have hEt (t : T) : (∫ ξ, attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (fun i j ↦ |g ξ i j|) (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤
      2 * G * n * μ.real {x | x.1 = t} := by
    have hix := (hxm t).1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hiy := (hym t).1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hiU : Integrable (fun ξ ↦ G *
        (iidTypeCount xs {x | x.1 = t} ξ + iidTypeCount ys {x | x.1 = t} ξ)) P :=
      (hix.add hiy).const_mul _
    have h := integral_mono_ae (hEi t) hiU (by
      filter_upwards [hbound] with ξ hξ
      simpa only [partitionCount_tag_eq_iidTypeCount] using
        attributedTypeEnergy_le_typeCounts t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
          (fun i j ↦ |g ξ i j|) (taggedHierarchyAssignment K xs ys ξ) hG hξ)
    rw [integral_const_mul, integral_add hix hiy, (hxm t).2.1, (hym t).2.1] at h
    exact h.trans_eq (by ring)
  refine ⟨integrable_finsetSum _ (fun t _ ↦ hEi t), ?_⟩
  unfold attributedTypesEnergy
  rw [integral_finsetSum _ (fun t _ ↦ hEi t)]
  calc
    _ ≤ ∑ t ∈ S, 2 * G * n * μ.real {x | x.1 = t} := Finset.sum_le_sum (fun t _ ↦ hEt t)
    _ = _ := by rw [← Finset.mul_sum, hmass]

end OTSelector.Reconstruction
