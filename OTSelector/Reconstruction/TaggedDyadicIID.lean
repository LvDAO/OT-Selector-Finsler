import OTSelector.Reconstruction.TaggedDyadicEnergy
import OTSelector.Reconstruction.IIDDyadicCubeMatching

/-!
# Original typed iid counts and one measurable hierarchy assignment

Raw cell fluctuations are integrated for the same original marked samples.
A deterministic measurable tie rule supplies one full permutation at every depth.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- A population-scale cutoff also covers empty and sub-unit expected types. -/
theorem exists_dyadicCube_rate_cutoff_nonneg {q : ℕ} (hq : 4 < q) {m : ℝ}
    (hm : 0 ≤ m) :
    ∃ K : ℕ, m * (1 / 4 : ℝ) ^ K + (1 / 2 : ℝ) *
      (∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
        Real.sqrt (2 * m * ((2 : ℝ) ^ (k + 1) + 1) ^ q)) ≤
      dyadicMatchingConstant q * m ^ (1 - 2 / (q : ℝ)) := by
  by_cases hm1 : 1 ≤ m
  · exact exists_dyadicCube_rate_cutoff hq hm1
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hg0 : 0 ≤ 1 - 2 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hg1 : 1 - 2 / (q : ℝ) ≤ 1 := by
    have : 0 ≤ 2 / (q : ℝ) := by positivity
    linarith
  have hpow : m ≤ m ^ (1 - 2 / (q : ℝ)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' hm (le_of_not_ge hm1) hg0 hg1
  have hC : 1 ≤ dyadicMatchingConstant q := by
    have hR := one_lt_dyadicFluctuationRatio hqR
    unfold dyadicMatchingConstant
    have : 0 ≤ ((2 : ℝ) ^ q * Real.sqrt 2) / (dyadicFluctuationRatio q - 1) := by positivity
    linarith
  refine ⟨0, ?_⟩
  simpa using hpow.trans (le_mul_of_one_le_left (Real.rpow_nonneg hm _) hC)

/-- Exact raw mass partition within a fixed original population type. -/
theorem sum_type_cell_mass {X T C : Type*} [MeasurableSpace X] [Fintype C]
    (μ : Measure X) [IsFiniteMeasure μ] (tag : X → T) (cell : X → C) (t : T)
    (hm : ∀ a, MeasurableSet {x | (tag x, cell x) = (t, a)}) :
    (∑ a, μ.real {x | (tag x, cell x) = (t, a)}) = μ.real {x | tag x = t} := by
  classical
  have h := sum_measureReal_preimage_singleton (μ := μ)
    (({t} : Finset T).product Finset.univ) (f := fun x ↦ (tag x, cell x))
    (fun a ha ↦ by
      have hat : a.1 = t := by simpa using (Finset.mem_product.mp ha).1
      subst hat
      exact hm a.2)
  simpa [Finset.sum_product, Set.preimage, Set.mem_singleton_iff, eq_comm] using h

/-- The histogram fluctuation uses a type's raw mass, including zero mass. -/
theorem iid_taggedDyadicDiscrepancy_bound
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    {q n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P) (t : T) (k : ℕ) :
    Integrable (fun ξ ↦ taggedDyadicDiscrepancy t k (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)) P ∧
    (∫ ξ, taggedDyadicDiscrepancy t k (fun i ↦ xs i ξ) (fun i ↦ ys i ξ) ∂P) ≤
      Real.sqrt (2 * (n : ℝ) * μ.real {x | x.1 = t} * ((2 : ℝ) ^ k + 1) ^ q) := by
  classical
  let A := fun a : Fin q → Fin (2 ^ k + 1) ↦
    {x : T × DyadicUnitCube q | (x.1, dyadicCubeCell k x.2) = (t, a)}
  have hA (a : Fin q → Fin (2 ^ k + 1)) : MeasurableSet (A a) :=
    (measurable_fst.prodMk ((measurable_dyadicCubeCell k).comp measurable_snd))
      (measurableSet_singleton (t, a))
  have hmass := sum_type_cell_mass μ Prod.fst (fun x ↦ dyadicCubeCell k x.2) t hA
  have heq (zs : Fin n → Ω → T × DyadicUnitCube q) a ξ :
      iidTypeCount zs (A a) ξ =
      partitionCount (fun i ↦ ((zs i ξ).1, dyadicCubeCell k (zs i ξ).2)) (t, a) := by
    unfold iidTypeCount partitionCount
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ((zs i ξ).1, dyadicCubeCell k (zs i ξ).2) = (t, a)
    · simp only [Prod.mk.injEq] at hi
      simp [A, partitionIndicator, hi.1, hi.2]
    · simp only [Prod.mk.injEq] at hi
      simp [A, partitionIndicator, hi]
  have h := iidTypeCount_total_difference_bound P μ μ xs ys hx hy hxi hyi hxl hyl hxy
    A A hA hA (fun _ ↦ rfl) hmass
  simp only [heq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at h
  simpa only [taggedDyadicDiscrepancy, mul_assoc, mul_comm, mul_left_comm] using h


/-- The deterministic tie rule for the one original type-and-cell hierarchy. -/
def taggedHierarchyAssignment {Ω T : Type*} {q n : ℕ} (K : ℕ)
    (xs ys : Fin n → Ω → T × DyadicUnitCube q) (ξ : Ω) : Assignment n :=
  firstOptimalAssignment (taggedHierarchyCost K (fun i ↦ xs i ξ) (fun i ↦ ys i ξ))

theorem measurable_taggedHierarchyAssignment_eval
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (K : ℕ) (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i)) (i : Fin n) :
    Measurable (fun ξ ↦ taggedHierarchyAssignment K xs ys ξ i) := by
  let : MeasurableSpace (Assignment n) := ⊤
  have hc (i j : Fin n) : Measurable (fun ξ ↦
      taggedHierarchyCost K (fun l ↦ xs l ξ) (fun l ↦ ys l ξ) i j) := by
    unfold taggedHierarchyCost hierarchyEdgeCost
    apply Finset.measurable_sum
    intro k _
    exact (measurable_of_countable (fun p ↦ partitionDistance p.1 p.2)).comp
      (((measurable_taggedDyadicCell k.val).comp (hx i)).prodMk
        ((measurable_taggedDyadicCell k.val).comp (hy j)))
  exact (measurable_of_countable (fun σ : Assignment n ↦ σ i)).comp
    (measurable_firstOptimalAssignment _ hc)

theorem typeTouchIndicator_bounds {T : Type*} (t a b : T) :
    0 ≤ typeTouchIndicator t a b ∧ typeTouchIndicator t a b ≤ 1 := by
  classical
  simp only [typeTouchIndicator]
  split_ifs <;> norm_num

theorem measurable_attributedTypeEnergy
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    {q n : ℕ} (t : T) (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (cost : Ω → Fin n → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j))
    (σ : Ω → Assignment n) (hσ : ∀ i, Measurable (fun ξ ↦ σ ξ i)) :
    Measurable (fun ξ ↦ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (cost ξ) (σ ξ)) := by
  classical
  unfold attributedTypeEnergy
  apply Finset.measurable_sum
  intro i _
  have hym : Measurable (fun ξ ↦ ys (σ ξ i) ξ) :=
    (measurable_from_prod_countable_left (f := fun p : Ω × Fin n ↦ ys p.2 p.1)
      (fun j ↦ hy j)).comp
      (measurable_id.prodMk (hσ i))
  have hcm : Measurable (fun ξ ↦ cost ξ i (σ ξ i)) :=
    (measurable_from_prod_countable_left (f := fun p : Ω × Fin n ↦ cost p.1 i p.2)
      (fun j ↦ hc i j)).comp
      (measurable_id.prodMk (hσ i))
  have ht : Measurable (fun ξ ↦ typeTouchIndicator t (xs i ξ).1 (ys (σ ξ i) ξ).1) := by
    unfold typeTouchIndicator
    exact measurable_const.ite
      (((hx i).fst (measurableSet_singleton t)).union
        (hym.fst (measurableSet_singleton t))) measurable_const
  exact ht.mul hcm

/-- Attribution is integrable under the original bounded physical cost. -/
theorem integrable_attributedTypeEnergy
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    {q n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (t : T) (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (cost : Ω → Fin n → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j))
    (σ : Ω → Assignment n) (hσ : ∀ i, Measurable (fun ξ ↦ σ ξ i)) {B : ℝ}
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B) :
    Integrable (fun ξ ↦ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (cost ξ) (σ ξ)) P := by
  apply (integrable_const ((n : ℝ) * B)).mono'
    (measurable_attributedTypeEnergy t xs ys hx hy cost hc σ hσ).aestronglyMeasurable
  filter_upwards [hcn, hbound] with ξ hnon hbd
  have hn : 0 ≤ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ) (cost ξ) (σ ξ) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (typeTouchIndicator_bounds _ _ _).1 (hnon i _))
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  calc
    _ ≤ ∑ i : Fin n, B := Finset.sum_le_sum (fun i _ ↦
      (mul_le_mul_of_nonneg_right (typeTouchIndicator_bounds _ _ _).2 (hnon i _)).trans
        (by simpa using hbd i (σ ξ i)))
    _ = _ := by simp


theorem partitionCount_tag_eq_iidTypeCount {Ω T : Type*} {q n : ℕ}
    (zs : Fin n → Ω → T × DyadicUnitCube q) (t : T) (ξ : Ω) :
    partitionCount (fun i ↦ (zs i ξ).1) t = iidTypeCount zs {x | x.1 = t} ξ := by
  classical
  unfold partitionCount iidTypeCount
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (zs i ξ).1 = t <;> simp [partitionIndicator, hi]

set_option backward.isDefEq.respectTransparency false in
/-- The same measurable full permutation has a finite-depth expectation bound
for each original type, based on its raw population mass. -/
theorem expected_taggedHierarchy_attributed_energy_multiscale
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n K N : ℕ} (hNK : N ≤ K)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (t : T) (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j)) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hquadratic : ∀ᵐ ξ ∂P, ∀ i j, (xs i ξ).1 = t → (ys j ξ).1 = t →
      cost ξ i j ≤ C * ‖dyadicCubePoint (xs i ξ).2 - dyadicCubePoint (ys j ξ).2‖ ^ 2) :
    Integrable (fun ξ ↦ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) P ∧
    (∫ ξ, attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (cost ξ) (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤
      C * ((n : ℝ) * μ.real {x | x.1 = t} * (1 / 4 : ℝ) ^ N +
        (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k *
          Real.sqrt (2 * (n : ℝ) * μ.real {x | x.1 = t} *
            ((2 : ℝ) ^ (k + 1) + 1) ^ q)) +
      B * Real.sqrt (2 * (n : ℝ) * μ.real {x | x.1 = t}) := by
  classical
  let A : Set (T × DyadicUnitCube q) := {x | x.1 = t}
  have hA : MeasurableSet A := measurable_fst (measurableSet_singleton t)
  have hmean := iidTypeCount_moments P μ xs hx hxi hxl hA
  have hdiff := iidTypeCount_difference_bound P μ μ xs ys hx hy hxi hyi hxl hyl hxy hA hA rfl
  let d (k : ℕ) (ξ : Ω) := taggedDyadicDiscrepancy t (k + 1)
    (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
  have hd (k : ℕ) := iid_taggedDyadicDiscrepancy_bound P μ xs ys hx hy hxi hyi hxl hyl hxy t (k + 1)
  have hmi := hmean.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsi : Integrable (fun ξ ↦ ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k * d k ξ) P :=
    integrable_finsetSum _ (fun k _ ↦ (hd k).1.const_mul _)
  have hui : Integrable (fun ξ ↦ C * (iidTypeCount xs A ξ * (1 / 4 : ℝ) ^ N +
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k * d k ξ) +
      B * |iidTypeCount xs A ξ - iidTypeCount ys A ξ|) P :=
    (((hmi.mul_const _).add (hsi.const_mul _)).const_mul _).add (hdiff.1.const_mul _)
  have hei := integrable_attributedTypeEnergy P t xs ys hx hy cost hc
    (taggedHierarchyAssignment K xs ys)
    (measurable_taggedHierarchyAssignment_eval K xs ys hx hy) hcn hbound
  refine ⟨hei, ?_⟩
  have hle := integral_mono_ae hei hui (by
    filter_upwards [hbound, hquadratic] with ξ hbξ hqξ
    have h := taggedHierarchy_attributed_energy_le hNK t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (firstOptimalAssignment_isOptimal _) (cost ξ) C B hC hbξ hqξ
    simpa only [partitionCount_tag_eq_iidTypeCount, taggedHierarchyAssignment, A, d] using h)
  have hbasi : Integrable (fun ξ ↦ iidTypeCount xs A ξ * (1 / 4 : ℝ) ^ N) P := hmi.mul_const _
  have hcoarsi : Integrable (fun ξ ↦ (1 / 2 : ℝ) * ∑ k ∈ Finset.range N,
      (1 / 4 : ℝ) ^ k * d k ξ) P := hsi.const_mul _
  have hinti : Integrable (fun ξ ↦ C * (iidTypeCount xs A ξ * (1 / 4 : ℝ) ^ N +
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k * d k ξ)) P :=
    (hbasi.add hcoarsi).const_mul _
  have hcrossi : Integrable (fun ξ ↦ B * |iidTypeCount xs A ξ - iidTypeCount ys A ξ|) P :=
    hdiff.1.const_mul _
  rw [integral_add hinti hcrossi, integral_const_mul, integral_const_mul,
    integral_add hbasi hcoarsi, integral_mul_const,
    integral_const_mul, integral_finsetSum _ (fun k _ ↦ (hd k).1.const_mul _), hmean.2.1] at hle
  simp only [integral_const_mul] at hle
  apply hle.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact Finset.sum_le_sum (fun k _ ↦ mul_le_mul_of_nonneg_left (hd k).2 (by positivity))
  · exact mul_le_mul_of_nonneg_left hdiff.2 hB



end OTSelector.Reconstruction
