import OTSelector.Finite.Assignment
import OTSelector.Finite.AssignmentDual
import OTSelector.Finite.PerturbedValue
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.HierarchicalAssignment.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.HierarchicalAssignment`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.HierarchicalAssignment

**Conditions:** Finite nested partitions of two equally sized arrays; the cost bound has the exact displayed base and weights, with no additional sign condition on those weights.

**Objects:** One unweighted hierarchy-distance optimizer, exact crossing counts at every level and its weighted histogram cost bound.

**Proof detail:** Use finite dual tightness for the two-edge exchange inequality; a swap cannot increase any nested-level mismatch and strictly improves an opposite crossing, so cell indicator differences have one sign and give the exact half-discrepancy count at every level.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Distribution-free squared matching above dimension four](main.tex#lem:general-upper-dyadic), main.tex label lem:general-upper-dyadic, line 1634.

Source relation (composition): Finite assignment duality and exchange arguments are classical; the single hierarchy optimizer and exact simultaneous histogram identities are locally proved deterministic ingredients of main.tex lem:general-upper-dyadic. The selected result does not assert the paper’s probabilistic dimension-dependent bound.
-/

/-!
# A simultaneous matching for every level of a finite partition hierarchy

An optimizer for the sum of discrete partition distances has no simultaneous
incoming and outgoing crossings at a cell. This supplies a single genuine
permutation whose discrepancy bound holds at every dyadic scale.
-/

open Function
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Every optimal finite assignment satisfies its two-edge exchange inequality. -/
theorem optimalAssignment_two_edge {n : ℕ} {cost : Fin n → Fin n → ℝ}
    {σ : Assignment n} (hσ : OptimalAssignment cost σ) (i j : Fin n) :
    cost i (σ i) + cost j (σ j) ≤ cost i (σ j) + cost j (σ i) := by
  obtain ⟨α, β, hfeasible, _, htight⟩ := exists_assignment_dual cost
  have hi := (htight σ).mp hσ i
  have hj := (htight σ).mp hσ j
  have hij := hfeasible i (σ j)
  have hji := hfeasible j (σ i)
  linarith

/-- Zero-one distance between cells of a partition. -/
def partitionDistance {C : Type*} (x y : C) : ℝ := by
  classical
  exact if x = y then 0 else 1

theorem partitionDistance_bounds {C : Type*} (x y : C) :
    0 ≤ partitionDistance x y ∧ partitionDistance x y ≤ 1 := by
  classical
  unfold partitionDistance
  split_ifs <;> norm_num

private theorem partitionDistance_uncross {C : Type*} (a b c d : C) (had : a = d) :
    partitionDistance a d + partitionDistance c b ≤
      partitionDistance a b + partitionDistance c d := by
  classical
  subst d
  by_cases hab : a = b
  · subst b
    simp [partitionDistance]
  by_cases hca : c = a
  · subst c
    simp [partitionDistance, hab]
  have hcb := (partitionDistance_bounds c b).2
  simpa [partitionDistance, hab, hca, one_add_one_eq_two] using hcb.trans (by norm_num : (1 : ℝ) ≤ 2)

/-- One cost, fixed before choosing the permutation, records all partition levels. -/
def hierarchyEdgeCost {X : Type*} {K n : ℕ} {C : Fin K → Type*}
    (cell : (k : Fin K) → X → C k) (x y : Fin n → X) (i j : Fin n) : ℝ :=
  ∑ k, partitionDistance (cell k (x i)) (cell k (y j))

/-- A single hierarchy optimizer saturates every cell: an outgoing source and
an incoming target cannot both remain unmatched to each other inside that cell. -/
theorem hierarchy_optimal_no_opposite_crossings
    {X : Type*} {K n : ℕ} {C : Fin K → Type*}
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ a b,
      cell l a = cell l b → cell k a = cell k b)
    (x y : Fin n → X) {σ : Assignment n}
    (hσ : OptimalAssignment (hierarchyEdgeCost cell x y) σ)
    (k : Fin K) (i j : Fin n)
    (hin : cell k (x i) = cell k (y (σ j)))
    (hout : cell k (x i) ≠ cell k (y (σ i))) :
    cell k (x j) = cell k (y (σ j)) := by
  classical
  by_contra hjout
  have hle (l : Fin K) :
      partitionDistance (cell l (x i)) (cell l (y (σ j))) +
          partitionDistance (cell l (x j)) (cell l (y (σ i))) ≤
        partitionDistance (cell l (x i)) (cell l (y (σ i))) +
          partitionDistance (cell l (x j)) (cell l (y (σ j))) := by
    rcases le_total l k with hl | hl
    · exact partitionDistance_uncross _ _ _ _ (hnested l k hl _ _ hin)
    · have hi : cell l (x i) ≠ cell l (y (σ i)) := fun h ↦
        hout (hnested k l hl _ _ h)
      have hj : cell l (x j) ≠ cell l (y (σ j)) := fun h ↦
        hjout (hnested k l hl _ _ h)
      have h₁ := (partitionDistance_bounds (cell l (x i)) (cell l (y (σ j)))).2
      have h₂ := (partitionDistance_bounds (cell l (x j)) (cell l (y (σ i)))).2
      simpa only [partitionDistance, ite_eq_right hi, ite_eq_right hj] using add_le_add h₁ h₂
  have hlt :
      partitionDistance (cell k (x i)) (cell k (y (σ j))) +
          partitionDistance (cell k (x j)) (cell k (y (σ i))) <
        partitionDistance (cell k (x i)) (cell k (y (σ i))) +
          partitionDistance (cell k (x j)) (cell k (y (σ j))) := by
    have hb := (partitionDistance_bounds (cell k (x j)) (cell k (y (σ i)))).2
    simpa only [partitionDistance, ite_eq_left hin, ite_eq_right hout, ite_eq_right hjout, zero_add, one_add_one_eq_two] using
      hb.trans_lt (by norm_num : (1 : ℝ) < 2)
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun l _ ↦ hle l)
    ⟨k, Finset.mem_univ k, hlt⟩
  simp only [Finset.sum_add_distrib] at hsum
  exact (not_lt_of_ge (optimalAssignment_two_edge hσ i j)) hsum

/-- Membership in one cell, represented as a real indicator. -/
def partitionIndicator {C : Type*} (x a : C) : ℝ := by
  classical
  exact if x = a then 1 else 0

/-- A real-valued histogram of a finite list at one partition cell. -/
def partitionCount {I C : Type*} [Fintype I] (x : I → C) (a : C) : ℝ :=
  ∑ i, partitionIndicator (x i) a

theorem partitionCount_abs_difference
    {n : ℕ} {C : Type*} (x y : Fin n → C) (σ : Assignment n)
    (hcross : ∀ i j, x i = y (σ j) → x i ≠ y (σ i) → x j = y (σ j)) (a : C) :
    |partitionCount x a - partitionCount y a| =
      ∑ i, |partitionIndicator (x i) a - partitionIndicator (y (σ i)) a| := by
  classical
  have hsum : (∑ i, partitionIndicator (y (σ i)) a) = partitionCount y a :=
    Equiv.sum_comp σ (fun j ↦ partitionIndicator (y j) a)
  rw [partitionCount, ← hsum, ← Finset.sum_sub_distrib]
  by_cases hdir : ∀ i, x i = a → y (σ i) = a
  · have hnonpos (i : Fin n) :
        partitionIndicator (x i) a - partitionIndicator (y (σ i)) a ≤ 0 := by
      by_cases hi : x i = a
      · simp [partitionIndicator, hi, hdir i hi]
      · unfold partitionIndicator
        split_ifs <;> norm_num
    rw [abs_of_nonpos (Finset.sum_nonpos (s := Finset.univ) (fun i _ ↦ hnonpos i)),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ (abs_of_nonpos (hnonpos i)).symm)
  · push Not at hdir
    obtain ⟨i, hix, hiy⟩ := hdir
    have hrev : ∀ j, y (σ j) = a → x j = a := by
      intro j hj
      exact (hcross i j (hix.trans hj.symm) (fun he ↦ hiy (he.symm.trans hix))).trans hj
    have hnonneg (j : Fin n) :
        0 ≤ partitionIndicator (x j) a - partitionIndicator (y (σ j)) a := by
      by_cases hj : y (σ j) = a
      · simp [partitionIndicator, hj, hrev j hj]
      · unfold partitionIndicator
        split_ifs <;> norm_num
    rw [abs_of_nonneg (Finset.sum_nonneg (s := Finset.univ) (fun j _ ↦ hnonneg j))]
    exact Finset.sum_congr rfl (fun j _ ↦ (abs_of_nonneg (hnonneg j)).symm)

theorem sum_abs_partition_indicator {C : Type*} [Fintype C] (x y : C) :
    (∑ a : C, |partitionIndicator x a - partitionIndicator y a|) =
      2 * partitionDistance x y := by
  classical
  by_cases hxy : x = y
  · simp [hxy, partitionDistance]
  have he (a : C) :
      |partitionIndicator x a - partitionIndicator y a| =
        partitionIndicator x a + partitionIndicator y a := by
    by_cases hx : x = a <;> by_cases hy : y = a <;> simp_all [partitionIndicator]
  simp_rw [he]
  simp [Finset.sum_add_distrib, partitionDistance, partitionIndicator, hxy, one_add_one_eq_two]

/-- Every level has exactly its histogram discrepancy, for the same optimizer.
This avoids selecting an unrelated matching at each dyadic scale. -/
theorem hierarchy_optimal_crossing_count
    {X : Type*} {K n : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ a b,
      cell l a = cell l b → cell k a = cell k b)
    (x y : Fin n → X) {σ : Assignment n}
    (hσ : OptimalAssignment (hierarchyEdgeCost cell x y) σ) (k : Fin K) :
    2 * (∑ i, partitionDistance (cell k (x i)) (cell k (y (σ i)))) =
      ∑ a, |partitionCount (cell k ∘ x) a - partitionCount (cell k ∘ y) a| := by
  classical
  have hcell (a : C k) := partitionCount_abs_difference (cell k ∘ x) (cell k ∘ y) σ
    (hierarchy_optimal_no_opposite_crossings cell hnested x y hσ k) a
  simp_rw [hcell]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ (sum_abs_partition_indicator _ _).symm)

/-- The hierarchy optimizer gives an actual competitor with the full weighted
multiscale discrepancy cost, without changing the permutation between scales. -/
theorem hierarchy_optimal_cost_bound
    {X : Type*} {K n : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ a b,
      cell l a = cell l b → cell k a = cell k b)
    (x y : Fin n → X) {σ : Assignment n}
    (hσ : OptimalAssignment (hierarchyEdgeCost cell x y) σ)
    (cost : Fin n → Fin n → ℝ) (base : ℝ) (weight : Fin K → ℝ)
    (hcost : ∀ i j, cost i j ≤ base +
      ∑ k, weight k * partitionDistance (cell k (x i)) (cell k (y j))) :
    assignmentCost cost σ ≤ (n : ℝ) * base +
      (1 / 2 : ℝ) * ∑ k, weight k *
        ∑ a, |partitionCount (cell k ∘ x) a - partitionCount (cell k ∘ y) a| := by
  classical
  calc
    assignmentCost cost σ ≤ ∑ i, (base + ∑ k,
        weight k * partitionDistance (cell k (x i)) (cell k (y (σ i)))) :=
      Finset.sum_le_sum (fun i _ ↦ hcost i (σ i))
    _ = (n : ℝ) * base + ∑ k, weight k *
        ∑ i, partitionDistance (cell k (x i)) (cell k (y (σ i))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← hierarchy_optimal_crossing_count cell hnested x y hσ k]
      ring

/-- Existence of a genuine full assignment with the multiscale histogram bound. -/
theorem exists_hierarchical_assignment_cost_bound
    {X : Type*} {K n : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ a b,
      cell l a = cell l b → cell k a = cell k b)
    (x y : Fin n → X) (cost : Fin n → Fin n → ℝ)
    (base : ℝ) (weight : Fin K → ℝ)
    (hcost : ∀ i j, cost i j ≤ base +
      ∑ k, weight k * partitionDistance (cell k (x i)) (cell k (y j))) :
    ∃ σ : Assignment n, assignmentCost cost σ ≤ (n : ℝ) * base +
      (1 / 2 : ℝ) * ∑ k, weight k *
        ∑ a, |partitionCount (cell k ∘ x) a - partitionCount (cell k ∘ y) a| :=
  ⟨_, hierarchy_optimal_cost_bound cell hnested x y
    (optimalAssignment_isOptimal _) cost base weight hcost⟩

end OTSelector.Reconstruction

end
end
