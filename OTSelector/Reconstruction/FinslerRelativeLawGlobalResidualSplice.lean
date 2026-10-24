import OTSelector.Finite.PartitionCountTotal
import OTSelector.Reconstruction.FinslerRelativeLawSelectedHierarchyMatching
import OTSelector.Reconstruction.FinslerRelativeLawGlobalMatchingSplice

/-!
# Reconstruction.FinslerRelativeLawGlobalResidualSplice

**Conditions:** A finite index type and finite target label type, with arbitrary label map.

**Objects:** The total of all real partition counts and the original index cardinality.

**Proof detail:** Exchange the two finite sums; each index contributes exactly one nonzero label indicator, so the total equals the original number of indices.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-! Splice the original true-type hierarchy matching with all retained cell
matchings. Bounded completion sees only original count and legal deficits. -/

open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000



/-- The residual cell count equals the sum of the selected original type
counts. This is a pointwise partition identity, without any independence claim. -/
theorem partitionCount_none_eq_selected
    {T C : Type*} [DecidableEq T] [DecidableEq C] {n : ℕ}
    (S : Finset T) (types : Fin n → T) (cell : Fin n → Option C)
    (hcell : ∀ i, cell i = none ↔ types i ∈ S) :
    partitionCount cell none = ∑ t ∈ S, partitionCount types t := by
  unfold partitionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show partitionIndicator (cell i) none = if types i ∈ S then (1 : ℝ) else 0 from by
    simp only [partitionIndicator, hcell i]]
  by_cases h : types i ∈ S <;> simp [partitionIndicator, h, eq_comm]

/-- On actual original indices, the selected hierarchy piece and retained
cell competitors admit a full assignment with only count/Hall completion cost. -/
theorem exists_global_assignment_retained_and_selected
    {T C : Type*} [Fintype T] [Fintype C] [DecidableEq T] [DecidableEq C]
    {q n : ℕ} (S : Finset T) (x y : Fin n → T × DyadicUnitCube q)
    (hierarchy : Assignment n)
    (hsat : ∀ i j, (x i).1 = (y (hierarchy j)).1 →
      (x i).1 ≠ (y (hierarchy i)).1 → (x j).1 = (y (hierarchy j)).1)
    (sourceCell targetCell : Fin n → Option C)
    (hsourceCell : ∀ i, sourceCell i = none ↔ (x i).1 ∈ S)
    (htargetCell : ∀ j, targetCell j = none ↔ (y j).1 ∈ S)
    (retained : C → OTSelector.PartialMatching n n)
    (hretained : ∀ c e, e ∈ (retained c).edges →
      sourceCell e.1 = some c ∧ targetCell e.2 = some c)
    (score majorant : Fin n → Fin n → ℝ)
    (hmajorant : ∀ i j, 0 ≤ majorant i j) (hscore : ∀ i j, score i j ≤ majorant i j)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i j, score i j ≤ B) :
    ∃ full : Assignment n, assignmentCost score full ≤
      (∑ c, (retained c).cost score) + attributedTypesEnergy S x y majorant hierarchy +
      B * ((∑ c, (partitionCount sourceCell (some c) - (retained c).card)) +
        ∑ t, |partitionCount (fun i ↦ (x i).1) t - partitionCount (fun j ↦ (y j).1) t|) := by
  let residual := selectedSameTypeMatching S (fun i ↦ (x i).1) (fun j ↦ (y j).1) hierarchy
  let pieces : Option C → OTSelector.PartialMatching n n
    | none => residual
    | some c => retained c
  have hpieces : ∀ c e, e ∈ (pieces c).edges → sourceCell e.1 = c ∧ targetCell e.2 = c := by
    intro c e he
    cases c with
    | none =>
      have h := selectedSameTypeMatching_mem S (fun i ↦ (x i).1) (fun j ↦ (y j).1) hierarchy he
      exact ⟨(hsourceCell e.1).mpr h.1, (htargetCell e.2).mpr h.2.1⟩
    | some c => exact hretained c e he
  let U := populationCellMatchingUnion sourceCell targetCell pieces hpieces
  have hUcard : U.card = residual.card + ∑ c, (retained c).card := by
    rw [show U.card = ∑ c, (pieces c).card from card_populationCellMatchingUnion _ _ _ _]
    rw [Fintype.sum_option]
  have hUcost : U.cost score = residual.cost score + ∑ c, (retained c).cost score := by
    rw [show U.cost score = ∑ c, (pieces c).cost score from cost_populationCellMatchingUnion _ _ _ _ _]
    rw [Fintype.sum_option]
  have hres := selectedSameTypeMatching_source_defect_le S
    (fun i ↦ (x i).1) (fun j ↦ (y j).1) hierarchy hsat
  have hdisc : (∑ t ∈ S, |partitionCount (fun i ↦ (x i).1) t -
      partitionCount (fun j ↦ (y j).1) t|) ≤
      ∑ t, |partitionCount (fun i ↦ (x i).1) t - partitionCount (fun j ↦ (y j).1) t| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ ↦ abs_nonneg _)
  have hpartition := sum_partitionCount_eq_card sourceCell
  rw [Fintype.sum_option, Fintype.card_fin,
    partitionCount_none_eq_selected S (fun i ↦ (x i).1) sourceCell hsourceCell] at hpartition
  have hdefect : ((n - U.card : ℕ) : ℝ) ≤
      (∑ c, (partitionCount sourceCell (some c) - (retained c).card)) +
        ∑ t, |partitionCount (fun i ↦ (x i).1) t - partitionCount (fun j ↦ (y j).1) t| := by
    rw [Nat.cast_sub (by simpa using U.card_le), hUcard, Nat.cast_add, Nat.cast_sum,
      Finset.sum_sub_distrib]
    change (n : ℝ) - ((residual.card : ℝ) + _) ≤ _
    change _ - (residual.card : ℝ) ≤ _ at hres
    linarith
  have hresCost : residual.cost score ≤ attributedTypesEnergy S x y majorant hierarchy := by
    apply le_trans (Finset.sum_le_sum (fun e he ↦ hscore e.1 e.2))
    exact selectedSameTypeMatching_cost_le_attributed S x y hierarchy majorant hmajorant
  obtain ⟨ρ, hcard, hcost⟩ := U.exists_maxCardinality_cost_le score hbound
  obtain ⟨full, hfull⟩ := ρ.exists_assignment_cost_eq score hcard
  refine ⟨full, hfull.trans_le ?_⟩
  have hcompletion := mul_le_mul_of_nonneg_left hdefect hB
  rw [min_self, hUcost] at hcost
  nlinarith only [hcost, hresCost, hcompletion]

end OTSelector.Reconstruction
