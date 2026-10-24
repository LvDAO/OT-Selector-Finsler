import OTSelector.Reconstruction.AssignmentPressureLocalization
import OTSelector.Finite.FractionalGauge

/-!
# Removing endpoint cores preserves quantitative marginal mass bounds

For every doubly stochastic plan the mass touching a discarded source or target
is bounded by the original two marginal losses. This is a mass statement; it does
not identify discarded energy with discarded probability.
-/

open Set Matrix MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {n : ℕ}

/-- The normalized exceptional edge mass is its indicator readout. -/
theorem fractionalEdgeMass_eq_indicator_cost (Q : Set (Fin n × Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) :
    fractionalEdgeMass Q W =
      fractionalAssignmentCost (fun i j ↦ Q.indicator (fun _ ↦ (1 : ℝ)) (i, j)) W / n := by
  classical
  unfold fractionalEdgeMass fractionalAssignmentCost
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : (i, j) ∈ Q <;> simp [h]

/-- The mass of edges touching discarded endpoints is bounded by the two
unmodified empirical marginal losses, uniformly over the whole feasible face. -/
theorem fractionalEdgeMass_endpoint_union_le
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W ∈ doublyStochastic ℝ (Fin n))
    (I J : Set (Fin n)) :
    fractionalEdgeMass {ij | ij.1 ∈ I ∨ ij.2 ∈ J} W ≤
      ((∑ i : Fin n, I.indicator (fun _ ↦ (1 : ℝ)) i) +
        ∑ j : Fin n, J.indicator (fun _ ↦ (1 : ℝ)) j) / n := by
  classical
  let row := I.indicator (fun _ ↦ (1 : ℝ))
  let col := J.indicator (fun _ ↦ (1 : ℝ))
  have hcost := fractionalAssignmentCost_mono_of_feasible hW
    (c := fun i j ↦ ({ij | ij.1 ∈ I ∨ ij.2 ∈ J} : Set (Fin n × Fin n)).indicator
      (fun _ ↦ (1 : ℝ)) (i, j)) (d := fun i j ↦ row i + col j) (by
      intro i j
      by_cases hi : i ∈ I <;> by_cases hj : j ∈ J <;> simp [row, col, hi, hj])
  have heq : fractionalAssignmentCost (fun i j ↦ row i + col j) W =
      (∑ i, row i) + ∑ j, col j := by
    simpa only [Pi.zero_apply, zero_mul, zero_add] using
      fractionalAssignmentCost_scale_add_rowColumn (0 : Matrix (Fin n) (Fin n) ℝ)
        W 0 row col hW
  rw [heq] at hcost
  rw [fractionalEdgeMass_eq_indicator_cost]
  exact div_le_div_of_nonneg_right hcost (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- Restriction of a feasible plan has row and column capacities at most one. -/
theorem fractional_restrict_capacities
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W ∈ doublyStochastic ℝ (Fin n))
    (Q : Set (Fin n × Fin n)) :
    let R := fun i j ↦ Q.indicator (fun ij ↦ W ij.1 ij.2) (i, j)
    (∀ i j, 0 ≤ R i j) ∧ (∀ i, ∑ j, R i j ≤ 1) ∧ (∀ j, ∑ i, R i j ≤ 1) := by
  classical
  dsimp only
  have hbound (i j : Fin n) :
      Q.indicator (fun ij ↦ W ij.1 ij.2) (i, j) ≤ W i j := by
    by_cases h : (i, j) ∈ Q
    · simp only [indicator_of_mem h, le_refl]
    · simpa only [indicator_of_notMem h] using nonneg_of_mem_doublyStochastic hW
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_, fun j ↦ ?_⟩
  · by_cases h : (i, j) ∈ Q
    · simpa only [indicator_of_mem h] using nonneg_of_mem_doublyStochastic hW
    · simp only [indicator_of_notMem h, le_refl]
  · exact (Finset.sum_le_sum (fun j _ ↦ hbound i j)).trans_eq
      (sum_row_of_mem_doublyStochastic hW i)
  · exact (Finset.sum_le_sum (fun i _ ↦ hbound i j)).trans_eq
      (sum_col_of_mem_doublyStochastic hW j)

end OTSelector.Reconstruction
