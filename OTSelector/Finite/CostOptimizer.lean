import OTSelector.Basic.FiniteSampleLaw
import OTSelector.Gauge.RowColumn
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable finite optimizers and exact affine normalization

A fixed enumeration of permutations selects the first minimum for any real edge-cost matrix.
This rule is measurable for every measurable family of matrices, including samples with ties.
Positive scaling and row-column additions preserve both the full optimal set and this rule.
The final lemmas apply the invariance to the slope-profile normalization of a smooth norm.
-/

open MeasureTheory Set
open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

private noncomputable def assignmentEnumeration (n : ℕ) : ℕ → Assignment n := by
  let _ : Encodable (Assignment n) := Encodable.ofCountable _
  exact fun k ↦ (Encodable.decode k).getD (Equiv.refl _)

private theorem assignmentEnumeration_surjective (n : ℕ) :
    Function.Surjective (assignmentEnumeration n) := by
  let _ : Encodable (Assignment n) := Encodable.ofCountable _
  exact Encodable.surjective_decode_getD _ (Equiv.refl _)

private theorem exists_optimalAssignment_index (cost : Fin n → Fin n → ℝ) :
    ∃ k, OptimalAssignment cost (assignmentEnumeration n k) := by
  obtain ⟨σ, hσ⟩ := exists_optimalAssignment cost
  obtain ⟨k, rfl⟩ := assignmentEnumeration_surjective n σ
  exact ⟨k, hσ⟩

/-- The first optimal permutation in one fixed enumeration, with a deterministic tie rule. -/
noncomputable def firstOptimalAssignment (cost : Fin n → Fin n → ℝ) : Assignment n := by
  classical
  exact assignmentEnumeration n (Nat.find (exists_optimalAssignment_index cost))

theorem firstOptimalAssignment_isOptimal (cost : Fin n → Fin n → ℝ) :
    OptimalAssignment cost (firstOptimalAssignment cost) := by
  classical
  exact Nat.find_spec (exists_optimalAssignment_index cost)

/-- The tie rule only depends on the optimal set. -/
theorem firstOptimalAssignment_eq_of_optimal_iff (cost other : Fin n → Fin n → ℝ)
    (h : ∀ σ, OptimalAssignment cost σ ↔ OptimalAssignment other σ) :
    firstOptimalAssignment cost = firstOptimalAssignment other := by
  classical
  unfold firstOptimalAssignment
  congr 1
  exact Nat.find_congr' (h _)

/-- Measurable edge costs give a measurable minimum, without any uniqueness hypothesis. -/
theorem measurable_firstOptimalAssignment {α : Type*} [MeasurableSpace α]
    [MeasurableSpace (Assignment n)] (cost : α → Fin n → Fin n → ℝ)
    (hcost : ∀ i j, Measurable (fun x ↦ cost x i j)) :
    Measurable (fun x ↦ firstOptimalAssignment (cost x)) := by
  classical
  have hm (k : ℕ) : MeasurableSet
      {x : α | OptimalAssignment (cost x) (assignmentEnumeration n k)} := by
    simp only [OptimalAssignment, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro τ
    apply measurableSet_le <;> unfold assignmentCost
    · exact Finset.measurable_sum _ (fun i _ ↦ hcost i _)
    · exact Finset.measurable_sum _ (fun i _ ↦ hcost i _)
  exact (measurable_of_countable (assignmentEnumeration n)).comp
    (measurable_find (fun x ↦ exists_optimalAssignment_index (cost x)) hm)

/-- A measurable family always admits an everywhere measurable exact minimizing assignment. -/
theorem exists_measurable_optimalAssignment {α : Type*} [MeasurableSpace α]
    [MeasurableSpace (Assignment n)] (cost : α → Fin n → Fin n → ℝ)
    (hcost : ∀ i j, Measurable (fun x ↦ cost x i j)) :
    ∃ f : α → Assignment n, Measurable f ∧ ∀ x, OptimalAssignment (cost x) (f x) :=
  ⟨fun x ↦ firstOptimalAssignment (cost x), measurable_firstOptimalAssignment cost hcost,
    fun x ↦ firstOptimalAssignment_isOptimal (cost x)⟩

/-- Scaling and adding one term per row and column gives a permutation-independent offset. -/
theorem assignmentCost_scale_add_rowColumn (cost : Fin n → Fin n → ℝ)
    (k : ℝ) (row column : Fin n → ℝ) (σ : Assignment n) :
    assignmentCost (fun i j ↦ k * cost i j + row i + column j) σ =
      k * assignmentCost cost σ + ∑ i, row i + ∑ j, column j := by
  simp only [assignmentCost, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Equiv.sum_comp σ column]

/-- Positive scaling and row-column additions preserve every optimal permutation. -/
theorem optimalAssignment_posScale_add_rowColumn_iff (cost : Fin n → Fin n → ℝ)
    (k : ℝ) (hk : 0 < k) (row column : Fin n → ℝ) (σ : Assignment n) :
    OptimalAssignment (fun i j ↦ k * cost i j + row i + column j) σ ↔
      OptimalAssignment cost σ := by
  simp only [OptimalAssignment, assignmentCost_scale_add_rowColumn,
    add_le_add_iff_right, mul_le_mul_iff_right₀ hk]

/-- The fixed tie rule also commutes exactly with positive scaling and row-column additions. -/
theorem firstOptimalAssignment_posScale_add_rowColumn (cost : Fin n → Fin n → ℝ)
    (k : ℝ) (hk : 0 < k) (row column : Fin n → ℝ) :
    firstOptimalAssignment (fun i j ↦ k * cost i j + row i + column j) =
      firstOptimalAssignment cost :=
  firstOptimalAssignment_eq_of_optimal_iff _ _
    (optimalAssignment_posScale_add_rowColumn_iff cost k hk row column)

namespace FiniteSample

/-- An arbitrary measurable edge-cost family can use the same deterministic tie rule. -/
noncomputable def costOptimizer (sample : FiniteSample n)
    (cost : FiniteSample n → Fin n → Fin n → ℝ) : Assignment n :=
  firstOptimalAssignment (cost sample)

theorem costOptimizer_isOptimal (sample : FiniteSample n)
    (cost : FiniteSample n → Fin n → Fin n → ℝ) :
    OptimalAssignment (cost sample) (sample.costOptimizer cost) :=
  firstOptimalAssignment_isOptimal (cost sample)

theorem measurable_costOptimizer [MeasurableSpace (Assignment n)]
    (cost : FiniteSample n → Fin n → Fin n → ℝ)
    (hcost : ∀ i j, Measurable (fun sample ↦ cost sample i j)) :
    Measurable (fun sample : FiniteSample n ↦ sample.costOptimizer cost) :=
  measurable_firstOptimalAssignment cost hcost

/-- The perspective cost `D L(δ / D)`, where `δ = S - T` is signed. -/
noncomputable def slopeProfileEdgeCost (sample : FiniteSample n) (L : ℝ → ℝ)
    (i j : Fin n) : ℝ :=
  sample.horizontalGap i j *
    L (((sample.targetHeight j : ℝ) - sample.sourceHeight i) / sample.horizontalGap i j)

theorem measurable_slopeProfileEdgeCost (L : ℝ → ℝ) (hL : Measurable L) (i j : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.slopeProfileEdgeCost L i j) := by
  have hD : Measurable (fun sample : FiniteSample n ↦ sample.horizontalGap i j) := by
    unfold horizontalGap
    fun_prop
  exact hD.mul (hL.comp (((measurable_targetHeight j).subtype_val.sub
    (measurable_sourceHeight i).subtype_val).div hD))

/-- Exact edgewise identity underlying the norm's affine subtraction and curvature scaling. -/
theorem slopeProfileEdgeCost_normalization (sample : FiniteSample n) (ψ : ℝ → ℝ)
    (k a b : ℝ) (hk : k ≠ 0) :
    sample.slopeProfileEdgeCost ψ =
      fun i j ↦ k * sample.slopeProfileEdgeCost (fun z ↦ (ψ z - a - b * z) / k) i j +
        (-a * (sample.sourceMark i : ℝ) - b * sample.sourceHeight i) +
        (a * (2 + (sample.targetMark j : ℝ)) + b * sample.targetHeight j) := by
  funext i j
  have hD : sample.horizontalGap i j ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (sample.horizontalGap_mem i j).1)
  dsimp only [slopeProfileEdgeCost]
  field_simp
  dsimp [horizontalGap] at *
  nlinarith [mul_ne_zero hk hD]

/-- The full norm objective and its normalized profile have identical finite optimal sets. -/
theorem optimalAssignment_slopeProfile_normalization_iff (sample : FiniteSample n)
    (ψ : ℝ → ℝ) (k a b : ℝ) (hk : 0 < k) (σ : Assignment n) :
    OptimalAssignment (sample.slopeProfileEdgeCost ψ) σ ↔
      OptimalAssignment
        (sample.slopeProfileEdgeCost (fun z ↦ (ψ z - a - b * z) / k)) σ := by
  rw [sample.slopeProfileEdgeCost_normalization ψ k a b (ne_of_gt hk)]
  exact optimalAssignment_posScale_add_rowColumn_iff _ k hk _ _ σ

/-- Exact normalization preserves the selected permutation even when the minimum has ties. -/
theorem firstOptimalAssignment_slopeProfile_normalization (sample : FiniteSample n)
    (ψ : ℝ → ℝ) (k a b : ℝ) (hk : 0 < k) :
    firstOptimalAssignment (sample.slopeProfileEdgeCost ψ) =
      firstOptimalAssignment
        (sample.slopeProfileEdgeCost (fun z ↦ (ψ z - a - b * z) / k)) :=
  firstOptimalAssignment_eq_of_optimal_iff _ _
    (sample.optimalAssignment_slopeProfile_normalization_iff ψ k a b hk)

end FiniteSample

end OTSelector
