import OTSelector.Probability.IIDCapacityCostUniqueness
import OTSelector.Finite.CapacityAssignment
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Actual iid capacity allocations have unique optima

An atomless target-cost difference in one source row remains atomless after adding
the independent cost difference of all other original rows. Hence distinct label
allocations have distinct total costs almost surely, simultaneously for every
capacity vector. Repeated slots do not require distinct slot costs: uniqueness
concerns the actual target labels.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace OTSelector.Probability

variable {ι α S Ω : Type*} [Fintype ι] [Fintype α]
  [MeasurableSpace S] [MeasurableSpace Ω]







/-- Every capacity vector of the correct total has a unique actual optimal
label allocation, on a common full-probability event. -/
theorem ae_existsUnique_optimalCapacityAssignment_of_iid_atomless
    {n : ℕ} [DecidableEq α]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : Fin n → Ω → S) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c : α → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun s ↦ c j s - c k s))) :
    ∀ᵐ ω ∂P, ∀ r : α → ℕ, ∑ j, r j = n →
      ∃! a, OptimalCapacityAssignment r (fun i j ↦ c j (X i ω)) a := by
  filter_upwards [ae_injective_capacityAssignmentCost_of_iid_atomless
    P μ X hX hindep hlaw c hc hatom] with ω hω
  intro r hr
  obtain ⟨a, ha⟩ := exists_optimalCapacityAssignment r hr (fun i j ↦ c j (X i ω))
  refine ⟨a, ha, fun b hb ↦ hω ?_⟩
  exact le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)

/-- Deleting any one original source preserves uniqueness for every retained
capacity problem, simultaneously over all deletion positions and capacities. -/
theorem ae_existsUnique_retained_optimalCapacityAssignment_of_iid_atomless
    {n : ℕ} [DecidableEq α]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : Fin (n + 1) → Ω → S) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c : α → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun s ↦ c j s - c k s))) :
    ∀ᵐ ω ∂P, ∀ i : Fin (n + 1), ∀ r : α → ℕ, ∑ j, r j = n →
      ∃! a, OptimalCapacityAssignment r (fun k j ↦ c j (X (i.succAbove k) ω)) a := by
  apply ae_all_iff.mpr
  intro i
  exact ae_existsUnique_optimalCapacityAssignment_of_iid_atomless P μ
    (fun k ↦ X (i.succAbove k)) (fun k ↦ hX (i.succAbove k))
    (hindep.precomp Fin.succAbove_right_injective) (fun k ↦ hlaw (i.succAbove k))
    c hc hatom

/-- The uniqueness premise of the actual target-tree construction follows from
the original iid rows, for all vacancy labels and every capacity vector at once. -/
theorem ae_capacityVacancy_optimizer_unique_of_iid_atomless
    {n : ℕ} [DecidableEq α]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : Fin (n + 1) → Ω → S) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c : α → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun s ↦ c j s - c k s))) :
    ∀ᵐ ω ∂P, ∀ (i : Fin (n + 1)) (r : α → ℕ) (z : α) (a b : Fin n → α),
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun k j ↦ c j (X (i.succAbove k) ω)) a →
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun k j ↦ c j (X (i.succAbove k) ω)) b → a = b := by
  have hinj : ∀ᵐ ω ∂P, ∀ i : Fin (n + 1), Function.Injective
      (capacityAssignmentCost (fun k j ↦ c j (X (i.succAbove k) ω))) := by
    apply ae_all_iff.mpr
    intro i
    exact ae_injective_capacityAssignmentCost_of_iid_atomless P μ
      (fun k ↦ X (i.succAbove k)) (fun k ↦ hX (i.succAbove k))
      (hindep.precomp Fin.succAbove_right_injective) (fun k ↦ hlaw (i.succAbove k))
      c hc hatom
  filter_upwards [hinj] with ω hω
  intro i r z a b ha hb
  exact hω i (le_antisymm (ha.2 b hb.1) (hb.2 a ha.1))

end OTSelector.Probability
