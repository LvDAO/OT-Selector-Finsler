import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.Assignment
import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.PerturbedValue

/-!
# Finite.CapacityAssignment

**Conditions:** Finite target labels have integer quotas summing to the number of sources; positivity is assumed when a distinguished slot for each target is needed.

**Objects:** Quota-feasible allocations, repeated target slots, actual target-vacancy values and label-level cavity partner scores.

**Proof detail:** Identify each quota allocation with a permutation of repeated slots; delete one source and one slot, transfer attained minima both ways, and prove equal labels have identical cavity objectives and prices.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Integer quota problems are encoded as the usual finite assignment problem by repeated slots. The exact vacancy prices, row-update invariance and measurable finite-minimum statements are derived in the source.
-/

/-!
# Integer-capacity assignments and their exact cavities

Integer target capacities are represented by labelled slots. Every feasible label allocation
lifts to a slot permutation, and all optimal allocations are characterized by the corresponding
assignment optima. Deleting one source removes exactly one unit from its partner's capacity.
The cavity price depends only on the target label, even when repeated slots force ties.
These are finite combinatorial facts; no target-tree or Dirichlet distribution is asserted.
-/

open scoped BigOperators

namespace OTSelector

variable {ι α : Type*} [Fintype ι] [DecidableEq α] {n : ℕ}

/-- A label allocation uses exactly the prescribed integer capacities. -/
def CapacityFeasible (r : α → ℕ) (a : ι → α) : Prop :=
  ∀ j, Fintype.card {i // a i = j} = r j

/-- The actual total cost of a source-to-label allocation. -/
def capacityAssignmentCost (cost : ι → α → ℝ) (a : ι → α) : ℝ :=
  ∑ i, cost i (a i)

/-- Optimality among all allocations with the specified integer capacities. -/
def OptimalCapacityAssignment (r : α → ℕ) (cost : ι → α → ℝ) (a : ι → α) : Prop :=
  CapacityFeasible r a ∧
    ∀ b, CapacityFeasible r b → capacityAssignmentCost cost a ≤ capacityAssignmentCost cost b

/-- Enumerate the actual repeated slots of an integer-capacity vector. -/
noncomputable def capacitySlotEquiv [Fintype α] (r : α → ℕ) (h : ∑ j, r j = n) :
    Fin n ≃ (Σ j, Fin (r j)) :=
  Fintype.equivOfCardEq (by simpa using h.symm)

/-- The label carried by each enumerated slot. -/
noncomputable def capacitySlotLabel [Fintype α] (r : α → ℕ) (h : ∑ j, r j = n) :
    Fin n → α := fun s ↦ (capacitySlotEquiv r h s).1

/-- The repeated-slot construction realizes the requested capacities, including zero capacities. -/
theorem capacitySlotLabel_feasible [Fintype α] (r : α → ℕ) (h : ∑ j, r j = n) :
    CapacityFeasible r (capacitySlotLabel r h) := by
  intro j
  let e := (capacitySlotEquiv r h).subtypeEquiv
    (p := fun s ↦ capacitySlotLabel r h s = j) (q := fun s ↦ s.1 = j)
    (fun _ ↦ Iff.rfl)
  exact (Fintype.card_congr (e.trans (Equiv.sigmaSubtype j))).trans (Fintype.card_fin _)

/-- Relabelling the sources by a permutation preserves every target count. -/
theorem capacityFeasible_comp_perm (r : α → ℕ) (target : Fin n → α)
    (ht : CapacityFeasible r target) (σ : Assignment n) :
    CapacityFeasible r (target ∘ σ) := by
  intro j
  exact (Fintype.card_congr (σ.subtypeEquiv (p := fun i ↦ target (σ i) = j)
    (q := fun s ↦ target s = j) (fun _ ↦ Iff.rfl))).trans (ht j)

/-- Every feasible allocation is the projection of a slot permutation.
Repeated labels are allowed. -/
theorem capacityFeasible_iff_exists_perm (r : α → ℕ) (target a : Fin n → α)
    (ht : CapacityFeasible r target) :
    CapacityFeasible r a ↔ ∃ σ : Assignment n, ∀ i, target (σ i) = a i := by
  constructor
  · intro ha
    let e (j : α) : {i // a i = j} ≃ {s // target s = j} :=
      Fintype.equivOfCardEq ((ha j).trans (ht j).symm)
    exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  · rintro ⟨σ, hσ⟩
    have heq : a = target ∘ σ := (funext hσ).symm
    rw [heq]
    exact capacityFeasible_comp_perm r target ht σ

omit [DecidableEq α] in
/-- Label projection preserves the total assignment cost exactly. -/
theorem capacityAssignmentCost_comp (cost : Fin n → α → ℝ) (target : Fin n → α)
    (σ : Assignment n) :
    capacityAssignmentCost cost (target ∘ σ) =
      assignmentCost (fun i s ↦ cost i (target s)) σ := rfl

/-- Slot expansion identifies the entire optimal allocation set, without choosing among ties. -/
theorem optimalCapacityAssignment_iff (r : α → ℕ) (cost : Fin n → α → ℝ)
    (target : Fin n → α) (ht : CapacityFeasible r target) (σ : Assignment n) :
    OptimalCapacityAssignment r cost (target ∘ σ) ↔
      OptimalAssignment (fun i s ↦ cost i (target s)) σ := by
  constructor
  · rintro ⟨_, hσ⟩ τ
    exact hσ _ (capacityFeasible_comp_perm r target ht τ)
  · intro hσ
    refine ⟨capacityFeasible_comp_perm r target ht σ, ?_⟩
    intro b hb
    obtain ⟨τ, hτ⟩ := (capacityFeasible_iff_exists_perm r target b ht).mp hb
    have heq : b = target ∘ τ := (funext hτ).symm
    rw [heq]
    exact hσ τ

/-- Every capacity problem whose total count is the source count has an actual optimum. -/
theorem exists_optimalCapacityAssignment [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n) (cost : Fin n → α → ℝ) :
    ∃ a, OptimalCapacityAssignment r cost a := by
  let target := capacitySlotLabel r h
  let c := fun i s ↦ cost i (target s)
  refine ⟨target ∘ optimalAssignment c, ?_⟩
  exact (optimalCapacityAssignment_iff r cost target (capacitySlotLabel_feasible r h)
    (optimalAssignment c)).mpr (optimalAssignment_isOptimal c)

/-- Removing one unit at target `j` gives the retained-source capacity vector. -/
def capacityDeficit (r : α → ℕ) (j : α) : α → ℕ :=
  fun k ↦ r k - if k = j then 1 else 0

private theorem card_fiber_eq_sum (a : ι → α) (j : α) :
    Fintype.card {i // a i = j} = ∑ i, if a i = j then 1 else 0 := by
  simp [Fintype.card_subtype, Finset.sum_boole]

/-- Deleting a source leaves exactly one unit vacant at its actual target. -/
theorem capacityFeasible_delete (r : α → ℕ) (a : Fin (n + 1) → α)
    (ha : CapacityFeasible r a) (i : Fin (n + 1)) :
    CapacityFeasible (capacityDeficit r (a i)) (fun k ↦ a (i.succAbove k)) := by
  intro j
  have hj := ha j
  rw [card_fiber_eq_sum, Fin.sum_univ_succAbove _ i] at hj
  rw [card_fiber_eq_sum]
  dsimp [capacityDeficit]
  by_cases h : a i = j
  · simp only [h, ↓reduceIte] at hj ⊢
    omega
  · have h' : j ≠ a i := Ne.symm h
    simp only [h, h', ↓reduceIte, zero_add, Nat.sub_zero] at hj ⊢
    exact hj

private theorem slotValue_eq (cost : Fin n → Fin n → ℝ) :
    perturbedAssignmentValue cost 0 0 = assignmentCost cost (optimalAssignment cost) := by
  have h := perturbedAssignmentValue_eq_of_optimal cost 0 0 (optimalAssignment cost)
    (by rw [perturbedEdgeCost_zero cost 0]; exact optimalAssignment_isOptimal cost)
  simpa only [perturbedEdgeCost_zero cost 0] using h

private theorem slotValue_le (cost : Fin n → Fin n → ℝ) (σ : Assignment n) :
    perturbedAssignmentValue cost 0 0 ≤ assignmentCost cost σ := by
  simpa only [perturbedEdgeCost_zero cost 0] using perturbedAssignmentValue_le cost 0 0 σ

/-- A repeated-slot cavity value is attained by an actual allocation with one-unit deficit. -/
theorem assignmentCavityValue_capacity_attained (r : α → ℕ)
    (cost : Fin (n + 1) → α → ℝ) (target : Fin (n + 1) → α)
    (ht : CapacityFeasible r target) (i s : Fin (n + 1)) :
    ∃ a : Fin n → α, CapacityFeasible (capacityDeficit r (target s)) a ∧
      capacityAssignmentCost (fun k j ↦ cost (i.succAbove k) j) a =
        assignmentCavityValue (fun k t ↦ cost k (target t)) i s := by
  let t : Fin n → α := fun l ↦ target (s.succAbove l)
  let c := assignmentCavityCost (fun k t ↦ cost k (target t)) i s
  refine ⟨t ∘ optimalAssignment c,
    capacityFeasible_comp_perm _ t (capacityFeasible_delete r target ht s) _, ?_⟩
  exact (slotValue_eq c).symm

/-- The cavity value is bounded by every feasible allocation with the same one-unit deficit. -/
theorem assignmentCavityValue_le_capacity_cost (r : α → ℕ)
    (cost : Fin (n + 1) → α → ℝ) (target : Fin (n + 1) → α)
    (ht : CapacityFeasible r target) (i s : Fin (n + 1)) (a : Fin n → α)
    (ha : CapacityFeasible (capacityDeficit r (target s)) a) :
    assignmentCavityValue (fun k t ↦ cost k (target t)) i s ≤
      capacityAssignmentCost (fun k j ↦ cost (i.succAbove k) j) a := by
  obtain ⟨τ, hτ⟩ := (capacityFeasible_iff_exists_perm _
    (fun l ↦ target (s.succAbove l)) a (capacityFeasible_delete r target ht s)).mp ha
  have heq : a = (fun l ↦ target (s.succAbove l)) ∘ τ := (funext hτ).symm
  rw [heq]
  exact slotValue_le (assignmentCavityCost (fun k t ↦ cost k (target t)) i s) τ

/-- All slots with the same target label have identical actual vacancy prices. -/
theorem assignmentCavityValue_eq_of_same_label (r : α → ℕ)
    (cost : Fin (n + 1) → α → ℝ) (target : Fin (n + 1) → α)
    (ht : CapacityFeasible r target) (i s t : Fin (n + 1)) (hst : target s = target t) :
    assignmentCavityValue (fun k u ↦ cost k (target u)) i s =
      assignmentCavityValue (fun k u ↦ cost k (target u)) i t := by
  apply le_antisymm
  · obtain ⟨a, ha, hcost⟩ := assignmentCavityValue_capacity_attained r cost target ht i t
    rw [← hcost]
    exact assignmentCavityValue_le_capacity_cost r cost target ht i s a (hst ▸ ha)
  · obtain ⟨a, ha, hcost⟩ := assignmentCavityValue_capacity_attained r cost target ht i s
    rw [← hcost]
    exact assignmentCavityValue_le_capacity_cost r cost target ht i t a (hst ▸ ha)

/-- Every minimizing label and only such a label occurs in some optimal capacity allocation. -/
theorem exists_optimalCapacityAssignment_partner_iff (r : α → ℕ)
    (cost : Fin (n + 1) → α → ℝ) (target : Fin (n + 1) → α)
    (ht : CapacityFeasible r target) (i s : Fin (n + 1)) :
    (∃ a, OptimalCapacityAssignment r cost a ∧ a i = target s) ↔
      ∀ t, assignmentRowEnvelope (fun k u ↦ cost k (target u)) i s ≤
        assignmentRowEnvelope (fun k u ↦ cost k (target u)) i t := by
  constructor
  · rintro ⟨a, ha, hai⟩
    obtain ⟨σ, hσ⟩ := (capacityFeasible_iff_exists_perm r target a ht).mp ha.1
    have heq : a = target ∘ σ := (funext hσ).symm
    have hopt := (optimalCapacityAssignment_iff r cost target ht σ).mp (heq ▸ ha)
    have hlabel : target (σ i) = target s := (hσ i).trans hai
    have hp := (optimalAssignment_iff_cavity _ σ i).mp hopt |>.2
    have hv := assignmentCavityValue_eq_of_same_label r cost target ht i (σ i) s hlabel
    simpa only [assignmentRowEnvelope, hlabel, hv] using hp
  · intro hs
    obtain ⟨σ, hσ, hsi⟩ := (exists_optimalAssignment_partner_iff _ i s).mpr hs
    refine ⟨target ∘ σ, (optimalCapacityAssignment_iff r cost target ht σ).mpr hσ, ?_⟩
    exact congrArg target hsi

/-- Restricting any optimal capacity allocation gives an optimum for its actual vacancy. -/
theorem optimalCapacityAssignment_delete (r : α → ℕ)
    (cost : Fin (n + 1) → α → ℝ) (a : Fin (n + 1) → α)
    (ha : OptimalCapacityAssignment r cost a) (i : Fin (n + 1)) :
    OptimalCapacityAssignment (capacityDeficit r (a i))
      (fun k j ↦ cost (i.succAbove k) j) (fun k ↦ a (i.succAbove k)) := by
  let target := a
  have ht : CapacityFeasible r target := ha.1
  obtain ⟨σ, hσ⟩ := (capacityFeasible_iff_exists_perm r target a ht).mp ha.1
  have heq : a = target ∘ σ := (funext hσ).symm
  have hopt := (optimalCapacityAssignment_iff r cost target ht σ).mp (heq ▸ ha)
  have hrest := optimalAssignment_restrictAssignment _ σ hopt i
  have hcap := (optimalCapacityAssignment_iff (capacityDeficit r (target (σ i)))
    (fun k j ↦ cost (i.succAbove k) j) (fun l ↦ target ((σ i).succAbove l))
    (capacityFeasible_delete r target ht (σ i)) (restrictAssignment σ i)).mpr hrest
  have hfunc : ((fun l ↦ target ((σ i).succAbove l)) ∘ restrictAssignment σ i) =
      (fun k ↦ a (i.succAbove k)) := by
    funext k
    simp only [Function.comp_apply, restrictAssignment_succAbove, hσ]
  rw [hfunc, hσ i] at hcap
  exact hcap

/-- A representative slot for a target of positive capacity. -/
noncomputable def capacityLabelSlot [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n) (j : α) (hj : 0 < r j) : Fin n :=
  (capacitySlotEquiv r h).symm ⟨j, ⟨0, hj⟩⟩

omit [DecidableEq α] in
@[simp]
theorem capacitySlotLabel_labelSlot [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n) (j : α) (hj : 0 < r j) :
    capacitySlotLabel r h (capacityLabelSlot r h j hj) = j := by
  simp [capacitySlotLabel, capacityLabelSlot]

/-- The attained remainder price for leaving one unit vacant at the indicated target. -/
noncomputable def capacityVacancyPrice [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n + 1) (cost : Fin (n + 1) → α → ℝ)
    (i : Fin (n + 1)) (j : α) (hj : 0 < r j) : ℝ :=
  assignmentCavityValue (fun k s ↦ cost k (capacitySlotLabel r h s)) i
    (capacityLabelSlot r h j hj)

/-- The label price is exactly the minimum over every allocation with the specified deficit. -/
theorem capacityVacancyPrice_spec [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n + 1) (cost : Fin (n + 1) → α → ℝ)
    (i : Fin (n + 1)) (j : α) (hj : 0 < r j) :
    (∃ a : Fin n → α, CapacityFeasible (capacityDeficit r j) a ∧
      capacityAssignmentCost (fun k l ↦ cost (i.succAbove k) l) a =
        capacityVacancyPrice r h cost i j hj) ∧
    (∀ a : Fin n → α, CapacityFeasible (capacityDeficit r j) a →
      capacityVacancyPrice r h cost i j hj ≤
        capacityAssignmentCost (fun k l ↦ cost (i.succAbove k) l) a) := by
  constructor
  · simpa only [capacitySlotLabel_labelSlot, capacityVacancyPrice] using
      assignmentCavityValue_capacity_attained r cost (capacitySlotLabel r h)
        (capacitySlotLabel_feasible r h) i (capacityLabelSlot r h j hj)
  · intro a ha
    apply assignmentCavityValue_le_capacity_cost r cost (capacitySlotLabel r h)
      (capacitySlotLabel_feasible r h) i (capacityLabelSlot r h j hj) a
    simpa only [capacitySlotLabel_labelSlot] using ha

/-- The label cell criterion characterizes all possible optimal partners, including all ties. -/
theorem exists_optimalCapacityAssignment_label_iff [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j) (cost : Fin (n + 1) → α → ℝ)
    (i : Fin (n + 1)) (j : α) :
    (∃ a, OptimalCapacityAssignment r cost a ∧ a i = j) ↔
      ∀ k, cost i j + capacityVacancyPrice r h cost i j (hr j) ≤
        cost i k + capacityVacancyPrice r h cost i k (hr k) := by
  let target := capacitySlotLabel r h
  let c := fun k s ↦ cost k (target s)
  have henv (s : Fin (n + 1)) : assignmentRowEnvelope c i s =
      cost i (target s) + capacityVacancyPrice r h cost i (target s) (hr (target s)) := by
    unfold assignmentRowEnvelope capacityVacancyPrice
    congr 1
    exact assignmentCavityValue_eq_of_same_label r cost target
      (capacitySlotLabel_feasible r h) i s (capacityLabelSlot r h (target s) (hr _))
      (capacitySlotLabel_labelSlot r h (target s) (hr _)).symm
  have hs := exists_optimalCapacityAssignment_partner_iff r cost target
    (capacitySlotLabel_feasible r h) i (capacityLabelSlot r h j (hr j))
  simp only [target, capacitySlotLabel_labelSlot] at hs
  rw [hs]
  change (∀ t, assignmentRowEnvelope c i (capacityLabelSlot r h j (hr j)) ≤
    assignmentRowEnvelope c i t) ↔ _
  simp only [henv, target, capacitySlotLabel_labelSlot]
  constructor
  · intro hmin k
    simpa only [capacitySlotLabel_labelSlot] using hmin (capacityLabelSlot r h k (hr k))
  · intro hmin t
    exact hmin (capacitySlotLabel r h t)

/-- Every optimal allocation chooses a minimizing cavity label.
The assertion includes all optima. -/
theorem optimalCapacityAssignment_cavity_min [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j) (cost : Fin (n + 1) → α → ℝ)
    (a : Fin (n + 1) → α) (ha : OptimalCapacityAssignment r cost a) (i : Fin (n + 1)) :
    ∀ k, cost i (a i) + capacityVacancyPrice r h cost i (a i) (hr (a i)) ≤
      cost i k + capacityVacancyPrice r h cost i k (hr k) :=
  (exists_optimalCapacityAssignment_label_iff r h hr cost i (a i)).mp ⟨a, ha, rfl⟩

omit [DecidableEq α] in
/-- Inserting any new source row leaves every actual capacity vacancy price unchanged. -/
@[simp]
theorem capacityVacancyPrice_update_row [Fintype α] (r : α → ℕ)
    (h : ∑ j, r j = n + 1) (cost : Fin (n + 1) → α → ℝ)
    (i : Fin (n + 1)) (row : α → ℝ) (j : α) (hj : 0 < r j) :
    capacityVacancyPrice r h (Function.update cost i row) i j hj =
      capacityVacancyPrice r h cost i j hj := by
  apply assignmentCavityValue_congr_off_row
  intro k hk s
  simp only [Function.update_of_ne hk]

omit [DecidableEq α] in
/-- Capacity vacancy prices are measurable functions of any measurable retained cost matrix. -/
theorem measurable_capacityVacancyPrice {Ω : Type*} [MeasurableSpace Ω] [Fintype α]
    (r : α → ℕ) (h : ∑ j, r j = n + 1) (cost : Ω → Fin (n + 1) → α → ℝ)
    (hcost : ∀ k j, Measurable (fun ω ↦ cost ω k j))
    (i : Fin (n + 1)) (j : α) (hj : 0 < r j) :
    Measurable (fun ω ↦ capacityVacancyPrice r h (cost ω) i j hj) :=
  measurable_assignmentCavityValue _ (fun k s ↦ hcost k (capacitySlotLabel r h s)) i
    (capacityLabelSlot r h j hj)

end OTSelector
