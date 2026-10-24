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
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.Assignment
import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.AssignmentDual
import OTSelector.Finite.CapacityAssignment

/-!
# Finite.CapacityCalibration

**Conditions:** Finite target labels, positive integer quotas totaling n+1, and one removed source.

**Objects:** Common quota-vacancy row potentials and exact dual attainment for every missing target.

**Proof detail:** Project the already constructed slot dual to repeated target labels; feasibility and tightness persist, and quota-weighted summation yields each vacancy price and the common balance identity.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# One actual vacancy dual for all integer-capacity remainders

The row potentials are the minima of the original costs plus the actual capacity vacancy
prices. They calibrate every optimal retained allocation for every possible missing target.
The construction projects the already proved slot cavity dual, retaining the original label
capacities and costs. No uniqueness, common-dual premise, or population balancing is assumed.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- The common row potential from the actual label vacancy prices. -/
def capacityVacancyRowPotential (r : α → ℕ) (htotal : ∑ j, r j = n + 1)
    (hr : ∀ j, 0 < r j) (cost : Fin (n + 1) → α → ℝ) (i₀ k : Fin (n + 1)) : ℝ :=
  ⨅ j, cost k j + capacityVacancyPrice r htotal cost i₀ j (hr j)

/-- Every slot vacancy price is the price of its actual target label. -/
theorem assignmentCavityValue_eq_capacityVacancyPrice
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ s : Fin (n + 1)) :
    assignmentCavityValue (fun k t ↦ cost k (capacitySlotLabel r htotal t)) i₀ s =
      capacityVacancyPrice r htotal cost i₀ (capacitySlotLabel r htotal s)
        (hr (capacitySlotLabel r htotal s)) := by
  apply assignmentCavityValue_eq_of_same_label r cost (capacitySlotLabel r htotal)
    (capacitySlotLabel_feasible r htotal)
  exact (capacitySlotLabel_labelSlot r htotal _ _).symm

/-- Taking the minimum over slots gives exactly the minimum over target labels. -/
theorem capacityVacancyRowPotential_eq_slot
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ k : Fin (n + 1)) :
    capacityVacancyRowPotential r htotal hr cost i₀ k =
      cavityRowPotential (fun k t ↦ cost k (capacitySlotLabel r htotal t)) i₀ k := by
  have : Nonempty α := ⟨capacitySlotLabel r htotal 0⟩
  unfold capacityVacancyRowPotential cavityRowPotential
  simp_rw [assignmentCavityValue_eq_capacityVacancyPrice r htotal hr]
  apply le_antisymm
  · apply le_ciInf
    intro s
    exact ciInf_le (Set.finite_range _).bddBelow (capacitySlotLabel r htotal s)
  · apply le_ciInf
    intro j
    have h := ciInf_le (Set.finite_range (fun s ↦ cost k (capacitySlotLabel r htotal s) +
      capacityVacancyPrice r htotal cost i₀ (capacitySlotLabel r htotal s)
        (hr (capacitySlotLabel r htotal s)))).bddBelow
      (capacityLabelSlot r htotal j (hr j))
    simpa only [capacitySlotLabel_labelSlot] using h

omit [DecidableEq α] in
/-- The actual common capacity potentials satisfy every original cost inequality. -/
theorem capacityVacancyPotentials_feasible
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ k : Fin (n + 1)) (j : α) :
    capacityVacancyRowPotential r htotal hr cost i₀ k -
      capacityVacancyPrice r htotal cost i₀ j (hr j) ≤ cost k j := by
  have h := ciInf_le (Set.finite_range
    (fun j ↦ cost k j + capacityVacancyPrice r htotal cost i₀ j (hr j))).bddBelow j
  change capacityVacancyRowPotential r htotal hr cost i₀ k ≤ _ at h
  linarith

private theorem restrict_insert (i j : Fin (n + 1)) (τ : Assignment n) :
    restrictAssignment (insertAssignment i j τ) i = τ := by
  apply Equiv.ext
  intro k
  apply Fin.succAbove_right_injective (p := j)
  have h := restrictAssignment_succAbove (insertAssignment i j τ) i k
  simpa only [insertAssignment_at, insertAssignment_succAbove] using h

/-- Every optimal quota remainder is tight for the same actual vacancy-price potentials,
simultaneously for all possible missing target labels. -/
theorem capacityVacancyPotentials_tight_of_optimal
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (j : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r j)
      (fun k l ↦ cost (i₀.succAbove k) l) a) (k : Fin n) :
    capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ (a k) (hr (a k)) =
        cost (i₀.succAbove k) (a k) := by
  let target := capacitySlotLabel r htotal
  let s := capacityLabelSlot r htotal j (hr j)
  let t : Fin n → α := fun l ↦ target (s.succAbove l)
  have ht : CapacityFeasible (capacityDeficit r j) t := by
    simpa only [t, target, s, capacitySlotLabel_labelSlot] using
      capacityFeasible_delete r target (capacitySlotLabel_feasible r htotal) s
  obtain ⟨τ, hτ⟩ := (capacityFeasible_iff_exists_perm (capacityDeficit r j) t a ht).mp ha.1
  have hae : a = t ∘ τ := (funext hτ).symm
  have hτopt := (optimalCapacityAssignment_iff (capacityDeficit r j)
    (fun k l ↦ cost (i₀.succAbove k) l) t ht τ).mp (hae ▸ ha)
  let c := fun k u ↦ cost k (target u)
  have hrest : OptimalAssignment (assignmentCavityCost c i₀
      (insertAssignment i₀ s τ i₀)) (restrictAssignment (insertAssignment i₀ s τ) i₀) := by
    rw [insertAssignment_at, restrict_insert]
    exact hτopt
  have hh := cavityPotentials_tight_of_restrict_optimal c i₀ (insertAssignment i₀ s τ)
    hrest (i₀.succAbove k) (i₀.succAbove_ne k)
  rw [insertAssignment_succAbove] at hh
  rw [capacityVacancyRowPotential_eq_slot]
  change cavityRowPotential c i₀ (i₀.succAbove k) - _ = _
  have hp := assignmentCavityValue_eq_capacityVacancyPrice r htotal hr cost i₀
    (s.succAbove (τ k))
  have htk : target (s.succAbove (τ k)) = a k := hτ k
  change assignmentCavityValue c i₀ (s.succAbove (τ k)) =
    capacityVacancyPrice r htotal cost i₀ (target (s.succAbove (τ k))) _ at hp
  change cavityRowPotential c i₀ (i₀.succAbove k) -
    assignmentCavityValue c i₀ (s.succAbove (τ k)) =
      cost (i₀.succAbove k) (target (s.succAbove (τ k))) at hh
  rw [hp] at hh
  simpa only [htk] using hh

/-- A capacity-feasible allocation sums any target quantity with the prescribed multiplicities. -/
theorem capacityFeasible_sum_weighted {ι : Type*} [Fintype ι]
    (r : α → ℕ) (a : ι → α) (ha : CapacityFeasible r a) (v : α → ℝ) :
    (∑ k, v (a k)) = ∑ j, (r j : ℝ) * v j := by
  rw [← Fintype.sum_fiberwise' a v]
  apply Finset.sum_congr rfl
  intro j _
  simp [ha j, nsmul_eq_mul]

/-- Tightness for the actual common vacancy potentials characterizes the complete set of
optimal quota allocations; no choice of a preferred optimizer appears. -/
theorem optimalCapacityAssignment_iff_capacityVacancyPotentials_tight
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (j : α) (a : Fin n → α) :
    OptimalCapacityAssignment (capacityDeficit r j)
      (fun k l ↦ cost (i₀.succAbove k) l) a ↔
      CapacityFeasible (capacityDeficit r j) a ∧ ∀ k,
        capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
          capacityVacancyPrice r htotal cost i₀ (a k) (hr (a k)) =
            cost (i₀.succAbove k) (a k) := by
  constructor
  · intro ha
    exact ⟨ha.1, capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ j a ha⟩
  · rintro ⟨ha, ht⟩
    refine ⟨ha, ?_⟩
    intro b hb
    have hs : (∑ k, capacityVacancyPrice r htotal cost i₀ (a k) (hr (a k))) =
        ∑ k, capacityVacancyPrice r htotal cost i₀ (b k) (hr (b k)) := by
      let v := fun l ↦ capacityVacancyPrice r htotal cost i₀ l (hr l)
      exact (capacityFeasible_sum_weighted _ a ha v).trans
        (capacityFeasible_sum_weighted _ b hb v).symm
    unfold capacityAssignmentCost
    simp_rw [← ht]
    rw [Finset.sum_sub_distrib, hs, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k _ ↦
      capacityVacancyPotentials_feasible r htotal hr cost i₀ (i₀.succAbove k) (b k)

/-- The same actual potentials attain the value of every one-unit capacity deficit. -/
theorem capacityVacancyPotentials_attain_each_vacancy
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (j : α) :
    capacityVacancyPrice r htotal cost i₀ j (hr j) =
      (∑ k : Fin n, capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k)) -
        ∑ l, (capacityDeficit r j l : ℝ) * capacityVacancyPrice r htotal cost i₀ l (hr l) := by
  have hs := capacityVacancyPrice_spec r htotal cost i₀ j (hr j)
  obtain ⟨a, ha, hv⟩ := hs.1
  have hopt : OptimalCapacityAssignment (capacityDeficit r j)
      (fun k l ↦ cost (i₀.succAbove k) l) a :=
    ⟨ha, fun b hb ↦ hv ▸ hs.2 b hb⟩
  have ht := capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ j a hopt
  rw [← hv]
  unfold capacityAssignmentCost
  simp_rw [← ht]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact capacityFeasible_sum_weighted _ a ha
    (fun l ↦ capacityVacancyPrice r htotal cost i₀ l (hr l))

/-- Removing one positive-capacity unit subtracts exactly its target weight. -/
theorem capacityDeficit_sum_weighted
    (r : α → ℕ) (j : α) (hj : 0 < r j) (v : α → ℝ) :
    (∑ l, (capacityDeficit r j l : ℝ) * v l) = (∑ l, (r l : ℝ) * v l) - v j := by
  have heq (l : α) : (capacityDeficit r j l : ℝ) * v l =
      (r l : ℝ) * v l - if l = j then v j else 0 := by
    by_cases hl : l = j
    · subst l
      simp only [capacityDeficit, ↓reduceIte, Nat.cast_sub (Nat.one_le_of_lt hj), Nat.cast_one]
      ring
    · simp [capacityDeficit, hl]
  simp_rw [heq]
  rw [Finset.sum_sub_distrib]
  simp

/-- The common tight rows have total shifted value `∑ rⱼ Rⱼ`, as required by the
capacitated target-tree argument. The prices are the actual attained vacancy minima. -/
theorem capacityVacancyPotentials_balance
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) :
    (∑ k : Fin n, capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k)) =
      ∑ j, (r j : ℝ) * capacityVacancyPrice r htotal cost i₀ j (hr j) := by
  let j := capacitySlotLabel r htotal 0
  have h := capacityVacancyPotentials_attain_each_vacancy r htotal hr cost i₀ j
  have hs := capacityDeficit_sum_weighted r j (hr j)
    (fun l ↦ capacityVacancyPrice r htotal cost i₀ l (hr l))
  rw [hs] at h
  linarith

end OTSelector
