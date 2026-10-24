import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.CapacityCalibration
import OTSelector.Finite.TargetTreeRows

/-!
# Finite.TargetTreeRestriction

**Conditions:** The canonical flexible-row subset is obtained under uniqueness of all quota-vacancy optima.

**Objects:** Reduced unit-capacity vacancy allocations and the common cost of omitted strict rows.

**Proof detail:** Restrict actual optimizers to flexible rows, subtract fixed strict-row counts, and retain tight feasibility for unit quotas; split finite objective sums over the subset and its complement.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (corollary): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Restricting actual quota optima to their canonical tree rows

Deleting the strict rows leaves a unit-capacity vacancy problem. The restrictions of all
actual quota optima solve these reduced problems, and their omitted total cost is the same
for every vacant target. These facts use the already constructed canonical row subset.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A feasible allocation tight for feasible additive potentials is an actual optimum. -/
theorem optimalCapacityAssignment_of_feasible_tight_potentials
    {ι : Type*} [Fintype ι] (r : α → ℕ) (cost : ι → α → ℝ)
    (u : ι → ℝ) (v : α → ℝ) (a : ι → α) (ha : CapacityFeasible r a)
    (hle : ∀ k j, u k - v j ≤ cost k j) (ht : ∀ k, u k - v (a k) = cost k (a k)) :
    OptimalCapacityAssignment r cost a := by
  refine ⟨ha, fun b hb ↦ ?_⟩
  have hs : (∑ k, v (a k)) = ∑ k, v (b k) :=
    (capacityFeasible_sum_weighted r a ha v).trans
      (capacityFeasible_sum_weighted r b hb v).symm
  unfold capacityAssignmentCost
  simp_rw [← ht]
  rw [Finset.sum_sub_distrib, hs, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun k _ ↦ hle k (b k)

omit [Fintype α] in
/-- Changing only the enumeration of source rows preserves the prescribed capacities. -/
theorem capacityFeasible_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : α → ℕ) (a : κ → α) (e : ι ≃ κ) (ha : CapacityFeasible r a) :
    CapacityFeasible r (a ∘ e) := by
  intro j
  exact (Fintype.card_congr (e.subtypeEquiv (p := fun k ↦ a (e k) = j)
    (q := fun k ↦ a k = j) (fun _ ↦ Iff.rfl))).trans (ha j)

omit [Fintype α] [DecidableEq α] in
/-- The actual total allocation cost is unchanged by a bijective source enumeration. -/
theorem capacityAssignmentCost_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (cost : κ → α → ℝ) (a : κ → α) (e : ι ≃ κ) :
    capacityAssignmentCost (fun k j ↦ cost (e k) j) (a ∘ e) =
      capacityAssignmentCost cost a := by
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

omit [Fintype α] in
/-- An actual optimal allocation stays optimal after a bijective source enumeration. -/
theorem optimalCapacityAssignment_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : α → ℕ) (cost : κ → α → ℝ) (a : κ → α) (e : ι ≃ κ)
    (ha : OptimalCapacityAssignment r cost a) :
    OptimalCapacityAssignment r (fun k j ↦ cost (e k) j) (a ∘ e) := by
  refine ⟨capacityFeasible_reindex r a e ha.1, fun b hb ↦ ?_⟩
  have h := ha.2 (b ∘ e.symm) (capacityFeasible_reindex r b e.symm hb)
  rw [capacityAssignmentCost_reindex]
  have heq := capacityAssignmentCost_reindex cost (b ∘ e.symm) e
  have he : (b ∘ e.symm) ∘ e = b := by funext k; simp
  rw [he] at heq
  exact h.trans_eq heq.symm

section Restriction

variable {n : ℕ} (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
  (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α) (a : Fin n → α)
  (ha : OptimalCapacityAssignment (capacityDeficit r root)
    (fun s j ↦ cost (i₀.succAbove s) j) a)
  (hunique : ∀ z b c,
    OptimalCapacityAssignment (capacityDeficit r z)
      (fun s j ↦ cost (i₀.succAbove s) j) b →
    OptimalCapacityAssignment (capacityDeficit r z)
      (fun s j ↦ cost (i₀.succAbove s) j) c → b = c)

local notation "T" => capacityVacancyTreeRow r htotal hr cost i₀ a

local instance : DecidablePred T := Classical.decPred _

include ha hunique

/-- Restricting any actual quota optimum to the canonical tree rows leaves unit capacities
with precisely its original target vacant. -/
theorem capacityFeasible_restrict_treeRows (z : α) (b : Fin n → α)
    (hb : OptimalCapacityAssignment (capacityDeficit r z)
      (fun s j ↦ cost (i₀.succAbove s) j) b) :
    CapacityFeasible (capacityDeficit (fun _ : α ↦ 1) z) (fun k : {k // T k} ↦ b k) := by
  classical
  intro j
  let e : {k : {k // T k} // b k = j} ≃
      {k : Fin n // capacityVacancyTreeRow r htotal hr cost i₀ b k ∧ b k = j} :=
    { toFun := fun k ↦ ⟨k.1, (capacityVacancyTreeRow_iff_of_optimal
          r htotal hr cost i₀ root a ha z b hb k.1).mp k.1.2, k.2⟩
      invFun := fun k ↦ ⟨⟨k, (capacityVacancyTreeRow_iff_of_optimal
          r htotal hr cost i₀ root a ha z b hb k).mpr k.2.1⟩, k.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card,
    card_capacityVacancyTreeRow_fiber r htotal hr cost i₀ z b hb hunique]
  by_cases hj : j = z <;> simp [capacityDeficit, hj]

/-- The restricted allocation is an actual optimum for the unit-capacity tree problem. -/
theorem optimalCapacityAssignment_restrict_treeRows (z : α) (b : Fin n → α)
    (hb : OptimalCapacityAssignment (capacityDeficit r z)
      (fun s j ↦ cost (i₀.succAbove s) j) b) :
    OptimalCapacityAssignment (capacityDeficit (fun _ : α ↦ 1) z)
      (fun (k : {k // T k}) j ↦ cost (i₀.succAbove k) j) (fun k ↦ b k) := by
  classical
  apply optimalCapacityAssignment_of_feasible_tight_potentials _ _
    (fun k : {k // T k} ↦ capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k))
    (fun j ↦ capacityVacancyPrice r htotal cost i₀ j (hr j)) _
    (capacityFeasible_restrict_treeRows r htotal hr cost i₀ root a ha hunique z b hb)
  · intro k j
    exact capacityVacancyPotentials_feasible r htotal hr cost i₀ (i₀.succAbove k) j
  · intro k
    exact capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ z b hb k

omit hunique in
/-- Removing the strict rows subtracts one fixed cost from every quota vacancy optimum. -/
theorem capacityAssignmentCost_eq_tree_add_strict (z : α) (b : Fin n → α)
    (hb : OptimalCapacityAssignment (capacityDeficit r z)
      (fun s j ↦ cost (i₀.succAbove s) j) b) :
    capacityAssignmentCost (fun s j ↦ cost (i₀.succAbove s) j) b =
      capacityAssignmentCost (fun (k : {k // T k}) j ↦ cost (i₀.succAbove k) j)
        (fun k ↦ b k) +
      ∑ k : {k // ¬ T k}, cost (i₀.succAbove k) (a k) := by
  classical
  unfold capacityAssignmentCost
  rw [← Fintype.sum_subtype_add_sum_subtype T (fun k ↦ cost (i₀.succAbove k) (b k))]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [capacityVacancy_strict_row_fixed r htotal hr cost i₀ root a ha z b hb k k.2]

end Restriction
end OTSelector
