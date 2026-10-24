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
import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.TargetTreeRestriction
import OTSelector.Finite.TargetTreeRows

/-!
# Finite.TargetTreePrices

**Conditions:** The same actual quota-uniqueness assumptions and an explicit enumeration of the canonical flexible rows.

**Objects:** Quota vacancy prices, reduced unit-capacity tree prices, and invariant insertion-score comparisons.

**Proof detail:** Evaluate both minima on corresponding restricted optimizers; their costs differ by the fixed strict-row sum, which cancels from all score differences.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (corollary): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Exact quota-to-tree vacancy price reduction

The actual quota vacancy prices equal the actual unit-capacity tree prices plus the cost
of the strict rows. That additive constant is independent of the vacant target, so all
insertion score comparisons and the resulting full cells are unchanged.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- Every actual quota optimum attains the actual quota vacancy price. -/
theorem capacityVacancyPrice_eq_cost_of_optimal
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (j : α) (hj : 0 < r j)
    (b : Fin n → α) (hb : OptimalCapacityAssignment (capacityDeficit r j)
      (fun k l ↦ cost (i₀.succAbove k) l) b) :
    capacityVacancyPrice r htotal cost i₀ j hj =
      capacityAssignmentCost (fun k l ↦ cost (i₀.succAbove k) l) b := by
  obtain ⟨⟨d, hd, hval⟩, hle⟩ := capacityVacancyPrice_spec r htotal cost i₀ j hj
  exact le_antisymm (hle b hb.1) ((hb.2 d hd).trans_eq hval)

/-- Unit-capacity label vacancy prices are exactly the ordinary assignment cavity values. -/
theorem capacityVacancyPrice_unit_eq_assignmentCavityValue {m : ℕ}
    (cost : Fin (m + 1) → Fin (m + 1) → ℝ) (i j : Fin (m + 1)) :
    capacityVacancyPrice (fun _ : Fin (m + 1) ↦ 1) (by simp) cost i j (by omega) =
      assignmentCavityValue cost i j := by
  have ht : CapacityFeasible (fun _ : Fin (m + 1) ↦ 1) id := by
    intro l
    simp
  obtain ⟨⟨b, hb, hbval⟩, hbmin⟩ := capacityVacancyPrice_spec
    (fun _ : Fin (m + 1) ↦ 1) (by simp) cost i j (by omega)
  obtain ⟨d, hd, hdval⟩ := assignmentCavityValue_capacity_attained
    (fun _ : Fin (m + 1) ↦ 1) cost id ht i j
  apply le_antisymm
  · exact (hbmin d hd).trans_eq hdval
  · exact (assignmentCavityValue_le_capacity_cost
      (fun _ : Fin (m + 1) ↦ 1) cost id ht i j b hb).trans_eq hbval

section Prices

variable (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
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

/-- Enumerating the actual canonical tree rows supplies a genuine reduced cavity problem. -/
theorem exists_capacityVacancy_treeRow_equiv {m : ℕ} (hα : Fintype.card α = m + 1) :
    Nonempty (Fin m ≃ {k : Fin n // T k}) := by
  classical
  apply Fintype.card_eq.mp
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
    card_capacityVacancyTreeRows r htotal hr cost i₀ root a ha hunique, hα]
  simp

/-- Quota vacancy prices differ from the actual unit-capacity tree vacancy prices by
the single strict-row cost, independently of the vacant target. The reduced rows may be
enumerated in any order, and the artificial deleted row may contain arbitrary costs. -/
theorem capacityVacancyPrice_eq_tree_price_add_strict {m : ℕ}
    (hα : ∑ _ : α, 1 = m + 1) (e : Fin m ≃ {k : Fin n // T k})
    (treeCost : Fin (m + 1) → α → ℝ) (iT : Fin (m + 1))
    (hcost : ∀ k j, treeCost (iT.succAbove k) j = cost (i₀.succAbove (e k)) j)
    (j : α) :
    capacityVacancyPrice r htotal cost i₀ j (hr j) =
      capacityVacancyPrice (fun _ : α ↦ 1) hα treeCost iT j (by omega) +
        ∑ k : {k // ¬ T k}, cost (i₀.succAbove k) (a k) := by
  classical
  obtain ⟨⟨b, hb, hval⟩, hle⟩ := capacityVacancyPrice_spec r htotal cost i₀ j (hr j)
  have hbopt : OptimalCapacityAssignment (capacityDeficit r j)
      (fun k l ↦ cost (i₀.succAbove k) l) b :=
    ⟨hb, fun d hd ↦ hval ▸ hle d hd⟩
  have htree := optimalCapacityAssignment_restrict_treeRows
    r htotal hr cost i₀ root a ha hunique j b hbopt
  have henum := optimalCapacityAssignment_reindex _ _ _ e htree
  have heCost : (fun k l ↦ cost (i₀.succAbove (e k)) l) =
      (fun k l ↦ treeCost (iT.succAbove k) l) := by
    funext k l
    exact (hcost k l).symm
  have henum' : OptimalCapacityAssignment (capacityDeficit (fun _ : α ↦ 1) j)
      (fun k l ↦ treeCost (iT.succAbove k) l) (fun k ↦ b (e k)) := heCost ▸ henum
  have htval := capacityVacancyPrice_eq_cost_of_optimal
    (fun _ : α ↦ 1) hα treeCost iT j (by omega) _ henum'
  have hsum := capacityAssignmentCost_reindex
    (fun (k : {k // T k}) l ↦ cost (i₀.succAbove k) l) (fun k ↦ b k) e
  rw [heCost] at hsum
  rw [← hval, capacityAssignmentCost_eq_tree_add_strict
    r htotal hr cost i₀ root a ha j b hbopt, htval]
  exact congrArg (fun x ↦ x + ∑ k : {k // ¬ T k}, cost (i₀.succAbove k) (a k)) hsum.symm

/-- Every insertion-score comparison is identical for the actual quota and tree prices. -/
theorem capacityVacancy_score_le_iff_tree_score_le {m : ℕ}
    (hα : ∑ _ : α, 1 = m + 1) (e : Fin m ≃ {k : Fin n // T k})
    (treeCost : Fin (m + 1) → α → ℝ) (iT : Fin (m + 1))
    (hcost : ∀ k j, treeCost (iT.succAbove k) j = cost (i₀.succAbove (e k)) j)
    (row : α → ℝ) (j l : α) :
    (row j + capacityVacancyPrice r htotal cost i₀ j (hr j) ≤
      row l + capacityVacancyPrice r htotal cost i₀ l (hr l)) ↔
    (row j + capacityVacancyPrice (fun _ : α ↦ 1) hα treeCost iT j (by omega) ≤
      row l + capacityVacancyPrice (fun _ : α ↦ 1) hα treeCost iT l (by omega)) := by
  rw [capacityVacancyPrice_eq_tree_price_add_strict
    r htotal hr cost i₀ root a ha hunique hα e treeCost iT hcost j,
    capacityVacancyPrice_eq_tree_price_add_strict
      r htotal hr cost i₀ root a ha hunique hα e treeCost iT hcost l]
  simp only [← add_assoc, add_le_add_iff_right]

end Prices
end OTSelector
