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
import OTSelector.Finite.TargetTreePrices
import OTSelector.Finite.TargetTreeRestriction
import OTSelector.Finite.TargetTreeRows
import OTSelector.Finite.TargetTreeSuccessful

/-!
# Finite.TargetTreeCanonicalSuccess

**Conditions:** Positive finite integer quotas and uniqueness of every actual quota-vacancy optimizer.

**Objects:** The unique successful retained subset, its original row enumeration and its actual reduced cavity costs.

**Proof detail:** Canonical flexible rows have the required cardinality and the strict complement has quota r−1; their reduced prices differ by one fixed constant, proving success, while the gluing characterization forces any successful subset to equal them.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Reinhard Diestel, Graph Theory, 6th edition (2025)](https://diestel-graph-theory.com/Contents.pdf), Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Existence and uniqueness of the actual successful retained subset

A candidate is an actual source subset with one fewer row than targets. Its prices are
computed by solving its own unit-capacity cavity problem. Success means that all omitted
rows choose strict cells with the requested residual counts. The canonical tree rows
supply a success, and the gluing theorem identifies every success with those same rows.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n m : ℕ}

section Canonical

variable (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
  (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α) (a : Fin n → α)
  (ha : OptimalCapacityAssignment (capacityDeficit r root)
    (fun k j ↦ cost (i₀.succAbove k) j) a)
  (hunique : ∀ z b c,
    OptimalCapacityAssignment (capacityDeficit r z)
      (fun k j ↦ cost (i₀.succAbove k) j) b →
    OptimalCapacityAssignment (capacityDeficit r z)
      (fun k j ↦ cost (i₀.succAbove k) j) c → b = c)

local notation "T" => capacityVacancyTreeRow r htotal hr cost i₀ a
local instance : DecidablePred T := Classical.decPred _

include ha hunique

/-- The complement of the actual tree has exactly the residual capacities and consists
of strict cells for the tree's own actual cavity prices. -/
theorem capacityVacancy_tree_complement_successful
    (hα : ∑ _ : α, 1 = m + 1) (e : Fin m ≃ {k : Fin n // T k})
    (small : Fin (m + 1) → α → ℝ) (iT : Fin (m + 1))
    (hcost : ∀ k j, small (iT.succAbove k) j = cost (i₀.succAbove (e k)) j) :
    CapacityFeasible (fun j ↦ r j - 1) (fun k : {k // ¬ T k} ↦ a k) ∧
      ∀ k : {k // ¬ T k}, ∀ j, j ≠ a k →
        cost (i₀.succAbove k) (a k) +
            capacityVacancyPrice (fun _ : α ↦ 1) hα small iT (a k) (by omega) <
          cost (i₀.succAbove k) j +
            capacityVacancyPrice (fun _ : α ↦ 1) hα small iT j (by omega) := by
  classical
  constructor
  · intro j
    let e' : {k : {k // ¬ T k} // a k = j} ≃ {k : Fin n // ¬ T k ∧ a k = j} :=
      { toFun := fun k ↦ ⟨k.1, k.1.2, k.2⟩
        invFun := fun k ↦ ⟨⟨k, k.2.1⟩, k.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e', ← Nat.card_eq_fintype_card]
    exact card_capacityVacancy_strict_fiber r htotal hr cost i₀ root a ha hunique j
  · intro k j hne
    have hle := capacityVacancyPotentials_feasible r htotal hr cost i₀ (i₀.succAbove k) j
    have hn : capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
        capacityVacancyPrice r htotal cost i₀ j (hr j) ≠ cost (i₀.succAbove k) j := by
      intro ht
      exact k.2 ⟨j, hne, ht⟩
    have hlt := lt_of_le_of_ne hle hn
    have ht := capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ root a ha k
    have hpa := capacityVacancyPrice_eq_tree_price_add_strict
      r htotal hr cost i₀ root a ha hunique hα e small iT hcost (a k)
    have hpj := capacityVacancyPrice_eq_tree_price_add_strict
      r htotal hr cost i₀ root a ha hunique hα e small iT hcost j
    linarith

end Canonical

/-- A fixed enumeration of the rows in an actual candidate subset. -/
def retainedSubsetRowEquiv (I : {I : Finset (Fin n) // I.card = m}) :
    Fin m ≃ {k : Fin n // k ∈ I.1} :=
  Fintype.equivOfCardEq (by simpa using I.2.symm)

/-- The candidate's actual retained cost matrix, completed by a zero dummy source row. -/
def retainedSubsetCavityCost (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1))
    (I : {I : Finset (Fin n) // I.card = m}) : Fin (m + 1) → α → ℝ :=
  Fin.insertNth 0 (fun _ ↦ 0) (fun k j ↦ cost (i₀.succAbove (retainedSubsetRowEquiv I k)) j)

omit [Fintype α] [DecidableEq α] in
@[simp]
theorem retainedSubsetCavityCost_retained (cost : Fin (n + 1) → α → ℝ)
    (i₀ : Fin (n + 1)) (I : {I : Finset (Fin n) // I.card = m}) (k : Fin m) (j : α) :
    retainedSubsetCavityCost cost i₀ I ((0 : Fin (m + 1)).succAbove k) j =
      cost (i₀.succAbove (retainedSubsetRowEquiv I k)) j := by
  simp only [retainedSubsetCavityCost, Fin.insertNth_apply_succAbove]

/-- Success of an actual candidate subset: its omitted rows have strict cavity-cell
choices with exactly the residual target counts. All prices are the candidate's own optima. -/
def CapacitySuccessfulSubset (r : α → ℕ) (hα : ∑ _ : α, 1 = m + 1)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1))
    (I : {I : Finset (Fin n) // I.card = m}) : Prop :=
  ∃ s : {k : Fin n // k ∉ I.1} → α,
    CapacityFeasible (fun j ↦ r j - 1) s ∧
      ∀ k : {k : Fin n // k ∉ I.1}, ∀ j, j ≠ s k →
        cost (i₀.succAbove k) (s k) + capacityVacancyPrice (fun _ : α ↦ 1) hα
            (retainedSubsetCavityCost cost i₀ I) 0 (s k) (Nat.zero_lt_succ 0) <
          cost (i₀.succAbove k) j + capacityVacancyPrice (fun _ : α ↦ 1) hα
            (retainedSubsetCavityCost cost i₀ I) 0 j (Nat.zero_lt_succ 0)

/-- Exactly one actual source subset succeeds. The subset is constructed from the quota
optima and is not supplied as a separate tree or successful-subset assumption. -/
theorem existsUnique_capacitySuccessfulSubset
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (hα : ∑ _ : α, 1 = m + 1) (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1))
    (hunique : ∀ z b c,
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun k j ↦ cost (i₀.succAbove k) j) b →
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun k j ↦ cost (i₀.succAbove k) j) c → b = c) :
    ∃! I : {I : Finset (Fin n) // I.card = m}, CapacitySuccessfulSubset r hα cost i₀ I := by
  classical
  let root := capacitySlotLabel r htotal 0
  obtain ⟨⟨a, ha, hval⟩, hmin⟩ := capacityVacancyPrice_spec r htotal cost i₀ root (hr root)
  have haopt : OptimalCapacityAssignment (capacityDeficit r root)
      (fun k j ↦ cost (i₀.succAbove k) j) a :=
    ⟨ha, fun b hb ↦ hval ▸ hmin b hb⟩
  let T := capacityVacancyTreeRow r htotal hr cost i₀ a
  let Iset := Finset.univ.filter T
  have hI : Iset.card = m := by
    have h := card_capacityVacancyTreeRows r htotal hr cost i₀ root a haopt hunique
    have hc : Fintype.card α = m + 1 := by simpa using hα
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, hc, Nat.add_sub_cancel] using h
  let I : {I : Finset (Fin n) // I.card = m} := ⟨Iset, hI⟩
  have hmem (k : Fin n) : k ∈ I.1 ↔ T k := by simp [I, Iset]
  let eT : {k : Fin n // k ∈ I.1} ≃ {k : Fin n // T k} :=
    Equiv.subtypeEquivRight hmem
  let eC : {k : Fin n // k ∉ I.1} ≃ {k : Fin n // ¬ T k} :=
    Equiv.subtypeEquivRight (fun k ↦ not_congr (hmem k))
  have hsucc := capacityVacancy_tree_complement_successful
    r htotal hr cost i₀ root a haopt hunique hα ((retainedSubsetRowEquiv I).trans eT)
    (retainedSubsetCavityCost cost i₀ I) 0 (fun k j ↦ retainedSubsetCavityCost_retained cost i₀ I k j)
  have hsuccess : CapacitySuccessfulSubset r hα cost i₀ I := by
    refine ⟨fun k ↦ a k, ?_, ?_⟩
    · exact capacityFeasible_reindex _ _ eC hsucc.1
    · intro k j hj
      exact hsucc.2 (eC k) j hj
  refine ⟨I, hsuccess, ?_⟩
  intro J hJ
  obtain ⟨s, hs, hstrict⟩ := hJ
  have hminJ : ∀ k : {k : Fin n // k ∉ J.1}, ∀ j,
      cost (i₀.succAbove k) (s k) + capacityVacancyPrice (fun _ : α ↦ 1) hα
          (retainedSubsetCavityCost cost i₀ J) 0 (s k) (Nat.zero_lt_succ 0) ≤
        cost (i₀.succAbove k) j + capacityVacancyPrice (fun _ : α ↦ 1) hα
          (retainedSubsetCavityCost cost i₀ J) 0 j (Nat.zero_lt_succ 0) := by
    intro k j
    by_cases hj : j = s k
    · rw [hj]
    · exact (hstrict k j hj).le
  have heq := capacityVacancyTreeRow_iff_successful_retained r htotal hr cost i₀
    (fun k ↦ k ∈ J.1) hα (retainedSubsetRowEquiv J) (retainedSubsetCavityCost cost i₀ J) 0
    (fun k j ↦ retainedSubsetCavityCost_retained cost i₀ J k j) s hs hminJ
    root a haopt hunique hstrict
  apply Subtype.ext
  apply Finset.ext
  intro k
  exact (heq k).symm.trans (hmem k).symm

end OTSelector
