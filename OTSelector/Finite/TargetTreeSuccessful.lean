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
import OTSelector.Finite.TargetTreeGluing
import OTSelector.Finite.TargetTreePrices
import OTSelector.Finite.TargetTreeRestriction
import OTSelector.Finite.TargetTreeRows

/-!
# Finite.TargetTreeSuccessful

**Conditions:** A retained subset has one fewer row than targets; omitted rows minimize its actual reduced cavity scores with residual quota counts, and strictness/uniqueness are explicit in their respective conclusions.

**Objects:** Successful complementary allocations and identification with the canonical flexible-row subset.

**Proof detail:** Glue each reduced vacancy optimum to the omitted minimizing cells, sum feasible capacities and common tight costs, then compare strict complement choices and canonical row counts to identify exactly the retained rows.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Successful retained subsets recover the actual quota problem

An arbitrary retained subset with one fewer row than targets supplies its own actual
unit-capacity cavity prices. If the complementary minimizing choices have counts `r - 1`,
gluing them to every reduced vacancy optimum constructs actual quota optima. Their prices
therefore differ by the single cost of those complementary choices.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n m : ℕ}

section Successful

variable (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
  (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1))
  (P : Fin n → Prop) [DecidablePred P]
  (hα : ∑ _ : α, 1 = m + 1) (e : Fin m ≃ {k // P k})
  (small : Fin (m + 1) → α → ℝ) (iT : Fin (m + 1))
  (hcost : ∀ k j, small (iT.succAbove k) j = cost (i₀.succAbove (e k)) j)
  (s : {k // ¬ P k} → α) (hs : CapacityFeasible (fun j ↦ r j - 1) s)

local notation "R" =>
  (fun j : α ↦ capacityVacancyPrice (fun _ : α ↦ 1) hα small iT j (Nat.zero_lt_succ 0))

variable (hmin : ∀ k : {k // ¬ P k}, ∀ j,
  cost (i₀.succAbove k) (s k) +
      capacityVacancyPrice (fun _ : α ↦ 1) hα small iT (s k) (Nat.zero_lt_succ 0) ≤
    cost (i₀.succAbove k) j +
      capacityVacancyPrice (fun _ : α ↦ 1) hα small iT j (Nat.zero_lt_succ 0))

include hr hcost hs hmin

/-- Complementary minimizing choices with the prescribed counts complete every ordinary
vacancy optimum to an actual quota optimum, with its exact total cost recorded. -/
theorem exists_optimalCapacityAssignment_glue_cavity_cells (z : α) :
    ∃ b : Fin n → α,
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun k j ↦ cost (i₀.succAbove k) j) b ∧
      (∀ k : {k // ¬ P k}, b k = s k) ∧
      capacityAssignmentCost (fun k j ↦ cost (i₀.succAbove k) j) b =
        R z + ∑ k : {k // ¬ P k}, cost (i₀.succAbove k) (s k) := by
  classical
  obtain ⟨⟨d, hd, hdval⟩, hdmin⟩ := capacityVacancyPrice_spec
    (fun _ : α ↦ 1) hα small iT z (by omega)
  have hdopt : OptimalCapacityAssignment (capacityDeficit (fun _ : α ↦ 1) z)
      (fun k j ↦ small (iT.succAbove k) j) d :=
    ⟨hd, fun b hb ↦ hdval ▸ hdmin b hb⟩
  let p : {k // P k} → α := d ∘ e.symm
  let b := glueCapacityAssignments P p s
  have hce (k : {k // P k}) (j : α) :
      small (iT.succAbove (e.symm k)) j = cost (i₀.succAbove k) j := by
    simpa only [Equiv.apply_symm_apply] using hcost (e.symm k) j
  have hp : CapacityFeasible (capacityDeficit (fun _ : α ↦ 1) z) p :=
    capacityFeasible_reindex _ d e.symm hd
  have hb : CapacityFeasible (capacityDeficit r z) b := by
    have h := capacityFeasible_glue P _ _ p s hp hs
    have heq : (fun j ↦ capacityDeficit (fun _ : α ↦ 1) z j + (r j - 1)) =
        capacityDeficit r z := by
      funext j
      have hj := hr j
      by_cases hjz : j = z <;> simp only [capacityDeficit, hjz, ↓reduceIte] <;> omega
    exact heq ▸ h
  let u : Fin n → ℝ := glueCapacityAssignments P
    (fun k ↦ capacityVacancyRowPotential (fun _ : α ↦ 1) hα (by intro j; omega)
      small iT (iT.succAbove (e.symm k)))
    (fun k ↦ cost (i₀.succAbove k) (s k) + R (s k))
  have hle (k : Fin n) (j : α) : u k - R j ≤ cost (i₀.succAbove k) j := by
    by_cases hk : P k
    · have h := capacityVacancyPotentials_feasible
        (fun _ : α ↦ 1) hα (by intro l; omega) small iT
        (iT.succAbove (e.symm ⟨k, hk⟩)) j
      simpa only [u, glueCapacityAssignments_of_pos P _ _ k hk, hce] using h
    · have h := hmin ⟨k, hk⟩ j
      simp only [u, glueCapacityAssignments_of_neg P _ _ k hk]
      linarith
  have ht (k : Fin n) : u k - R (b k) = cost (i₀.succAbove k) (b k) := by
    by_cases hk : P k
    · have h := capacityVacancyPotentials_tight_of_optimal
        (fun _ : α ↦ 1) hα (by intro j; omega) small iT z d hdopt (e.symm ⟨k, hk⟩)
      simpa only [u, b, glueCapacityAssignments_of_pos P _ _ k hk, p,
        Function.comp_apply, hce] using h
    · simp only [u, b, glueCapacityAssignments_of_neg P _ _ k hk]
      ring
  refine ⟨b, optimalCapacityAssignment_of_feasible_tight_potentials
    _ _ u R b hb hle ht, fun k ↦ glueCapacityAssignments_of_neg P p s k k.2, ?_⟩
  rw [capacityAssignmentCost_glue]
  have hv := capacityAssignmentCost_reindex
    (fun k j ↦ small (iT.succAbove k) j) d e.symm
  have hcfun : (fun (k : {k // P k}) j ↦ small (iT.succAbove (e.symm k)) j) =
      (fun (k : {k // P k}) j ↦ cost (i₀.succAbove k) j) := by
    funext k j
    exact hce k j
  rw [hcfun, hdval] at hv
  exact congrArg (fun x ↦ x + ∑ k : {k // ¬ P k}, cost (i₀.succAbove k) (s k)) hv

/-- Any successful complementary choices identify the actual quota prices, even before
strictness or optimizer uniqueness is used. -/
theorem capacityVacancyPrice_eq_of_successful_complement (z : α) :
    capacityVacancyPrice r htotal cost i₀ z (hr z) =
      R z + ∑ k : {k // ¬ P k}, cost (i₀.succAbove k) (s k) := by
  obtain ⟨b, hb, _, hcostb⟩ := exists_optimalCapacityAssignment_glue_cavity_cells
    r hr cost i₀ P hα e small iT hcost s hs hmin z
  exact (capacityVacancyPrice_eq_cost_of_optimal r htotal cost i₀ z (hr z) b hb).trans hcostb

/-- Strict complementary cell choices force every actual tree row to lie in the retained
subset. This conclusion uses actual quota prices, reconstructed by the preceding gluing. -/
theorem capacityVacancyTreeRow_of_successful_complement_subset
    (root : α) (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun k j ↦ cost (i₀.succAbove k) j) a)
    (hstrict : ∀ k : {k // ¬ P k}, ∀ j, j ≠ s k →
      cost (i₀.succAbove k) (s k) + R (s k) < cost (i₀.succAbove k) j + R j) :
    ∀ k, capacityVacancyTreeRow r htotal hr cost i₀ a k → P k := by
  intro k hk
  by_contra hkP
  let q : {k // ¬ P k} := ⟨k, hkP⟩
  have hprice (j : α) := capacityVacancyPrice_eq_of_successful_complement
    r htotal hr cost i₀ P hα e small iT hcost s hs hmin j
  have hta := capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ root a ha k
  have hfs := capacityVacancyPotentials_feasible r htotal hr cost i₀
    (i₀.succAbove k) (s q)
  have hak : a k = s q := by
    by_contra hne
    have hlt := hstrict q (a k) hne
    have hpa := hprice (a k)
    have hps := hprice (s q)
    dsimp only [q] at hlt
    linarith
  obtain ⟨u, hu, htu⟩ := hk
  have hus : u ≠ s q := hak ▸ hu
  have hlt := hstrict q u hus
  have hpa := hprice (a k)
  have hpu := hprice u
  rw [← hak] at hlt
  dsimp only [q] at hlt
  linarith

/-- A successful retained subset is the canonical actual tree-row subset. In particular,
there can be only one successful subset of the required size. -/
theorem capacityVacancyTreeRow_iff_successful_retained
    (root : α) (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun k j ↦ cost (i₀.succAbove k) j) a)
    (hunique : ∀ z b c,
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun k j ↦ cost (i₀.succAbove k) j) b →
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun k j ↦ cost (i₀.succAbove k) j) c → b = c)
    (hstrict : ∀ k : {k // ¬ P k}, ∀ j, j ≠ s k →
      cost (i₀.succAbove k) (s k) + R (s k) < cost (i₀.succAbove k) j + R j) :
    ∀ k, capacityVacancyTreeRow r htotal hr cost i₀ a k ↔ P k := by
  classical
  let T := capacityVacancyTreeRow r htotal hr cost i₀ a
  have hsub : Finset.univ.filter T ⊆ Finset.univ.filter P := by
    intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact capacityVacancyTreeRow_of_successful_complement_subset
      r htotal hr cost i₀ P hα e small iT hcost s hs hmin root a ha hstrict
      k (Finset.mem_filter.mp hk).2
  have hcardα : Fintype.card α = m + 1 := by simpa using hα
  have hT : (Finset.univ.filter T).card = m := by
    have h := card_capacityVacancyTreeRows r htotal hr cost i₀ root a ha hunique
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hcardα] at h
    simpa using h
  have hP : (Finset.univ.filter P).card = m := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_fin, Fintype.card_subtype] using h.symm
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro k
  have h := congrArg (fun S : Finset (Fin n) ↦ k ∈ S) heq
  exact propext_iff.mp (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h)

end Successful
end OTSelector
