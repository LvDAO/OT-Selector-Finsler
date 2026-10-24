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
import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.CapacityCalibration

/-!
# Finite.TargetTreeTightEdges

**Conditions:** Positive integer quotas and the actual common vacancy dual; a retained allocation is an actual vacancy optimum.

**Objects:** Tight source-target edges and allocations obtained by moving one source into the vacancy.

**Proof detail:** A one-row update shifts one unit of capacity between its old target and the vacancy; tightness preserves the attained dual objective, identifying tight edges with edges appearing in actual vacancy optima.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (corollary): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Every actual tight edge occurs in a capacity vacancy optimum

Reassign one retained source to the currently vacant target. Its previous target becomes
the new vacancy, and every capacity remains correct. If the new edge is tight for the
actual common vacancy dual, the changed allocation is again optimal. Thus the tight graph
used by the target-tree argument consists exactly of edges occurring in actual vacancy
optima, without an assumed graph or an optimizer selection rule.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

omit [Fintype α] [DecidableEq ι] in
private theorem card_fiber_eq_sum (a : ι → α) (j : α) :
    Fintype.card {k // a k = j} = ∑ k, if a k = j then 1 else 0 := by
  simp [Fintype.card_subtype, Finset.sum_boole]

omit [Fintype α] in
private theorem card_fiber_update_balance (a : ι → α) (k : ι) (j l : α) :
    Fintype.card {s // Function.update a k j s = l} + (if a k = l then 1 else 0) =
      Fintype.card {s // a s = l} + (if j = l then 1 else 0) := by
  have hfun : (fun s ↦ if Function.update a k j s = l then 1 else 0) =
      Function.update (fun s ↦ if a s = l then 1 else 0) k (if j = l then 1 else 0) :=
    funext (Function.apply_update (fun _ t ↦ if t = l then 1 else 0) a k j)
  rw [card_fiber_eq_sum, hfun, Finset.sum_update_of_mem (Finset.mem_univ k),
    Finset.sdiff_singleton_eq_erase, card_fiber_eq_sum]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun s ↦ if a s = l then 1 else 0) (Finset.mem_univ k)
  omega

omit [Fintype α] in
/-- Assigning a row to the current vacancy transfers the vacancy to its previous target. -/
theorem capacityFeasible_update_vacancy
    (r : α → ℕ) (hr : ∀ j, 0 < r j) (j : α) (a : ι → α)
    (ha : CapacityFeasible (capacityDeficit r j) a) (k : ι) :
    CapacityFeasible (capacityDeficit r (a k)) (Function.update a k j) := by
  intro l
  have h := card_fiber_update_balance a k j l
  rw [ha l] at h
  have hl := hr l
  dsimp only [capacityDeficit] at h ⊢
  by_cases hjl : j = l <;> by_cases hkl : a k = l <;>
    simp only [hjl, hkl, eq_comm (a := l), ↓reduceIte] at h ⊢
  all_goals omega

variable {n : ℕ}

/-- Reassigning an actual optimal vacancy allocation along a tight edge gives an actual
optimum with the old partner vacant. Every unchanged row keeps its original partner. -/
theorem optimalCapacityAssignment_update_vacancy_of_tight
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (j : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r j)
      (fun k l ↦ cost (i₀.succAbove k) l) a)
    (k : Fin n)
    (htight : capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ j (hr j) = cost (i₀.succAbove k) j) :
    OptimalCapacityAssignment (capacityDeficit r (a k))
      (fun s l ↦ cost (i₀.succAbove s) l) (Function.update a k j) := by
  apply (optimalCapacityAssignment_iff_capacityVacancyPotentials_tight
    r htotal hr cost i₀ (a k) (Function.update a k j)).mpr
  refine ⟨capacityFeasible_update_vacancy r hr j a ha.1 k, ?_⟩
  intro s
  by_cases hsk : s = k
  · subst s
    simpa only [Function.update_self] using htight
  · simpa only [Function.update_of_ne hsk] using
      capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ j a ha s

/-- The actual common tight graph equals the union of the supports of all quota vacancy
optima. The forward implication constructs its witness by a single-row reassignment. -/
theorem capacityVacancy_tight_iff_exists_optimal_edge
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (k : Fin n) (j : α) :
    (capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ j (hr j) = cost (i₀.succAbove k) j) ↔
      ∃ (v : α) (a : Fin n → α),
        OptimalCapacityAssignment (capacityDeficit r v)
          (fun s l ↦ cost (i₀.succAbove s) l) a ∧ a k = j := by
  constructor
  · intro htight
    have hs := capacityVacancyPrice_spec r htotal cost i₀ j (hr j)
    obtain ⟨a, ha, hv⟩ := hs.1
    have hopt : OptimalCapacityAssignment (capacityDeficit r j)
        (fun s l ↦ cost (i₀.succAbove s) l) a :=
      ⟨ha, fun b hb ↦ hv ▸ hs.2 b hb⟩
    exact ⟨a k, Function.update a k j,
      optimalCapacityAssignment_update_vacancy_of_tight r htotal hr cost i₀ j a hopt k htight,
      Function.update_self k j a⟩
  · rintro ⟨v, a, ha, haj⟩
    have h := capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ v a ha k
    simpa only [haj] using h

end OTSelector
