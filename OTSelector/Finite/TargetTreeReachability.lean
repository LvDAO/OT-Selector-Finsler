import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
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
import OTSelector.Finite.TargetTreeCycles

/-!
# Finite.TargetTreeReachability

**Conditions:** Positive quotas and one actual reference vacancy optimum; no uniqueness is needed for reachability.

**Objects:** Targets reachable from the missing target through actual tight arcs.

**Proof detail:** If another vacancy lies outside the reachable set, all rows assigned into it must already have reference partners there; summing quota counts gives a one-unit contradiction.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Reinhard Diestel, Graph Theory, 6th edition (2025)](https://diestel-graph-theory.com/Contents.pdf), Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Root reachability in the actual capacity vacancy tight graph

Every target is reachable from the missing target of a reference quota optimum.
For the set of reachable targets, any other vacancy optimum can only assign a row into
that set if its reference partner is also in the set: otherwise an actual tight arc
would enlarge the set. If the other vacancy were outside it, its prescribed capacities
would nevertheless require one additional row in the set. This contradiction proves
reachability directly from the actual capacity counts and common calibration.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- Every target is reachable from the actual missing target in the common tight graph.
The argument requires no uniqueness assumption on any of the finite optimizers. -/
theorem capacityVacancyTightArc_reachable
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun k l ↦ cost (i₀.succAbove k) l) a) (v : α) :
    Relation.ReflTransGen (capacityVacancyTightArc r htotal hr cost i₀ a) root v := by
  classical
  let R := capacityVacancyTightArc r htotal hr cost i₀ a
  by_contra hnot
  let w : α → ℝ := fun j ↦ if Relation.ReflTransGen R root j then 1 else 0
  have hroot : w root = 1 := by simp [w, Relation.ReflTransGen.refl]
  have hv : w v = 0 := by simp [w, R, hnot]
  have hs := capacityVacancyPrice_spec r htotal cost i₀ v (hr v)
  obtain ⟨b, hb, hvalue⟩ := hs.1
  have hbopt : OptimalCapacityAssignment (capacityDeficit r v)
      (fun k l ↦ cost (i₀.succAbove k) l) b :=
    ⟨hb, fun d hd ↦ hvalue ▸ hs.2 d hd⟩
  have hback (k : Fin n) (hk : Relation.ReflTransGen R root (b k)) :
      Relation.ReflTransGen R root (a k) := by
    by_cases hba : b k = a k
    · exact hba ▸ hk
    · have ht := capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ v b hbopt k
      exact Relation.ReflTransGen.tail hk ⟨hba, k, rfl, ht⟩
  have hle (k : Fin n) : w (b k) ≤ w (a k) := by
    by_cases hk : Relation.ReflTransGen R root (b k)
    · simp [w, hk, hback k hk]
    · simp only [w, ite_eq_right hk]
      split_ifs <;> norm_num
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) ↦ hle k)
  have haSum : (∑ k, w (a k)) = (∑ j, (r j : ℝ) * w j) - 1 := by
    rw [capacityFeasible_sum_weighted _ a ha.1 w,
      capacityDeficit_sum_weighted r root (hr root) w, hroot]
  have hbSum : (∑ k, w (b k)) = ∑ j, (r j : ℝ) * w j := by
    rw [capacityFeasible_sum_weighted _ b hb w,
      capacityDeficit_sum_weighted r v (hr v) w, hv, sub_zero]
  rw [haSum, hbSum] at hsum
  linarith

end OTSelector
