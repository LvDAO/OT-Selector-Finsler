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
import OTSelector.Finite.TargetTreeCycles
import OTSelector.Finite.TargetTreeReachability

/-!
# Finite.TargetTreeSimplePaths

**Conditions:** Reflexive-transitive reachability for a relation; quota-specific exclusions additionally assume uniqueness of the actual reference optimizer.

**Objects:** Finite injective paths, no reverse reachability across a tight arc, and labelled paths in the vacancy graph.

**Proof detail:** Induct over reachability and truncate repeated vertices to obtain a simple path; a reverse path would close a forbidden tight cycle, and actual edge witnesses supply the source-row labels.

**Sources:** [Reinhard Diestel, Graph Theory, 6th edition (2025)](https://diestel-graph-theory.com/Contents.pdf), Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Simple paths in the actual vacancy graph

Finite indexed simple paths are extracted from actual reachability by truncating at a
previously visited endpoint. Their row labels come directly from the actual tight edges.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

/-- Any finite reachability witness has a simple finite indexed path. -/
theorem exists_simple_fin_path_of_reflTransGen {α : Type*} {R : α → α → Prop}
    {u z : α} (h : Relation.ReflTransGen R u z) :
    ∃ (m : ℕ) (v : Fin (m + 1) → α), Function.Injective v ∧ v 0 = u ∧
      v (Fin.last m) = z ∧ ∀ t : Fin m, R (v t.castSucc) (v t.succ) := by
  classical
  induction h with
  | refl =>
    exact ⟨0, fun _ ↦ u, (by intro s t _; apply Fin.ext; omega), rfl, rfl,
      fun t ↦ Fin.elim0 t⟩
  | @tail x y hxy hstep ih =>
    obtain ⟨m, v, hv, hstart, hend, hsteps⟩ := ih
    by_cases hy : y ∈ Set.range v
    · obtain ⟨t, ht⟩ := hy
      have hle : t.val + 1 ≤ m + 1 := Nat.succ_le_of_lt t.isLt
      let w : Fin (t.val + 1) → α := fun s ↦ v (s.castLE hle)
      refine ⟨t.val, w, hv.comp (Fin.castLE_injective hle), ?_, ?_, ?_⟩
      · exact hstart
      · exact ht
      · intro s
        exact hsteps ⟨s.val, lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ t.isLt)⟩
    · let w : Fin (m + 1 + 1) → α := Fin.snoc v y
      refine ⟨m + 1, w, Fin.snoc_injective_of_injective hv hy, ?_, ?_, ?_⟩
      · simpa only [w, Fin.snoc_apply_zero] using hstart
      · simp only [w, Fin.snoc_last]
      · intro t
        refine Fin.lastCases ?_ (fun s ↦ ?_) t
        · simpa only [w, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hend] using hstep
        · simpa only [w, ← Fin.castSucc_succ, Fin.snoc_castSucc] using hsteps s

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- Each vertex of a finite directed path reaches its terminal vertex. -/
theorem fin_path_reachable_to_last {β : Type*} {R : β → β → Prop}
    {m : ℕ} (v : Fin (m + 1) → β)
    (hstep : ∀ t : Fin m, R (v t.castSucc) (v t.succ)) (t : Fin (m + 1)) :
    Relation.ReflTransGen R (v t) (v (Fin.last m)) := by
  refine Fin.reverseInduction Relation.ReflTransGen.refl (fun s hs ↦ ?_) t
  exact hs.head (hstep s)

/-- An actual tight arc cannot point back to a vertex that reaches its source, when
the reference quota optimum is unique. -/
theorem not_capacityVacancyTightArc_reverse_reachable
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) a)
    (hunique : ∀ b, OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) b → b = a)
    {u z : α} (hedge : capacityVacancyTightArc r htotal hr cost i₀ a u z) :
    ¬ Relation.ReflTransGen (capacityVacancyTightArc r htotal hr cost i₀ a) z u := by
  intro hback
  obtain ⟨m, v, hv, hstart, hend, hsteps⟩ :=
    exists_simple_fin_path_of_reflTransGen hback
  cases m with
  | zero => exact hedge.1 (hend.symm.trans hstart)
  | succ m =>
    apply not_capacityVacancyTightArc_cycle r htotal hr cost i₀ root a ha hunique m v hv
    intro t
    refine Fin.lastCases ?_ (fun s ↦ ?_) t
    · simpa only [finRotate_last, hend, hstart] using hedge
    · rw [show finRotate (m + 2) s.castSucc = s.succ from finRotate_of_lt s.isLt]
      exact hsteps s

/-- The reference vacant target has no incoming actual tight arc. -/
theorem not_capacityVacancyTightArc_to_root
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) a)
    (hunique : ∀ b, OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) b → b = a) (u : α) :
    ¬ capacityVacancyTightArc r htotal hr cost i₀ a u root := by
  intro h
  exact not_capacityVacancyTightArc_reverse_reachable r htotal hr cost i₀ root a ha
    hunique h (capacityVacancyTightArc_reachable r htotal hr cost i₀ root a ha u)

/-- Every target admits a simple labelled path in the actual capacity vacancy tight graph. -/
theorem exists_capacityVacancy_labelled_path
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) a) (z : α) :
    ∃ (m : ℕ) (v : Fin (m + 1) → α) (k : Fin m → Fin n),
      Function.Injective v ∧ v 0 = root ∧ v (Fin.last m) = z ∧
      (∀ t, a (k t) = v t.succ) ∧
      ∀ t, capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove (k t)) -
        capacityVacancyPrice r htotal cost i₀ (v t.castSucc) (hr (v t.castSucc)) =
          cost (i₀.succAbove (k t)) (v t.castSucc) := by
  obtain ⟨m, v, hv, hstart, hend, hsteps⟩ :=
    exists_simple_fin_path_of_reflTransGen
      (capacityVacancyTightArc_reachable r htotal hr cost i₀ root a ha z)
  choose k hk htight using fun t ↦ (hsteps t).2
  exact ⟨m, v, k, hv, hstart, hend, hk, htight⟩

end OTSelector
