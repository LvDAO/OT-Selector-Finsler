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
import OTSelector.Finite.TargetTreePaths
import OTSelector.Finite.TargetTreeSimplePaths

/-!
# Finite.TargetTreeIncoming

**Conditions:** Every actual quota-vacancy problem has a unique optimizer; compare tight edges with the same reference target.

**Objects:** The unique incoming tight edge to a nonroot target, including its retained source label.

**Proof detail:** Append a tight edge to a simple rooted path and reroot the vacancy; uniqueness of the resulting actual vacancy optimum forces both constructions to change the same terminal row to the same preceding target.

**Sources:** [Reinhard Diestel, Graph Theory, 6th edition (2025)](https://diestel-graph-theory.com/Contents.pdf), Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Unique labelled incoming edges from actual quota uniqueness

Appending any actual tight edge to a simple path constructs a vacancy optimum in which
its row is the sole changed row previously assigned to the final target. Uniqueness of
the actual quota optimizers therefore forces every nonroot target to have at most one
incoming edge, including its source-row label.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- Any labelled tight edge can be the final edge of an actual rerooting. Among the
rows originally assigned to its target, only this row changes. -/
theorem exists_optimalCapacityAssignment_reroot_terminal_row
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) a)
    (hunique : ∀ b, OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) b → b = a)
    (k : Fin n) (u : α) (hu : u ≠ a k)
    (htight : capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ u (hr u) = cost (i₀.succAbove k) u) :
    ∃ b, OptimalCapacityAssignment (capacityDeficit r (a k))
        (fun s j ↦ cost (i₀.succAbove s) j) b ∧ b k = u ∧
      ∀ s, a s = a k → s ≠ k → b s = a s := by
  classical
  obtain ⟨m, v, q, hv, hstart, hend, hmatch, ht⟩ :=
    exists_capacityVacancy_labelled_path r htotal hr cost i₀ root a ha u
  have harc : capacityVacancyTightArc r htotal hr cost i₀ a u (a k) :=
    ⟨hu, k, rfl, htight⟩
  have hsteps (t : Fin m) :
      capacityVacancyTightArc r htotal hr cost i₀ a (v t.castSucc) (v t.succ) := by
    refine ⟨fun heq ↦ ?_, q t, hmatch t, ht t⟩
    have heq' := congrArg Fin.val (hv heq)
    simp only [Fin.val_castSucc, Fin.val_succ] at heq'
    omega
  have hout : a k ∉ Set.range v := by
    rintro ⟨t, htk⟩
    have hback := fin_path_reachable_to_last v hsteps t
    rw [htk, hend] at hback
    exact not_capacityVacancyTightArc_reverse_reachable
      r htotal hr cost i₀ root a ha hunique harc hback
  let w : Fin (m + 1 + 1) → α := Fin.snoc v (a k)
  let p : Fin (m + 1) → Fin n := Fin.snoc q k
  have hw : Function.Injective w := Fin.snoc_injective_of_injective hv hout
  have hw0 : w 0 = root := by simpa only [w, Fin.snoc_apply_zero] using hstart
  have hpmatch : ∀ t, a (p t) = w t.succ := by
    intro t
    refine Fin.lastCases ?_ (fun s ↦ ?_) t
    · simp only [p, w, Fin.snoc_last, Fin.succ_last]
    · simpa only [p, w, ← Fin.castSucc_succ, Fin.snoc_castSucc] using hmatch s
  have hptight : ∀ t,
      capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove (p t)) -
        capacityVacancyPrice r htotal cost i₀ (w t.castSucc) (hr (w t.castSucc)) =
          cost (i₀.succAbove (p t)) (w t.castSucc) := by
    intro t
    refine Fin.lastCases ?_ (fun s ↦ ?_) t
    · simpa only [p, w, Fin.snoc_last, Fin.snoc_castSucc, hend] using htight
    · simpa only [p, w, Fin.snoc_castSucc] using ht s
  obtain ⟨b, hb, hbmatch, hboutside⟩ := exists_optimalCapacityAssignment_reroot_path
    r htotal hr cost i₀ root a ha (m + 1) w hw hw0 p hpmatch hptight
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa only [w, Fin.snoc_last] using hb
  · simpa only [p, w, Fin.snoc_last, Fin.snoc_castSucc, hend] using hbmatch (Fin.last m)
  · intro s has hsk
    apply hboutside s
    rintro ⟨t, hts⟩
    have hpne : ∀ t, p t ≠ s := by
      intro t
      refine Fin.lastCases ?_ (fun z ↦ ?_) t
      · simpa only [p, Fin.snoc_last] using Ne.symm hsk
      · intro hzs
        have hqs : q z = s := by simpa only [p, Fin.snoc_castSucc] using hzs
        exact hout ⟨z.succ, (hmatch z).symm.trans ((congrArg a hqs).trans has)⟩
    exact hpne t hts

/-- Actual uniqueness of every quota optimum forces uniqueness of incoming tight edges,
including the retained-source row label. -/
theorem capacityVacancy_incoming_label_unique
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) a)
    (hunique : ∀ z b c,
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun s j ↦ cost (i₀.succAbove s) j) b →
      OptimalCapacityAssignment (capacityDeficit r z)
        (fun s j ↦ cost (i₀.succAbove s) j) c → b = c)
    (k l : Fin n) (u w : α) (hmatch : a k = a l)
    (hu : u ≠ a k) (hw : w ≠ a l)
    (hku : capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ u (hr u) = cost (i₀.succAbove k) u)
    (hlw : capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove l) -
      capacityVacancyPrice r htotal cost i₀ w (hr w) = cost (i₀.succAbove l) w) :
    k = l ∧ u = w := by
  have href b hb := hunique root b a hb ha
  obtain ⟨b, hb, hbk, _⟩ := exists_optimalCapacityAssignment_reroot_terminal_row
    r htotal hr cost i₀ root a ha href k u hu hku
  obtain ⟨c, hc, hcl, hcout⟩ := exists_optimalCapacityAssignment_reroot_terminal_row
    r htotal hr cost i₀ root a ha href l w hw hlw
  have hbc : b = c := hunique (a l) b c (hmatch ▸ hb) hc
  have hkl : k = l := by
    by_contra hkl
    exact hu (hbk.symm.trans ((congrFun hbc k).trans (hcout k hmatch hkl)))
  exact ⟨hkl, hbk.symm.trans ((congrFun hbc k).trans (hkl ▸ hcl))⟩

end OTSelector
