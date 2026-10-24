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

/-!
# Finite.TargetTreePaths

**Conditions:** An injective finite target path starts at the reference vacancy and its source labels satisfy the actual tight-edge equations.

**Objects:** Vacancy rerooting by rotating labelled source rows along the path.

**Proof detail:** Insert the omitted source, cyclically reassign the path rows and check all quota counts; retain common-dual tightness to obtain an optimum with vacancy at the terminal target and unchanged off-path rows.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Reinhard Diestel, Graph Theory, 6th edition (2025)](https://diestel-graph-theory.com/Contents.pdf), Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Actual labelled tight paths and vacancy rerooting

A simple path in the actual common tight graph carries retained-source labels. Rotating
these rows together with the missing source produces a full capacity allocation; deleting
the missing source then gives an actual optimal allocation with vacancy at the path's end.
The construction records both changed and unchanged rows, without a tree assumption.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

omit [Fintype α] in
/-- Filling the missing row at the vacant target restores the full capacities. -/
theorem capacityFeasible_insertNth_vacancy
    (r : α → ℕ) (hr : ∀ j, 0 < r j) (root : α) (a : Fin n → α)
    (ha : CapacityFeasible (capacityDeficit r root) a) (i : Fin (n + 1)) :
    CapacityFeasible r (Fin.insertNth i root a) := by
  intro j
  have hcard {N : ℕ} (f : Fin N → α) :
      Fintype.card {k // f k = j} = ∑ k, if f k = j then 1 else 0 := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  rw [hcard, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [← hcard, ha]
  have hj := hr j
  by_cases h : root = j
  · subst j
    simp only [capacityDeficit, ↓reduceIte]
    omega
  · simp [capacityDeficit, h, Ne.symm h]

/-- A simple labelled tight path reroots an actual vacancy optimum. Every selected row
moves to the previous path vertex, and every unselected row keeps its original target. -/
theorem exists_optimalCapacityAssignment_reroot_path
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun s j ↦ cost (i₀.succAbove s) j) a)
    (m : ℕ) (v : Fin (m + 1) → α) (hv : Function.Injective v) (hroot : v 0 = root)
    (k : Fin m → Fin n) (hmatch : ∀ t, a (k t) = v t.succ)
    (htight : ∀ t,
      capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove (k t)) -
        capacityVacancyPrice r htotal cost i₀ (v t.castSucc) (hr (v t.castSucc)) =
          cost (i₀.succAbove (k t)) (v t.castSucc)) :
    ∃ b : Fin n → α,
      OptimalCapacityAssignment (capacityDeficit r (v (Fin.last m)))
        (fun s j ↦ cost (i₀.succAbove s) j) b ∧
      (∀ t, b (k t) = v t.castSucc) ∧
      (∀ s, s ∉ Set.range k → b s = a s) := by
  classical
  have hk : Function.Injective k := by
    intro s t hst
    apply Fin.succ_injective
    apply hv
    exact (hmatch s).symm.trans ((congrArg a hst).trans (hmatch t))
  let A : Fin (n + 1) → α := Fin.insertNth i₀ root a
  have hA : CapacityFeasible r A := capacityFeasible_insertNth_vacancy r hr root a ha.1 i₀
  let e : Fin (m + 1) ↪ Fin (n + 1) :=
    ⟨Fin.cons i₀ (fun t ↦ i₀.succAbove (k t)),
      Fin.cons_injective_of_injective
        (by rintro ⟨t, ht⟩; exact Fin.succAbove_ne i₀ (k t) ht)
        (i₀.succAbove_right_injective.comp hk)⟩
  have he0 : e 0 = i₀ := rfl
  have hes (t : Fin m) : e t.succ = i₀.succAbove (k t) := rfl
  have hAv (t : Fin (m + 1)) : A (e t) = v t := by
    refine Fin.cases ?_ (fun s ↦ ?_) t
    · simpa only [he0, A, Fin.insertNth_apply_same] using hroot.symm
    · simpa only [hes, A, Fin.insertNth_apply_succAbove] using hmatch s
  let ρ := finRotate (m + 1)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.viaEmbedding ρ.symm e
  have hσ (t : Fin (m + 1)) : σ (e t) = e (ρ.symm t) :=
    Equiv.Perm.viaEmbedding_apply ρ.symm e t
  have hρ0 : ρ.symm 0 = Fin.last m := by
    apply ρ.injective
    simpa only [Equiv.apply_symm_apply] using (finRotate_last (n := m)).symm
  have hρs (t : Fin m) : ρ.symm t.succ = t.castSucc := by
    apply ρ.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    rw [show ρ = finRotate (m + 1) from rfl,
      coe_finRotate_of_ne_last (Fin.castSucc_ne_last t)]
    rfl
  let b : Fin n → α := fun s ↦ A (σ (i₀.succAbove s))
  have hB0 : (A ∘ σ) i₀ = v (Fin.last m) := by
    change A (σ i₀) = _
    rw [← he0, hσ, hρ0, hAv]
  have hbmatch (t : Fin m) : b (k t) = v t.castSucc := by
    change A (σ (i₀.succAbove (k t))) = _
    rw [← hes, hσ, hρs, hAv]
  have hboutside (s : Fin n) (hs : s ∉ Set.range k) : b s = a s := by
    have hse : i₀.succAbove s ∉ Set.range e := by
      rintro ⟨t, ht⟩
      have hne : ∀ t, e t ≠ i₀.succAbove s := by
        intro t
        refine Fin.cases ?_ (fun u ↦ ?_) t
        · intro heq
          exact (Fin.succAbove_ne i₀ s) (he0.symm.trans heq).symm
        · intro heq
          apply hs
          exact ⟨u, i₀.succAbove_right_injective ((hes u).symm.trans heq)⟩
      exact hne t ht
    change A (σ (i₀.succAbove s)) = _
    rw [show σ (i₀.succAbove s) = i₀.succAbove s from
      Equiv.Perm.viaEmbedding_apply_of_notMem ρ.symm e _ hse]
    simp only [A, Fin.insertNth_apply_succAbove]
  refine ⟨b, ?_, hbmatch, hboutside⟩
  apply (optimalCapacityAssignment_iff_capacityVacancyPotentials_tight
    r htotal hr cost i₀ (v (Fin.last m)) b).mpr
  refine ⟨?_, ?_⟩
  · have hB := capacityFeasible_delete r (A ∘ σ)
      (capacityFeasible_comp_perm r A hA σ) i₀
    simpa only [hB0, b, Function.comp_apply] using hB
  · intro s
    by_cases hs : s ∈ Set.range k
    · obtain ⟨t, rfl⟩ := hs
      simpa only [hbmatch] using htight t
    · simpa only [hboutside s hs] using
        capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ root a ha s

end OTSelector
