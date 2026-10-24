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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.CapacityCalibration

/-!
# Finite.TargetTreeCycles

**Conditions:** The reference quota-vacancy optimum is unique; the directed arcs come from actual common-dual tight alternatives.

**Objects:** The labelled tight graph and exclusion of simple directed target cycles.

**Proof detail:** Rotate the distinct source labels around a putative simple cycle; capacities and tight cost are preserved, producing another optimum, which uniqueness forces to coincide and contradicts the nontrivial cycle.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Reinhard Diestel, Graph Theory, 6th edition (2025)](https://diestel-graph-theory.com/Contents.pdf), Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# Cycle exclusion in the actual capacity vacancy tight graph

Fix an actual optimal quota allocation. A directed tight arc goes from an alternative
tight target to the row's matched target. A simple directed cycle would allow the
distinct rows along it to exchange partners cyclically. The resulting allocation has
the same capacities and remains tight for the actual common vacancy potentials.
Uniqueness of the actual quota optimizer therefore excludes every such cycle.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- The actual directed tight graph relative to a reference quota allocation. -/
def capacityVacancyTightArc
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (a : Fin n → α)
    (u v : α) : Prop :=
  u ≠ v ∧ ∃ k, a k = v ∧
    capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ u (hr u) = cost (i₀.succAbove k) u

/-- A row permutation supported on actual tight edges preserves the quota optimum.
Uniqueness then forces every resulting partner to remain the same. -/
theorem capacityVacancy_partners_eq_of_tight_rowPermutation
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun k l ↦ cost (i₀.succAbove k) l) a)
    (hunique : ∀ b, OptimalCapacityAssignment (capacityDeficit r root)
      (fun k l ↦ cost (i₀.succAbove k) l) b → b = a)
    (σ : Equiv.Perm (Fin n))
    (htight : ∀ k, capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ (a (σ k)) (hr (a (σ k))) =
        cost (i₀.succAbove k) (a (σ k))) :
    a ∘ σ = a := by
  apply hunique
  apply (optimalCapacityAssignment_iff_capacityVacancyPotentials_tight
    r htotal hr cost i₀ root (a ∘ σ)).mpr
  exact ⟨capacityFeasible_comp_perm _ a ha.1 σ, htight⟩

/-- Every simple directed cycle is excluded in the actual tight graph of a unique quota
optimum. The cycle's row permutation is constructed from its actual tight-edge witnesses. -/
theorem not_capacityVacancyTightArc_cycle
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (root : α)
    (a : Fin n → α)
    (ha : OptimalCapacityAssignment (capacityDeficit r root)
      (fun k l ↦ cost (i₀.succAbove k) l) a)
    (hunique : ∀ b, OptimalCapacityAssignment (capacityDeficit r root)
      (fun k l ↦ cost (i₀.succAbove k) l) b → b = a)
    (m : ℕ) (v : Fin (m + 2) → α) (hv : Function.Injective v) :
    ¬ ∀ t, capacityVacancyTightArc r htotal hr cost i₀ a
      (v t) (v (finRotate (m + 2) t)) := by
  classical
  intro hcycle
  let ρ := finRotate (m + 2)
  choose k hkmatch hktight using fun t ↦ (hcycle t).2
  have hk : Function.Injective k := by
    intro s t hst
    apply ρ.injective
    apply hv
    exact (hkmatch s).symm.trans ((congrArg a hst).trans (hkmatch t))
  let e : Fin (m + 2) ↪ Fin n := ⟨k, hk⟩
  let σ : Equiv.Perm (Fin n) := Equiv.Perm.viaEmbedding ρ.symm e
  have hlabel (t : Fin (m + 2)) : a (σ (e t)) = v t := by
    rw [show σ (e t) = e (ρ.symm t) from Equiv.Perm.viaEmbedding_apply ρ.symm e t]
    exact (hkmatch (ρ.symm t)).trans (congrArg v (ρ.apply_symm_apply t))
  have htight (s : Fin n) :
      capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove s) -
        capacityVacancyPrice r htotal cost i₀ (a (σ s)) (hr (a (σ s))) =
          cost (i₀.succAbove s) (a (σ s)) := by
    by_cases hs : s ∈ Set.range e
    · obtain ⟨t, rfl⟩ := hs
      have hlabel' : a (σ (k t)) = v t := hlabel t
      simpa only [e, Function.Embedding.coeFn_mk, hlabel'] using hktight t
    · have hσs : σ s = s := Equiv.Perm.viaEmbedding_apply_of_notMem ρ.symm e s hs
      simpa only [hσs] using
        capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ root a ha s
  have heq := capacityVacancy_partners_eq_of_tight_rowPermutation
    r htotal hr cost i₀ root a ha hunique σ htight
  have h0 : a (σ (e 0)) = a (e 0) := congrFun heq (e 0)
  exact (hcycle 0).1 ((hlabel 0).symm.trans (h0.trans (hkmatch 0)))

end OTSelector
