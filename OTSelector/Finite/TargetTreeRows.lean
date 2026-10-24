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
import OTSelector.Finite.TargetTreeIncoming
import OTSelector.Finite.TargetTreeReachability
import OTSelector.Finite.TargetTreeSimplePaths

/-!
# Finite.TargetTreeRows

**Conditions:** Finite positive quotas and uniqueness for every actual quota-vacancy optimum.

**Objects:** Canonical rows with multiple tight targets, one row per nonroot target, and strict rows with counts rj−1.

**Proof detail:** Combine rooted reachability and incoming-edge uniqueness to biject flexible rows with nonroot targets; count their fibers, identify their two tight targets, and use common tight calibration to fix all remaining rows in every vacancy optimum.

**Sources:** [Reinhard Diestel, Graph Theory, 6th edition (2025)](https://diestel-graph-theory.com/Contents.pdf), Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Jürgen Richter-Gebert; Bernd Sturmfels; Thorsten Theobald, First steps in tropical geometry (arXiv:math/0306366v2, 2003)](https://arxiv.org/html/math/0306366v2#S5), Section 5, proof of Theorem 5.3 in the n=k+1 case and Corollary 5.4; [OTSelector project, The one-hole target tree](main.tex#prop:highd-cavity-tree), main.tex label prop:highd-cavity-tree, line 4159.

Source relation (composition): The classical linkage-tree argument is in Richter-Gebert–Sturmfels–Theobald Section 5, proof of Theorem 5.3 and Corollary 5.4; main.tex prop:highd-cavity-tree proves the actual real-cost one-hole statement. This module derives the displayed integer-quota/labelled-row refinement using common-dual tightness, explicit counts and the stated uniqueness assumptions; it does not claim a verbatim quota theorem from either source.
-/

/-!
# The canonical actual capacity tree rows

The rows with more than one actual tight target are intrinsic to the common vacancy
potentials. Under actual quota uniqueness, their reference partners biject with the
nonroot targets. Every such row has exactly two tight targets; all other rows are strict
and occupy target `j` exactly `r j - 1` times.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- A retained row belongs to the actual target tree when it has a tight alternative
to its partner in the reference quota optimum. -/
def capacityVacancyTreeRow
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) (i₀ : Fin (n + 1)) (a : Fin n → α) (k : Fin n) : Prop :=
  ∃ u, u ≠ a k ∧
    capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
      capacityVacancyPrice r htotal cost i₀ u (hr u) = cost (i₀.succAbove k) u

section Tree

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

include ha hunique

/-- No tree row is assigned to the reference vacant target. -/
theorem capacityVacancyTreeRow_partner_ne_root (k : Fin n) (hk : T k) : a k ≠ root := by
  rintro hroot
  obtain ⟨u, hu, ht⟩ := hk
  apply not_capacityVacancyTightArc_to_root r htotal hr cost i₀ root a ha
    (fun b hb ↦ hunique root b a hb ha) u
  exact hroot ▸ ⟨hu, k, rfl, ht⟩

/-- Every nonroot target has a unique actual tree row assigned to it. -/
theorem existsUnique_capacityVacancyTreeRow_partner (z : α) (hz : z ≠ root) :
    ∃! k : Fin n, T k ∧ a k = z := by
  have hreach := capacityVacancyTightArc_reachable r htotal hr cost i₀ root a ha z
  obtain hzr | ⟨u, _, hu⟩ := hreach.cases_tail
  · exact (hz hzr).elim
  obtain ⟨hne, k, hmatch, ht⟩ := hu
  have hk : T k := ⟨u, hmatch ▸ hne, ht⟩
  refine ⟨k, ⟨hk, hmatch⟩, ?_⟩
  rintro l ⟨⟨w, hw, htl⟩, hl⟩
  exact (capacityVacancy_incoming_label_unique r htotal hr cost i₀ root a ha hunique
    l k w u (hl.trans hmatch.symm) hw (hmatch ▸ hne) htl ht).1

/-- The actual tree contains precisely one fewer row than there are targets. -/
theorem card_capacityVacancyTreeRows :
    Nat.card {k : Fin n // T k} = Fintype.card α - 1 := by
  classical
  let f : {k : Fin n // T k} → {z : α // z ≠ root} := fun k ↦
    ⟨a k, capacityVacancyTreeRow_partner_ne_root r htotal hr cost i₀ root a ha hunique k k.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro k l hkl
      apply Subtype.ext
      obtain ⟨q, _, hq⟩ := existsUnique_capacityVacancyTreeRow_partner
        r htotal hr cost i₀ root a ha hunique (a k)
        (capacityVacancyTreeRow_partner_ne_root r htotal hr cost i₀ root a ha hunique k k.2)
      exact (hq k ⟨k.2, rfl⟩).trans
        (hq l ⟨l.2, (congrArg Subtype.val hkl).symm⟩).symm
    · intro z
      obtain ⟨k, hk, _⟩ := existsUnique_capacityVacancyTreeRow_partner
        r htotal hr cost i₀ root a ha hunique z z.2
      exact ⟨⟨k, hk.1⟩, Subtype.ext hk.2⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (Equiv.ofBijective f hf)]
  simp

/-- A tree row has precisely its matched target and one distinct tight alternative. -/
theorem capacityVacancyTreeRow_two_tight_targets (k : Fin n) (hk : T k) :
    ∃ u, u ≠ a k ∧ ∀ j,
      (capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
        capacityVacancyPrice r htotal cost i₀ j (hr j) = cost (i₀.succAbove k) j) ↔
      j = a k ∨ j = u := by
  obtain ⟨u, hu, ht⟩ := hk
  refine ⟨u, hu, fun j ↦ ⟨?_, ?_⟩⟩
  · intro hj
    by_cases heq : j = a k
    · exact Or.inl heq
    · exact Or.inr (capacityVacancy_incoming_label_unique
        r htotal hr cost i₀ root a ha hunique k k j u rfl heq hu hj ht).2
  · rintro (rfl | rfl)
    · exact capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ root a ha k
    · exact ht

omit hunique in
/-- A row outside the canonical tree has exactly its original partner as a tight target. -/
theorem not_capacityVacancyTreeRow_iff_unique_tight (k : Fin n) :
    ¬ T k ↔ ∀ j,
      (capacityVacancyRowPotential r htotal hr cost i₀ (i₀.succAbove k) -
        capacityVacancyPrice r htotal cost i₀ j (hr j) = cost (i₀.succAbove k) j) ↔
      j = a k := by
  constructor
  · intro hk j
    constructor
    · intro hj
      by_contra hne
      exact hk ⟨j, hne, hj⟩
    · rintro rfl
      exact capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ root a ha k
  · rintro h ⟨j, hne, hj⟩
    exact hne ((h j).mp hj)

/-- The exact target counts of the tree rows. -/
theorem card_capacityVacancyTreeRow_fiber (j : α) :
    Nat.card {k : Fin n // T k ∧ a k = j} = if j = root then 0 else 1 := by
  classical
  rw [Nat.card_eq_fintype_card]
  split_ifs with hj
  · apply Fintype.card_eq_zero_iff.mpr
    refine ⟨?_⟩
    rintro ⟨k, hk, hkj⟩
    exact capacityVacancyTreeRow_partner_ne_root r htotal hr cost i₀ root a ha hunique
      k hk (hkj.trans hj)
  · obtain ⟨k, hk, hu⟩ := existsUnique_capacityVacancyTreeRow_partner
      r htotal hr cost i₀ root a ha hunique j hj
    exact Fintype.card_eq_one_iff.mpr ⟨⟨k, hk⟩, fun l ↦ Subtype.ext (hu l l.2)⟩

/-- Every target has exactly `r j - 1` strict rows, including the reference root. -/
theorem card_capacityVacancy_strict_fiber (j : α) :
    Nat.card {k : Fin n // ¬ T k ∧ a k = j} = r j - 1 := by
  classical
  let e : {k : Fin n // ¬ T k ∧ a k = j} ≃ {k : {s : Fin n // a s = j} // ¬ T k} :=
    { toFun := fun k ↦ ⟨⟨k, k.2.2⟩, k.2.1⟩
      invFun := fun k ↦ ⟨k.1, k.2, k.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e' : {k : {s : Fin n // a s = j} // T k} ≃ {k : Fin n // T k ∧ a k = j} :=
    { toFun := fun k ↦ ⟨k.1, k.2, k.1.2⟩
      invFun := fun k ↦ ⟨⟨k, k.2.2⟩, k.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun k : {s : Fin n // a s = j} ↦ T k),
    ha.1, Fintype.card_congr e', ← Nat.card_eq_fintype_card,
    card_capacityVacancyTreeRow_fiber r htotal hr cost i₀ root a ha hunique]
  by_cases hj : j = root <;> simp [capacityDeficit, hj]

omit hunique in
/-- Every actual vacancy optimum leaves each strict row at its reference partner. -/
theorem capacityVacancy_strict_row_fixed (z : α) (b : Fin n → α)
    (hb : OptimalCapacityAssignment (capacityDeficit r z)
      (fun s j ↦ cost (i₀.succAbove s) j) b) (k : Fin n) (hk : ¬ T k) : b k = a k := by
  apply ((not_capacityVacancyTreeRow_iff_unique_tight
    r htotal hr cost i₀ root a ha k).mp hk (b k)).mp
  exact capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ z b hb k

omit hunique in
/-- The canonical tree-row subset is independent of the reference vacancy and optimum. -/
theorem capacityVacancyTreeRow_iff_of_optimal (z : α) (b : Fin n → α)
    (hb : OptimalCapacityAssignment (capacityDeficit r z)
      (fun s j ↦ cost (i₀.succAbove s) j) b) (k : Fin n) :
    T k ↔ capacityVacancyTreeRow r htotal hr cost i₀ b k := by
  by_cases hab : a k = b k
  · simp only [capacityVacancyTreeRow, hab]
  · constructor <;> intro _
    · exact ⟨a k, hab,
        capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ root a ha k⟩
    · exact ⟨b k, Ne.symm hab,
        capacityVacancyPotentials_tight_of_optimal r htotal hr cost i₀ z b hb k⟩

end Tree
end OTSelector
