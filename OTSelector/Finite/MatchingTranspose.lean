import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.MaxCardValueStability
import OTSelector.Finite.PartialMatching

/-!
## Lemma skeleton

* **Conditions:** Finite bipartite matchings and real costs; pointwise bounds for cost estimates.
* **Objects:** Transposed matchings, their cardinalities/costs and empty/extended dimensions.
* **Proof detail:** Swap edge coordinates and reindex finite costs; use free-coordinate extension and the empty sum.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** These are direct representation consequences of the bipartite matching definition; no transposition theorem with these exact APIs is asserted in Diestel.
-/

/-!
# Transposition and target extension for finite partial matchings

The constructions in this module exchange the two parts of a finite bipartite matching.
They preserve cardinality and the total objective after transposing the cost matrix.
Consequently source-extension estimates also give target-extension estimates.

Source: Diestel, *Graph Theory*, 4th electronic edition (2010, corrected 2012), Chapter 2 opening
matching definition and §2.1 “Matching in bipartite graphs”:
<https://diestel-graph-theory.com/Sample.pdf#page=2>. The row/column bijections and cost identities
below are elementary consequences of that definition for the project's finite matrix encoding;
the book does not state these encoding-specific lemmas.
-/

open scoped BigOperators
noncomputable section
namespace OTSelector

namespace PartialMatching

variable {m n : ℕ}

/-- Transpose a partial matching. -/
def swapMatching (σ : PartialMatching m n) : PartialMatching n m where
  edges := σ.edges.image (fun p => (p.2, p.1))
  row_inj := by
    intro e he e' he' hrow
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he'
    have hcol : x.2 = y.2 := hrow
    have hxy : x = y := σ.col_inj x hx y hy hcol
    rw [hxy]
  col_inj := by
    intro e he e' he' hcol
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he'
    have hrow : x.1 = y.1 := hcol
    have hxy : x = y := σ.row_inj x hx y hy hrow
    rw [hxy]

/-- Transposing preserves the cardinality. -/
theorem card_swapMatching (σ : PartialMatching m n) :
    (swapMatching σ).card = σ.card := by
  classical
  unfold card swapMatching
  rw [Finset.card_image_of_injOn]
  intro x _ y _ h
  have h1 : x.2 = y.2 := congrArg Prod.fst h
  have h2 : x.1 = y.1 := congrArg Prod.snd h
  exact Prod.ext h2 h1

/-- Transposing preserves the total cost of the transposed matrix. -/
theorem cost_swapMatching (σ : PartialMatching m n) (c : Fin m → Fin n → ℝ) :
    (swapMatching σ).cost (fun j : Fin n => fun i : Fin m => c i j) = σ.cost c := by
  classical
  unfold cost swapMatching
  rw [Finset.sum_image]
  intro x _ y _ h
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

/-- The maximum-cardinality value is invariant under transposition. -/
theorem maxCardValue_comm (c : Fin m → Fin n → ℝ) :
    maxCardValue (fun j : Fin n => fun i : Fin m => c i j) = maxCardValue c := by
  classical
  have hset : {v : ℝ | ∃ σ : PartialMatching n m, σ.card = min n m ∧
        v = σ.cost (fun j : Fin n => fun i : Fin m => c i j)}
      = {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c} := by
    ext v
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨swapMatching σ, ?_, (cost_swapMatching σ (fun j i => c i j)).symm⟩
      rw [card_swapMatching, hσ, Nat.min_comm]
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨swapMatching σ, ?_, (cost_swapMatching σ c).symm⟩
      rw [card_swapMatching, hσ, Nat.min_comm]
  unfold maxCardValue
  rw [hset]

/-- A maximum-cardinality value with no rows is zero. -/
theorem maxCardValue_of_empty_rows {n : ℕ} (c : Fin 0 → Fin n → ℝ) :
    maxCardValue c = 0 := by
  have h := maxCardValue_comm c
  rw [maxCardValue_of_empty_cols (fun j : Fin n => fun i : Fin 0 => c i j)] at h
  exact h.symm

/-- Removing `δ` target points changes the maximum-cardinality value by at most
`2 B δ`, when all edge costs are bounded by `B` in absolute value. -/
theorem abs_maxCardValue_sub_le_add_cols {a b δ : ℕ} (c : Fin a → Fin (b + δ) → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    |maxCardValue c -
      maxCardValue (fun i : Fin a => fun j : Fin b =>
        c i (Fin.castLE (Nat.le_add_right b δ) j))| ≤ 2 * B * (δ : ℝ) := by
  have h := abs_maxCardValue_sub_le_add_rows (a := b) (δ := δ) (b := a)
    (c := fun j : Fin (b + δ) => fun i : Fin a => c i j) hB0
    (fun j i => hB i j)
  have ht : maxCardValue (fun j : Fin (b + δ) => fun i : Fin a => c i j) =
      maxCardValue c := maxCardValue_comm c
  have ht' : maxCardValue (fun j : Fin b => fun i : Fin a =>
        c i (Fin.castLE (Nat.le_add_right b δ) j)) =
      maxCardValue (fun i : Fin a => fun j : Fin b =>
        c i (Fin.castLE (Nat.le_add_right b δ) j)) :=
    maxCardValue_comm (fun i : Fin a => fun j : Fin b =>
      c i (Fin.castLE (Nat.le_add_right b δ) j))
  rw [ht, ht'] at h
  exact h

end PartialMatching

end OTSelector
