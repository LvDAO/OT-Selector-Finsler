import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.BlockLeafAssembly
import OTSelector.Finite.BlockMatchingComparison
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Finite.BlockRepair
import OTSelector.Finite.HierarchicalAssignment
import OTSelector.Finite.PartialMatching

/-!
# Finite.MaxCardValueBlockRepair

**Conditions:** A finite nested partition hierarchy has a constant root label; costs are nonnegative and within-cell repair costs obey the stated level bounds.

**Objects:** Cell discrepancies, optimal leaf-block sum and the telescoping hierarchical repair bound.

**Proof detail:** Use the block-optimal leaf union as the initial matching, apply deterministic coarse-scale repairs, and bound the global infimum by this full-cardinality competitor.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Optimal block value plus hierarchical repair

Combines the hierarchical repair lemma with the block-optimal leaf matching to
bound the optimal maximum-cardinality value by the sum of the leaf-block
optimal values plus the repair telescoping sum.  This is the deterministic core
of both the Euclidean and the marked-pressure block comparisons.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector
open Reconstruction

/-- The total absolute cell-count discrepancy of two point sequences at one
level of a nested cell hierarchy. -/
def cellDiscrepancy {X : Type*} {C : Type*} [Fintype C] [DecidableEq C]
    (cell : X → C) {a b : ℕ} (x : Fin a → X) (y : Fin b → X) : ℝ :=
  ∑ c : C, |partitionCount (cell ∘ x) c - partitionCount (cell ∘ y) c|

theorem cellDiscrepancy_nonneg {X : Type*} {C : Type*} [Fintype C] [DecidableEq C]
    (cell : X → C) {a b : ℕ} (x : Fin a → X) (y : Fin b → X) :
    0 ≤ cellDiscrepancy cell x y :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **Optimal block value plus hierarchical repair.**  If `σ0` is the matching
that is optimal in every leaf block, then the global optimal
maximum-cardinality value is at most the sum of the leaf-block optimal values
plus the telescoping repair sum.  All edge costs are assumed nonnegative. -/
theorem maxCardValue_le_blockSum_add_repair
    {X : Type*} {K : ℕ} {C : ℕ → Type*}
    [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (cell : (k : ℕ) → X → C k)
    (hnested : ∀ (k l : ℕ), k ≤ l → ∀ u v : X,
      cell l u = cell l v → cell k u = cell k v)
    {a b : ℕ} (x : Fin a → X) (y : Fin b → X)
    (cost : Fin a → Fin b → ℝ) (hnonneg : ∀ i j, 0 ≤ cost i j)
    (B : ℕ → ℝ)
    (hB : ∀ (k : ℕ), k < K → ∀ i j,
      cell k (x i) = cell k (y j) → cost i j ≤ B (k + 1))
    (hroot : ∀ u v : X, cell 0 u = cell 0 v) :
    PartialMatching.maxCardValue cost ≤
      (∑ c : C K,
        PartialMatching.maxCardValue
          (blockCost (fun i : Fin a => cell K (x i))
            (fun j : Fin b => cell K (y j)) cost c))
      + ∑ k ∈ Finset.range (K + 1), if 0 < k then
          B k * (1 / 2 : ℝ) *
            (cellDiscrepancy (cell k) x y - cellDiscrepancy (cell (k - 1)) x y)
        else 0 := by
  classical
  let blockS : Fin a → C K := fun i => cell K (x i)
  let blockT : Fin b → C K := fun j => cell K (y j)
  let σ0 : PartialMatching a b := blockPartialMatching blockS blockT cost
  have hmax : ∀ c : C K,
      (σ0.edges.filter (fun e => blockS e.1 = c)).card =
        min ((Finset.univ.filter (fun i => blockS i = c)).card)
            ((Finset.univ.filter (fun j => blockT j = c)).card) := by
    intro c
    have h := card_blockPartialMatching_filter (blockS := blockS) (blockT := blockT)
      (c := cost) c
    simpa only [blockSizeS, blockSizeT, blockFinset] using h
  have hleaf : ∀ e ∈ σ0.edges, cell K (x e.1) = cell K (y e.2) := by
    intro e he
    exact blockPartialMatching_edges_same_block (blockS := blockS) (blockT := blockT)
      (c := cost) (e := e) he
  obtain ⟨σ, hσcard, hσcost⟩ :=
    exists_maxCardMatching_le_add_hierarchical_repair
      (X := X) (K := K) (C := C) (cell := cell) (hnested := hnested)
      x y cost σ0 hleaf hmax (B := B) hB hroot
  have hle : PartialMatching.maxCardValue cost ≤ σ.cost cost :=
    PartialMatching.maxCardValue_le cost hσcard hnonneg
  have hσ0 : σ0.cost cost =
      ∑ c : C K,
        PartialMatching.maxCardValue (blockCost blockS blockT cost c) :=
    cost_blockPartialMatching blockS blockT cost
  calc PartialMatching.maxCardValue cost
      ≤ σ.cost cost := hle
    _ ≤ σ0.cost cost +
        ∑ k ∈ Finset.range (K + 1), if 0 < k then
          B k * (1 / 2 : ℝ) *
            (cellDiscrepancy (cell k) x y - cellDiscrepancy (cell (k - 1)) x y)
        else 0 := hσcost
    _ = _ := by rw [hσ0]

end OTSelector
