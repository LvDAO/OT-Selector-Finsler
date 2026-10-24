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
import OTSelector.Finite.BlockMatchingComparison
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Finite.PartialMatching

/-!
# Finite.BlockLeafAssembly

**Conditions:** Finite block fibers and the existing embedded optimal block matching construction.

**Objects:** The edges filtered to a block, their cardinality, and equality of source/target block labels.

**Proof detail:** Expand membership in the disjoint block union; label uniqueness identifies the filtered edge set with its one block, whose cardinality is the minimum of the block sizes.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Leaf assembly for the hierarchical block repair

The block decomposition of `BlockMaxValueComparison` constructs a matching that
is optimal inside every block.  This module records the two additional facts
needed to feed that matching into the multi-scale repair lemma of
`BlockRepair`: the edges lying in one block are exactly the ambient optimal
block edges, and their number is the minimum of the two block sizes.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {a b : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
  (blockS : Fin a → β) (blockT : Fin b → β) (c : Fin a → Fin b → ℝ)

/-- Membership in a block finset is equality of the block label. -/
theorem mem_blockFinset_iff {t : β} {i : Fin a} :
    i ∈ blockFinset blockS t ↔ blockS i = t :=
  mem_blockFinset

/-- Membership in a target block finset is equality of the target block label. -/
theorem mem_blockFinsetT_iff {t : β} {j : Fin b} :
    j ∈ blockFinset blockT t ↔ blockT j = t :=
  mem_blockFinset

/-- The edges of the block-optimal matching whose source lies in block `t` are
exactly the ambient edges of block `t`. -/
theorem blockPartialMatching_filter_eq (t : β) :
    ((blockPartialMatching blockS blockT c).edges.filter
        (fun e => blockS e.1 = t)) = blockEdgesAmbient blockS blockT c t := by
  classical
  ext e
  simp only [Finset.mem_filter, blockPartialMatching, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨s, hes⟩, hlabel⟩
    have hs : blockS e.1 = s := by
      simpa only [mem_blockFinset_iff] using
        fst_mem_blockEdgesAmbient blockS blockT c hes
    rw [hs] at hlabel
    rw [← hlabel]
    exact hes
  · intro he
    refine ⟨⟨t, he⟩, ?_⟩
    simpa only [mem_blockFinset_iff] using
      fst_mem_blockEdgesAmbient blockS blockT c he

/-- The source-block filter of the block-optimal matching has the minimum block
cardinality. -/
theorem card_blockPartialMatching_filter (t : β) :
    ((blockPartialMatching blockS blockT c).edges.filter
        (fun e => blockS e.1 = t)).card =
      min (blockSizeS blockS t) (blockSizeT blockT t) := by
  rw [blockPartialMatching_filter_eq, card_blockEdgesAmbient]

/-- The block-optimal matching stays inside the blocks. -/
theorem blockPartialMatching_edges_same_block {e : Fin a × Fin b}
    (he : e ∈ (blockPartialMatching blockS blockT c).edges) :
    blockS e.1 = blockT e.2 := by
  classical
  rw [blockPartialMatching, Finset.mem_biUnion] at he
  obtain ⟨t, -, het⟩ := he
  have h1 : blockS e.1 = t := by
    simpa only [mem_blockFinset_iff] using
      fst_mem_blockEdgesAmbient blockS blockT c het
  have h2 : blockT e.2 = t := by
    simpa only [mem_blockFinsetT_iff] using
      snd_mem_blockEdgesAmbient blockS blockT c het
  rw [h1, h2]

end OTSelector
