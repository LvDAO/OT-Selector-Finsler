import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.BlockMatchingComparison
import OTSelector.Finite.MatchingUnion
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching

/-!
# Finite.BlockMaxValueComparison

**Conditions:** Finite source and target sets may have different sizes, including zero; blocks are finite and costs may be signed, with c≤B and additionally B≥0 for the half-discrepancy bound.

**Objects:** Embedded block optimizers, their disjoint union, the free-endpoint repair and the global maximum-cardinality matching.

**Proof detail:** Attain and embed each block optimum, enumerate unused rows and columns, and append a diagonal repair; its edge count is the deficit of the sum of block minima, bounded by half the total absolute count discrepancy.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/



/-!
## Lemma skeleton

* **Conditions:** a and b are arbitrary natural source/target cardinalities, including empty clouds. beta is finite with decidable equality; blockS : Fin a -> beta and blockT : Fin b -> beta. All matching costs are real and may be signed. The basic comparison needs only c(i,j) <= B. The half-discrepancy corollary also requires 0 <= B.
* **Objects:** blockEmbeddingS,blockEmbeddingT: enumerations of the actual source and target block fibers; blockCost: c restricted along those finite block enumerations; optimalBlockMatching: an attained minimum-cost matching of maximum possible cardinality in a block; blockPartialMatching: the disjoint union of these block optima in the ambient index sets; residualBlockMatching: a diagonal matching of the unused source and target indices; assembledMatching: their union, of cardinality min a b; block discrepancy: sum_t abs(sourceSize_t-targetSize_t), a deterministic combinatorial quantity used in the final bound
* **Proof detail:** Attain each finite block value and embed its edges injectively into its original block rectangle. Use the disjoint label fibers to obtain one block matching with additive cardinality and cost. Enumerate unused rows and columns and match a diagonal of the two free sets; union it with the block part. Use the finite attained-value upper comparison for signed costs and bound the residual edge sum. Rewrite absolute differences of natural counts using s+t-2*min(s,t) and deduce the half-discrepancy bound.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean
* Sheldon Axler, *Supplement for Measure, Integration & Real Analysis*, Section C, Definitions 0.32 and 0.35, pp. 18–19.
  https://measure.axler.net/SupplementMIRA.pdf#page=18

**Relationship to the sources:** Block minima, disjoint union and free-endpoint repair are finite matching constructions. The signed-cost penalty and half-discrepancy coefficient are local arithmetic consequences, not named Diestel theorems.
-/

/-!
# Block decomposition of maximum-cardinality matching values

Two clouds are partitioned into common blocks.  Inside each block we take an
optimal maximum-cardinality matching; the unmatched points of all blocks are
then paired arbitrarily.  The union is a partial matching of global maximum
cardinality, and its cost is at most the sum of the block optimal values plus a
uniform edge bound times the number of residual points.

Unlike `BlockMatchingComparison`, the two clouds may have different sizes and
the block part is measured by `PartialMatching.maxCardValue`, so the estimate is
ready to be integrated over a random point process: the block values are exactly
the pressure functional, and the only stochastic correction is the histogram
discrepancy `∑ |#S_b - #T_b|`.

The main output is

`maxCardValue c ≤ ∑_b maxCardValue c_b + B * (#residual rows)`,

with `#residual rows = min (#rows - J) (#cols - J)`,
`J = ∑_b min (#S_b) (#T_b)`, and `#residual rows ≤ 1/2 ∑_b |#S_b - #T_b|`.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

section BlockDecomposition

variable {a b : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
  (blockS : Fin a → β) (blockT : Fin b → β) (c : Fin a → Fin b → ℝ)

/-- The enumeration of a source block used to identify it with `Fin #S_b`. -/
noncomputable def blockEmbeddingS (t : β) : Fin (blockSizeS blockS t) → Fin a :=
  fun i ↦ ((Finset.equivFin (blockFinset blockS t)).symm i).1

/-- The enumeration of a target block used to identify it with `Fin #T_b`. -/
noncomputable def blockEmbeddingT (t : β) : Fin (blockSizeT blockT t) → Fin b :=
  fun j ↦ ((Finset.equivFin (blockFinset blockT t)).symm j).1

omit [Fintype β] in
theorem blockEmbeddingS_mem (t : β) (i : Fin (blockSizeS blockS t)) :
    blockEmbeddingS blockS t i ∈ blockFinset blockS t :=
  ((Finset.equivFin (blockFinset blockS t)).symm i).2

omit [Fintype β] in
theorem blockEmbeddingT_mem (t : β) (j : Fin (blockSizeT blockT t)) :
    blockEmbeddingT blockT t j ∈ blockFinset blockT t :=
  ((Finset.equivFin (blockFinset blockT t)).symm j).2

omit [Fintype β] in
theorem blockEmbeddingS_injective (t : β) : Function.Injective (blockEmbeddingS blockS t) := by
  intro i j h
  have h' : (Finset.equivFin (blockFinset blockS t)).symm i =
      (Finset.equivFin (blockFinset blockS t)).symm j := Subtype.ext h
  exact (Finset.equivFin (blockFinset blockS t)).symm.injective h'

omit [Fintype β] in
theorem blockEmbeddingT_injective (t : β) : Function.Injective (blockEmbeddingT blockT t) := by
  intro i j h
  have h' : (Finset.equivFin (blockFinset blockT t)).symm i =
      (Finset.equivFin (blockFinset blockT t)).symm j := Subtype.ext h
  exact (Finset.equivFin (blockFinset blockT t)).symm.injective h'

/-- The cost restricted to one block, indexed by the block enumerations. -/
def blockCost (t : β) : Fin (blockSizeS blockS t) → Fin (blockSizeT blockT t) → ℝ :=
  fun i j ↦ c (blockEmbeddingS blockS t i) (blockEmbeddingT blockT t j)

/-- An optimal maximum-cardinality matching inside one block. -/
noncomputable def optimalBlockMatching (t : β) :
    PartialMatching (blockSizeS blockS t) (blockSizeT blockT t) :=
  (PartialMatching.exists_cost_eq_maxCardValue (blockCost blockS blockT c t)).choose

omit [Fintype β] in
theorem card_optimalBlockMatching (t : β) :
    (optimalBlockMatching blockS blockT c t).edges.card =
      min (blockSizeS blockS t) (blockSizeT blockT t) := by
  unfold optimalBlockMatching
  exact (PartialMatching.exists_cost_eq_maxCardValue (blockCost blockS blockT c t)).choose_spec.1

omit [Fintype β] in
theorem cost_optimalBlockMatching (t : β) :
    (optimalBlockMatching blockS blockT c t).cost (blockCost blockS blockT c t) =
      PartialMatching.maxCardValue (blockCost blockS blockT c t) := by
  unfold optimalBlockMatching
  exact (PartialMatching.exists_cost_eq_maxCardValue (blockCost blockS blockT c t)).choose_spec.2

/-- The edges of the block optimum, pushed back to the ambient index sets. -/
noncomputable def blockEdgesAmbient (t : β) : Finset (Fin a × Fin b) :=
  (optimalBlockMatching blockS blockT c t).edges.image fun e ↦
    (blockEmbeddingS blockS t e.1, blockEmbeddingT blockT t e.2)

theorem blockEdgesAmbient_injOn (t : β) :
    Set.InjOn (fun e : Fin (blockSizeS blockS t) × Fin (blockSizeT blockT t) ↦
      (blockEmbeddingS blockS t e.1, blockEmbeddingT blockT t e.2))
      ↑(optimalBlockMatching blockS blockT c t).edges := by
  intro e _ e' _ h
  have h1 : blockEmbeddingS blockS t e.1 = blockEmbeddingS blockS t e'.1 :=
    congrArg Prod.fst h
  have h2 : blockEmbeddingT blockT t e.2 = blockEmbeddingT blockT t e'.2 :=
    congrArg Prod.snd h
  exact Prod.ext (blockEmbeddingS_injective blockS t h1)
    (blockEmbeddingT_injective blockT t h2)

theorem card_blockEdgesAmbient (t : β) :
    (blockEdgesAmbient blockS blockT c t).card =
      min (blockSizeS blockS t) (blockSizeT blockT t) := by
  unfold blockEdgesAmbient
  rw [Finset.card_image_of_injOn (blockEdgesAmbient_injOn blockS blockT c t),
    card_optimalBlockMatching]

theorem fst_mem_blockEdgesAmbient {t : β} {e : Fin a × Fin b}
    (he : e ∈ blockEdgesAmbient blockS blockT c t) :
    e.1 ∈ blockFinset blockS t := by
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp he
  rw [← congrArg Prod.fst hx]
  exact blockEmbeddingS_mem blockS t x.1

theorem snd_mem_blockEdgesAmbient {t : β} {e : Fin a × Fin b}
    (he : e ∈ blockEdgesAmbient blockS blockT c t) :
    e.2 ∈ blockFinset blockT t := by
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp he
  rw [← congrArg Prod.snd hx]
  exact blockEmbeddingT_mem blockT t x.2

theorem sum_blockEdgesAmbient (t : β) :
    ∑ e ∈ blockEdgesAmbient blockS blockT c t, c e.1 e.2 =
      PartialMatching.maxCardValue (blockCost blockS blockT c t) := by
  unfold blockEdgesAmbient
  rw [Finset.sum_image (blockEdgesAmbient_injOn blockS blockT c t)]
  change ∑ e ∈ (optimalBlockMatching blockS blockT c t).edges,
      blockCost blockS blockT c t e.1 e.2 = _
  rw [← cost_optimalBlockMatching blockS blockT c t]
  rfl

theorem blockEdgesAmbient_pairwiseDisjoint :
    Set.PairwiseDisjoint ((Finset.univ : Finset β) : Set β)
      (blockEdgesAmbient blockS blockT c) := by
  intro s _ t _ hst
  apply Finset.disjoint_left.mpr
  intro e hes het
  have h1 : e.1 ∈ blockFinset blockS s := fst_mem_blockEdgesAmbient blockS blockT c hes
  have h2 : e.1 ∈ blockFinset blockS t := fst_mem_blockEdgesAmbient blockS blockT c het
  simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  exact hst (h1.symm.trans h2)

/-- The block part of the constructed matching. -/
noncomputable def blockPartialMatching : PartialMatching a b where
  edges := Finset.univ.biUnion (blockEdgesAmbient blockS blockT c)
  row_inj := by
    intro e he e' he' hrow
    rw [Finset.mem_biUnion] at he he'
    obtain ⟨s, -, hes⟩ := he
    obtain ⟨t, -, het⟩ := he'
    obtain ⟨x, hxmem, hx⟩ := Finset.mem_image.mp hes
    obtain ⟨y, hymem, hy⟩ := Finset.mem_image.mp het
    have hval : blockEmbeddingS blockS s x.1 = blockEmbeddingS blockS t y.1 := by
      have h := hrow
      rw [← hx, ← hy] at h
      exact h
    have hs : blockS (blockEmbeddingS blockS s x.1) = s := by
      have := blockEmbeddingS_mem blockS s x.1
      simpa only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have ht : blockS (blockEmbeddingS blockS t y.1) = t := by
      have := blockEmbeddingS_mem blockS t y.1
      simpa only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hst : s = t := by rw [← hs, ← ht, hval]
    cases hst
    have hrow' : x.1 = y.1 := blockEmbeddingS_injective blockS s hval
    have hxye : x = y := (optimalBlockMatching blockS blockT c s).row_inj x hxmem y hymem hrow'
    rw [← hx, ← hy, hxye]
  col_inj := by
    intro e he e' he' hcol
    rw [Finset.mem_biUnion] at he he'
    obtain ⟨s, -, hes⟩ := he
    obtain ⟨t, -, het⟩ := he'
    obtain ⟨x, hxmem, hx⟩ := Finset.mem_image.mp hes
    obtain ⟨y, hymem, hy⟩ := Finset.mem_image.mp het
    have hval : blockEmbeddingT blockT s x.2 = blockEmbeddingT blockT t y.2 := by
      have h := hcol
      rw [← hx, ← hy] at h
      exact h
    have hs : blockT (blockEmbeddingT blockT s x.2) = s := by
      have := blockEmbeddingT_mem blockT s x.2
      simpa only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have ht : blockT (blockEmbeddingT blockT t y.2) = t := by
      have := blockEmbeddingT_mem blockT t y.2
      simpa only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hst : s = t := by rw [← hs, ← ht, hval]
    cases hst
    have hcol' : x.2 = y.2 := blockEmbeddingT_injective blockT s hval
    have hxye : x = y := (optimalBlockMatching blockS blockT c s).col_inj x hxmem y hymem hcol'
    rw [← hx, ← hy, hxye]

theorem card_blockPartialMatching :
    (blockPartialMatching blockS blockT c).card =
      ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t) := by
  simp only [PartialMatching.card, blockPartialMatching]
  rw [Finset.card_biUnion (blockEdgesAmbient_pairwiseDisjoint blockS blockT c)]
  simp only [card_blockEdgesAmbient]

theorem cost_blockPartialMatching :
    (blockPartialMatching blockS blockT c).cost c =
      ∑ t, PartialMatching.maxCardValue (blockCost blockS blockT c t) := by
  unfold PartialMatching.cost blockPartialMatching
  rw [Finset.sum_biUnion (blockEdgesAmbient_pairwiseDisjoint blockS blockT c)]
  simp only [sum_blockEdgesAmbient]

end BlockDecomposition

section Residual

variable {a b : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
  (blockS : Fin a → β) (blockT : Fin b → β) (c : Fin a → Fin b → ℝ)

/-- The matching of the points left unmatched by the block part. -/
noncomputable def residualBlockMatching : PartialMatching a b :=
  let σ := blockPartialMatching blockS blockT c
  let rs := σ.freeRows
  let rt := σ.freeCols
  { edges := (PartialMatching.diagonal rs.card rt.card).edges.image fun e ↦
      (((Finset.equivFin rs).symm e.1).1, ((Finset.equivFin rt).symm e.2).1)
    row_inj := by
      intro e he e' he' hrow
      obtain ⟨x, hxmem, hx⟩ := Finset.mem_image.mp he
      obtain ⟨y, hymem, hy⟩ := Finset.mem_image.mp he'
      have hval : ((Finset.equivFin rs).symm x.1).1 = ((Finset.equivFin rs).symm y.1).1 := by
        have h := hrow
        rw [← hx, ← hy] at h
        exact h
      have hxyeq : ((Finset.equivFin rs).symm x.1) = ((Finset.equivFin rs).symm y.1) :=
        Subtype.ext hval
      have hxy : x.1 = y.1 := (Finset.equivFin rs).symm.injective hxyeq
      have hxy' : x = y := (PartialMatching.diagonal rs.card rt.card).row_inj x hxmem y hymem hxy
      rw [← hx, ← hy, hxy']
    col_inj := by
      intro e he e' he' hcol
      obtain ⟨x, hxmem, hx⟩ := Finset.mem_image.mp he
      obtain ⟨y, hymem, hy⟩ := Finset.mem_image.mp he'
      have hval : ((Finset.equivFin rt).symm x.2).1 = ((Finset.equivFin rt).symm y.2).1 := by
        have h := hcol
        rw [← hx, ← hy] at h
        exact h
      have hxyeq : ((Finset.equivFin rt).symm x.2) = ((Finset.equivFin rt).symm y.2) :=
        Subtype.ext hval
      have hxy : x.2 = y.2 := (Finset.equivFin rt).symm.injective hxyeq
      have hxy' : x = y := (PartialMatching.diagonal rs.card rt.card).col_inj x hxmem y hymem hxy
      rw [← hx, ← hy, hxy'] }

theorem residualBlockMatching_edges :
    (residualBlockMatching blockS blockT c).edges =
      (PartialMatching.diagonal (blockPartialMatching blockS blockT c).freeRows.card
        (blockPartialMatching blockS blockT c).freeCols.card).edges.image (fun e ↦
        (((Finset.equivFin (blockPartialMatching blockS blockT c).freeRows).symm e.1).1,
         ((Finset.equivFin (blockPartialMatching blockS blockT c).freeCols).symm e.2).1)) :=
  rfl

theorem card_residualBlockMatching :
    (residualBlockMatching blockS blockT c).card =
      min ((blockPartialMatching blockS blockT c).freeRows.card)
        ((blockPartialMatching blockS blockT c).freeCols.card) := by
  simp only [PartialMatching.card, residualBlockMatching]
  rw [Finset.card_image_of_injOn]
  · exact PartialMatching.card_diagonal _ _
  · intro e _ e' _ h
    have h1 : ((Finset.equivFin (blockPartialMatching blockS blockT c).freeRows).symm e.1).1 =
        ((Finset.equivFin (blockPartialMatching blockS blockT c).freeRows).symm e'.1).1 :=
      congrArg Prod.fst h
    have h2 : ((Finset.equivFin (blockPartialMatching blockS blockT c).freeCols).symm e.2).1 =
        ((Finset.equivFin (blockPartialMatching blockS blockT c).freeCols).symm e'.2).1 :=
      congrArg Prod.snd h
    have e1 : ((Finset.equivFin (blockPartialMatching blockS blockT c).freeRows).symm e.1) =
        ((Finset.equivFin (blockPartialMatching blockS blockT c).freeRows).symm e'.1) :=
      Subtype.ext h1
    have e2 : ((Finset.equivFin (blockPartialMatching blockS blockT c).freeCols).symm e.2) =
        ((Finset.equivFin (blockPartialMatching blockS blockT c).freeCols).symm e'.2) :=
      Subtype.ext h2
    exact Prod.ext ((Finset.equivFin _).symm.injective e1) ((Finset.equivFin _).symm.injective e2)

theorem residualBlockMatching_rows_subset :
    (residualBlockMatching blockS blockT c).rows ⊆
      (blockPartialMatching blockS blockT c).freeRows := by
  intro i hi
  unfold PartialMatching.rows at hi
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  rw [residualBlockMatching_edges] at he
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp he
  rw [← congrArg Prod.fst hx]
  exact ((Finset.equivFin (blockPartialMatching blockS blockT c).freeRows).symm x.1).2

theorem residualBlockMatching_cols_subset :
    (residualBlockMatching blockS blockT c).cols ⊆
      (blockPartialMatching blockS blockT c).freeCols := by
  intro j hj
  unfold PartialMatching.cols at hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  rw [residualBlockMatching_edges] at he
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp he
  rw [← congrArg Prod.snd hx]
  exact ((Finset.equivFin (blockPartialMatching blockS blockT c).freeCols).symm x.2).2

theorem disjoint_block_rows :
    Disjoint (blockPartialMatching blockS blockT c).rows
      (residualBlockMatching blockS blockT c).rows := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have hfree := residualBlockMatching_rows_subset blockS blockT c hx'
  simp only [PartialMatching.freeRows, Finset.mem_sdiff] at hfree
  exact hfree.2 hx

theorem disjoint_block_cols :
    Disjoint (blockPartialMatching blockS blockT c).cols
      (residualBlockMatching blockS blockT c).cols := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have hfree := residualBlockMatching_cols_subset blockS blockT c hx'
  simp only [PartialMatching.freeCols, Finset.mem_sdiff] at hfree
  exact hfree.2 hx

/-- The full constructed maximum-cardinality matching. -/
noncomputable def assembledMatching : PartialMatching a b :=
  (blockPartialMatching blockS blockT c).union (residualBlockMatching blockS blockT c)
    (disjoint_block_rows blockS blockT c) (disjoint_block_cols blockS blockT c)

theorem card_assembledMatching :
    (assembledMatching blockS blockT c).card = min a b := by
  have hJ : (blockPartialMatching blockS blockT c).card =
      ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t) :=
    card_blockPartialMatching blockS blockT c
  have hJr : (blockPartialMatching blockS blockT c).card ≤ min a b := by
    rw [hJ]
    apply le_min
    · calc ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t)
          ≤ ∑ t, blockSizeS blockS t := Finset.sum_le_sum fun t _ ↦ min_le_left _ _
        _ = a := sum_card_blockFinset blockS
    · calc ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t)
          ≤ ∑ t, blockSizeT blockT t := Finset.sum_le_sum fun t _ ↦ min_le_right _ _
        _ = b := sum_card_blockFinset blockT
  have hres : (residualBlockMatching blockS blockT c).card =
      min (a - (blockPartialMatching blockS blockT c).card)
        (b - (blockPartialMatching blockS blockT c).card) := by
    rw [card_residualBlockMatching, PartialMatching.card_freeRows, PartialMatching.card_freeCols,
      hJ]
  rw [assembledMatching, PartialMatching.card_union, hres]
  omega

theorem cost_residualBlockMatching_le {B : ℝ} (hB : ∀ i j, c i j ≤ B) :
    (residualBlockMatching blockS blockT c).cost c ≤
      B * ((residualBlockMatching blockS blockT c).card : ℝ) := by
  have h := PartialMatching.cost_le_card_mul c (residualBlockMatching blockS blockT c) hB
  rw [mul_comm]
  exact h

/-- The deterministic block decomposition bound for maximum-cardinality values. -/
theorem maxCardValue_le_sum_block_maxCardValue {B : ℝ}
    (hB : ∀ i j, c i j ≤ B) :
    PartialMatching.maxCardValue c ≤
      (∑ t, PartialMatching.maxCardValue (blockCost blockS blockT c t)) +
        B * ((min (a - ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t))
              (b - ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t)) : ℕ) : ℝ) := by
  have hcard : (assembledMatching blockS blockT c).card = min a b :=
    card_assembledMatching blockS blockT c
  have hmax := PartialMatching.maxCardValue_le_of_card c hcard
  have hcost : (assembledMatching blockS blockT c).cost c ≤
      (∑ t, PartialMatching.maxCardValue (blockCost blockS blockT c t)) +
        B * ((min (a - ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t))
              (b - ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t)) : ℕ) : ℝ) := by
    rw [assembledMatching, PartialMatching.cost_union,
      cost_blockPartialMatching blockS blockT c]
    have hres := cost_residualBlockMatching_le blockS blockT c hB
    rw [card_residualBlockMatching, PartialMatching.card_freeRows,
      PartialMatching.card_freeCols, card_blockPartialMatching] at hres
    linarith
  linarith

end Residual

section Discrepancy

variable {a b : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
  (blockS : Fin a → β) (blockT : Fin b → β) (c : Fin a → Fin b → ℝ)

/-- The real absolute difference of two natural numbers via their minimum. -/
theorem abs_cast_sub_eq_cast_add_sub_two_mul_min (m n : ℕ) :
    |(m : ℝ) - (n : ℝ)| =
      (m : ℝ) + (n : ℝ) - 2 * ((min m n : ℕ) : ℝ) := by
  rcases le_total m n with h | h
  · rw [Nat.cast_min, min_eq_left (by exact_mod_cast h), abs_of_nonpos (by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      linarith)]
    ring
  · rw [Nat.cast_min, min_eq_right (by exact_mod_cast h), abs_of_nonneg (by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      linarith)]
    ring

/-- The total histogram discrepancy in terms of the two totals and the common part. -/
theorem sum_abs_cast_sub_eq {ι : Type*} [Fintype ι] (s u : ι → ℕ) :
    (∑ i, |(s i : ℝ) - (u i : ℝ)|) =
      ((∑ i, s i : ℕ) : ℝ) + ((∑ i, u i : ℕ) : ℝ) -
        2 * ((∑ i, min (s i) (u i) : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl (fun i _ ↦ abs_cast_sub_eq_cast_add_sub_two_mul_min (s i) (u i))]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum]

/-- The residual count is at most half the total block count discrepancy. -/
theorem two_mul_min_residual_le_sum_abs {ι : Type*} [Fintype ι] (s u : ι → ℕ) :
    (2 : ℝ) * ((min ((∑ i, s i) - ∑ i, min (s i) (u i))
        ((∑ i, u i) - ∑ i, min (s i) (u i)) : ℕ) : ℝ) ≤
      ∑ i, |(s i : ℝ) - (u i : ℝ)| := by
  rw [sum_abs_cast_sub_eq]
  set A : ℕ := ∑ i, s i
  set B : ℕ := ∑ i, u i
  set J : ℕ := ∑ i, min (s i) (u i)
  have hJ : J ≤ A := Finset.sum_le_sum fun i _ ↦ min_le_left _ _
  have hJ' : J ≤ B := Finset.sum_le_sum fun i _ ↦ min_le_right _ _
  have hmincast : ((min (A - J) (B - J) : ℕ) : ℝ) = min ((A : ℝ) - J) ((B : ℝ) - J) := by
    have h1 : ((A - J : ℕ) : ℝ) = (A : ℝ) - J := by
      rw [Nat.cast_sub hJ]
    have h2 : ((B - J : ℕ) : ℝ) = (B : ℝ) - J := by
      rw [Nat.cast_sub hJ']
    rw [Nat.cast_min, h1, h2]
  rw [hmincast]
  rcases le_total A B with h | h
  · have hsub : (A : ℝ) - J ≤ (B : ℝ) - J := by
      have : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast h
      linarith
    rw [min_eq_left hsub]
    push_cast
    linarith
  · have hsub : (B : ℝ) - J ≤ (A : ℝ) - J := by
      have : (B : ℝ) ≤ (A : ℝ) := by exact_mod_cast h
      linarith
    rw [min_eq_right hsub]
    push_cast
    linarith

/-- The expected-value form: the repair cost is bounded by the uniform edge bound
times half the total histogram discrepancy. -/
theorem maxCardValue_le_sum_block_add_half_discrepancy {B : ℝ}
    (hB : ∀ i j, c i j ≤ B) (hB0 : 0 ≤ B) :
    PartialMatching.maxCardValue c ≤
      (∑ t : β, PartialMatching.maxCardValue (blockCost blockS blockT c t)) +
        B * ((1 / 2 : ℝ) * ∑ t : β,
          |(blockSizeS blockS t : ℝ) - (blockSizeT blockT t : ℝ)|) := by
  have hmain := maxCardValue_le_sum_block_maxCardValue blockS blockT c hB
  have h2 := two_mul_min_residual_le_sum_abs (ι := β) (fun t ↦ blockSizeS blockS t)
    (fun t ↦ blockSizeT blockT t)
  have hsumS : (∑ t, blockSizeS blockS t) = a := sum_card_blockFinset blockS
  have hsumT : (∑ t, blockSizeT blockT t) = b := sum_card_blockFinset blockT
  rw [hsumS, hsumT] at h2
  have hBle : B * ((min (a - ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t))
        (b - ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t)) : ℕ) : ℝ) ≤
      B * ((1 / 2 : ℝ) * ∑ t, |(blockSizeS blockS t : ℝ) - (blockSizeT blockT t : ℝ)|) := by
    apply mul_le_mul_of_nonneg_left _ hB0
    linarith
  linarith

end Discrepancy

end OTSelector
