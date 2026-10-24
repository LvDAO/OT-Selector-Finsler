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
import OTSelector.Finite.HierarchicalAssignment
import OTSelector.Finite.MatchingUnion
import OTSelector.Finite.PartialMatching
import OTSelector.Finite.PartitionCount

/-!
# Finite.BlockRepair

**Conditions:** Finite nested cell hierarchy, within-cell full matching at the leaf and explicit coarse-level repair bounds; signed costs are allowed.

**Objects:** A repaired global maximum-cardinality matching and the telescoping cell-discrepancy cost.

**Proof detail:** Enumerate free endpoints in each coarse cell and append disjoint repair edges; min(x,y)=(x+y−|x−y|)/2 counts the added edges exactly, then induction over scales telescopes the discrepancies.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Hierarchical block repair for maximum-cardinality partial matchings

A partial matching that is maximum-cardinality inside every finest cell of a
nested partition hierarchy is extended to a globally maximum-cardinality
matching by repairing the unmatched rows and columns at successively coarser
scales.  Within each coarse cell the free rows and free columns are paired as
soon as both are available; every new edge joins two points of the same coarse
cell, so its cost is bounded by the coarse-level cost bound.

The two-level step (`exists_maxCardMatching_le_add_repair`) proves that the
number of repair edges at a coarsening equals one half of the *decrease* of the
total absolute cell-count discrepancy when passing from the finer partition to
the coarser one.  Iterating the step from the finest level to the root gives
the multilevel bound: the repair cost at level `k` is `B k` times one half of
the increase of the total absolute discrepancy from level `k - 1` to level
`k`.

Levels are indexed by natural numbers: level `0` is the root/coarsest
partition and level `K` is the finest leaf partition.  The multiscale repair
therefore involves the bounds `B 1, ..., B K`; the root term is zero.

The final theorem does not assume nonnegativity of the edge costs: only the
bound `B k` for repair edges and the exact leaf cost of the initial matching
are used.
-/

open scoped BigOperators

noncomputable section

namespace OTSelector

open OTSelector.Reconstruction

namespace PartialMatching

variable {a b : ℕ}

/-- Filtering the used rows by a predicate counts the edges whose first endpoint
satisfies the predicate. -/
theorem card_rows_filter (σ : PartialMatching a b) (P : Fin a → Prop) [DecidablePred P] :
    (σ.rows.filter P).card = (σ.edges.filter (fun e => P e.1)).card := by
  classical
  have hset : σ.rows.filter P = (σ.edges.filter (fun e => P e.1)).image Prod.fst := by
    ext i
    constructor
    · intro hi
      obtain ⟨hrow, hP⟩ := Finset.mem_filter.mp hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hrow
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hP⟩, rfl⟩
    · intro hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩,
          (Finset.mem_filter.mp he).2⟩
  rw [hset, Finset.card_image_of_injOn]
  intro e he e' he' h
  exact σ.row_inj e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 h

/-- Filtering the used columns by a predicate counts the edges whose second
endpoint satisfies the predicate. -/
theorem card_cols_filter (σ : PartialMatching a b) (P : Fin b → Prop) [DecidablePred P] :
    (σ.cols.filter P).card = (σ.edges.filter (fun e => P e.2)).card := by
  classical
  have hset : σ.cols.filter P = (σ.edges.filter (fun e => P e.2)).image Prod.snd := by
    ext j
    constructor
    · intro hj
      obtain ⟨hcol, hP⟩ := Finset.mem_filter.mp hj
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hcol
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hP⟩, rfl⟩
    · intro hj
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩,
          (Finset.mem_filter.mp he).2⟩
  rw [hset, Finset.card_image_of_injOn]
  intro e he e' he' h
  exact σ.col_inj e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 h

/-- The number of free rows satisfying a predicate is the total number of rows
satisfying it minus the number of used rows satisfying it. -/
theorem card_freeRows_filter (σ : PartialMatching a b) (P : Fin a → Prop) [DecidablePred P] :
    (σ.freeRows.filter P).card = (Finset.univ.filter P).card - (σ.rows.filter P).card := by
  classical
  have hset : σ.freeRows.filter P = (Finset.univ.filter P) \ (σ.rows.filter P) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, PartialMatching.freeRows, Finset.mem_univ,
      true_and]
    tauto
  rw [hset, Finset.card_sdiff_of_subset]
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩

/-- The number of free columns satisfying a predicate is the total number of
columns satisfying it minus the number of used columns satisfying it. -/
theorem card_freeCols_filter (σ : PartialMatching a b) (P : Fin b → Prop) [DecidablePred P] :
    (σ.freeCols.filter P).card = (Finset.univ.filter P).card - (σ.cols.filter P).card := by
  classical
  have hset : σ.freeCols.filter P = (Finset.univ.filter P) \ (σ.cols.filter P) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, PartialMatching.freeCols, Finset.mem_univ,
      true_and]
    tauto
  rw [hset, Finset.card_sdiff_of_subset]
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩

end PartialMatching

/-! ## Elementary real identities -/

/-- The minimum of two reals in terms of their sum and absolute difference. -/
theorem min_eq_half_sub_abs_real (x y : ℝ) : min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The absolute difference of two reals in terms of their sum and minimum. -/
theorem abs_sub_eq_add_sub_two_min_real (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The cardinality of a matching that is maximum in every cell of a partition
is the sum over the cells of the minimum of the row and column cell counts. -/
theorem card_eq_sum_min_of_cell_max
    {X C : Type*} [Fintype C] [DecidableEq C] {a b : ℕ}
    (leaf : X → C) (x : Fin a → X) (y : Fin b → X) (σ : PartialMatching a b)
    (hmax : ∀ c : C, (σ.edges.filter (fun e => leaf (x e.1) = c)).card =
      min ((Finset.univ.filter (fun i => leaf (x i) = c)).card)
          ((Finset.univ.filter (fun j => leaf (y j) = c)).card)) :
    σ.card = ∑ c : C, min ((Finset.univ.filter (fun i => leaf (x i) = c)).card)
                            ((Finset.univ.filter (fun j => leaf (y j) = c)).card) := by
  classical
  have hsum : (∑ c : C, (σ.edges.filter (fun e => leaf (x e.1) = c)).card) = σ.card := by
    calc (∑ c : C, (σ.edges.filter (fun e => leaf (x e.1) = c)).card)
        = ∑ c : C, ∑ e ∈ σ.edges with leaf (x e.1) = c, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro c _
          exact Finset.card_eq_sum_ones _
      _ = ∑ e ∈ σ.edges, (1 : ℕ) :=
          Finset.sum_fiberwise σ.edges (fun e => leaf (x e.1)) (fun _ => (1 : ℕ))
      _ = σ.card := (Finset.card_eq_sum_ones σ.edges).symm
  calc σ.card = (∑ c : C, (σ.edges.filter (fun e => leaf (x e.1) = c)).card) := hsum.symm
    _ = ∑ c : C, min ((Finset.univ.filter (fun i => leaf (x i) = c)).card)
                          ((Finset.univ.filter (fun j => leaf (y j) = c)).card) :=
        Finset.sum_congr rfl (fun c _ => hmax c)

/-! ## Two-level repair -/

/-- **Two-level block repair.**  If `σ0` is supported inside the cells of the
finite partition `leaf` and is maximum-cardinality in every `leaf` cell, then it
can be extended to a matching that is maximum-cardinality in every cell of the
coarser partition `coarse`.  The number of repair edges is one half of the
decrease of the total absolute cell-count discrepancy from `leaf` to `coarse`,
and each repair edge costs at most `B`. -/
theorem exists_maxCardMatching_le_add_repair
    {X C D : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (leaf : X → C) (coarse : X → D)
    (hcompat : ∀ u v : X, leaf u = leaf v → coarse u = coarse v)
    {a b : ℕ} (x : Fin a → X) (y : Fin b → X)
    (cost : Fin a → Fin b → ℝ) (σ0 : PartialMatching a b)
    (hleaf : ∀ e ∈ σ0.edges, leaf (x e.1) = leaf (y e.2))
    (hmax : ∀ c : C, (σ0.edges.filter (fun e => leaf (x e.1) = c)).card =
      min ((Finset.univ.filter (fun i => leaf (x i) = c)).card)
          ((Finset.univ.filter (fun j => leaf (y j) = c)).card))
    (B : ℝ) (hB : ∀ i j, coarse (x i) = coarse (y j) → cost i j ≤ B) :
    ∃ σ : PartialMatching a b,
      (∀ e ∈ σ.edges, coarse (x e.1) = coarse (y e.2)) ∧
      (∀ d : D, (σ.edges.filter (fun e => coarse (x e.1) = d)).card =
        min ((Finset.univ.filter (fun i => coarse (x i) = d)).card)
            ((Finset.univ.filter (fun j => coarse (y j) = d)).card)) ∧
      σ.card = ∑ d : D, min ((Finset.univ.filter (fun i => coarse (x i) = d)).card)
                             ((Finset.univ.filter (fun j => coarse (y j) = d)).card) ∧
      σ.cost cost ≤ σ0.cost cost + B * ((1 / 2 : ℝ) *
        ((∑ c : C, |partitionCount (leaf ∘ x) c - partitionCount (leaf ∘ y) c|) -
         (∑ d : D, |partitionCount (coarse ∘ x) d - partitionCount (coarse ∘ y) d|))) := by
  classical
  -- Free rows and columns in each coarse cell.
  let R : D → Finset (Fin a) := fun d => σ0.freeRows.filter (fun i => coarse (x i) = d)
  let Cc : D → Finset (Fin b) := fun d => σ0.freeCols.filter (fun j => coarse (y j) = d)
  let m : D → ℕ := fun d => min (R d).card (Cc d).card
  -- Enumerations of the free rows and columns inside each coarse cell.
  let eR : (d : D) → {i : Fin a // i ∈ R d} ≃ Fin (R d).card :=
    fun d => (Fintype.equivFin {i : Fin a // i ∈ R d}).trans (finCongr (Fintype.card_coe (R d)))
  let eC : (d : D) → {j : Fin b // j ∈ Cc d} ≃ Fin (Cc d).card :=
    fun d => (Fintype.equivFin {j : Fin b // j ∈ Cc d}).trans (finCongr (Fintype.card_coe (Cc d)))
  let rowOf : (d : D) → Fin (m d) → Fin a :=
    fun d t => ((eR d).symm
      ⟨t.val, lt_of_lt_of_le t.isLt (min_le_left (R d).card (Cc d).card)⟩).val
  let colOf : (d : D) → Fin (m d) → Fin b :=
    fun d t => ((eC d).symm
      ⟨t.val, lt_of_lt_of_le t.isLt (min_le_right (R d).card (Cc d).card)⟩).val
  have rowOf_mem (d : D) (t : Fin (m d)) : rowOf d t ∈ R d := by
    dsimp only [rowOf]
    exact ((eR d).symm
      ⟨t.val, lt_of_lt_of_le t.isLt (min_le_left (R d).card (Cc d).card)⟩).2
  have colOf_mem (d : D) (t : Fin (m d)) : colOf d t ∈ Cc d := by
    dsimp only [colOf]
    exact ((eC d).symm
      ⟨t.val, lt_of_lt_of_le t.isLt (min_le_right (R d).card (Cc d).card)⟩).2
  have rowOf_coarse (d : D) (t : Fin (m d)) : coarse (x (rowOf d t)) = d :=
    (Finset.mem_filter.mp (rowOf_mem d t)).2
  have colOf_coarse (d : D) (t : Fin (m d)) : coarse (y (colOf d t)) = d :=
    (Finset.mem_filter.mp (colOf_mem d t)).2
  have rowOf_inj (d : D) : Function.Injective (rowOf d) := by
    intro t t' h
    have hs : (eR d).symm
          ⟨t.val, lt_of_lt_of_le t.isLt (min_le_left (R d).card (Cc d).card)⟩ =
        (eR d).symm
          ⟨t'.val, lt_of_lt_of_le t'.isLt (min_le_left (R d).card (Cc d).card)⟩ :=
      Subtype.ext h
    have h2 := congrArg (eR d) hs
    simp only [Equiv.apply_symm_apply] at h2
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  have colOf_inj (d : D) : Function.Injective (colOf d) := by
    intro t t' h
    have hs : (eC d).symm
          ⟨t.val, lt_of_lt_of_le t.isLt (min_le_right (R d).card (Cc d).card)⟩ =
        (eC d).symm
          ⟨t'.val, lt_of_lt_of_le t'.isLt (min_le_right (R d).card (Cc d).card)⟩ :=
      Subtype.ext h
    have h2 := congrArg (eC d) hs
    simp only [Equiv.apply_symm_apply] at h2
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  -- The repair matching.
  let edgeOf : Sigma (fun d : D => Fin (m d)) → Fin a × Fin b :=
    fun p => (rowOf p.1 p.2, colOf p.1 p.2)
  have edgeOf_row_eq {p q : Sigma (fun d : D => Fin (m d))}
      (h : (edgeOf p).1 = (edgeOf q).1) : p = q := by
    have hrow : rowOf p.1 p.2 = rowOf q.1 q.2 := h
    have hd : p.1 = q.1 := by
      calc p.1 = coarse (x (rowOf p.1 p.2)) := (rowOf_coarse p.1 p.2).symm
        _ = coarse (x (rowOf q.1 q.2)) := by rw [hrow]
        _ = q.1 := rowOf_coarse q.1 q.2
    obtain ⟨d, t⟩ := p
    obtain ⟨d', t'⟩ := q
    simp only at hd hrow
    subst hd
    have ht : t = t' := rowOf_inj d hrow
    subst ht
    rfl
  have edgeOf_col_eq {p q : Sigma (fun d : D => Fin (m d))}
      (h : (edgeOf p).2 = (edgeOf q).2) : p = q := by
    have hcol : colOf p.1 p.2 = colOf q.1 q.2 := h
    have hd : p.1 = q.1 := by
      calc p.1 = coarse (y (colOf p.1 p.2)) := (colOf_coarse p.1 p.2).symm
        _ = coarse (y (colOf q.1 q.2)) := by rw [hcol]
        _ = q.1 := colOf_coarse q.1 q.2
    obtain ⟨d, t⟩ := p
    obtain ⟨d', t'⟩ := q
    simp only at hd hcol
    subst hd
    have ht : t = t' := colOf_inj d hcol
    subst ht
    rfl
  have edgeOf_inj : Function.Injective edgeOf := by
    intro p q h
    exact edgeOf_row_eq (by rw [h])
  let τ : PartialMatching a b :=
    { edges := Finset.univ.image edgeOf
      row_inj := by
        intro e he e' he' hrow
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he'
        exact congrArg edgeOf (edgeOf_row_eq hrow)
      col_inj := by
        intro e he e' he' hcol
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he'
        exact congrArg edgeOf (edgeOf_col_eq hcol) }
  have τrows_sub : τ.rows ⊆ σ0.freeRows := by
    intro i hi
    simp only [PartialMatching.rows, Finset.mem_image] at hi
    obtain ⟨e, he, rfl⟩ := hi
    simp only [τ, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨p, rfl⟩ := he
    exact Finset.filter_subset _ _ (rowOf_mem p.1 p.2)
  have τcols_sub : τ.cols ⊆ σ0.freeCols := by
    intro j hj
    simp only [PartialMatching.cols, Finset.mem_image] at hj
    obtain ⟨e, he, rfl⟩ := hj
    simp only [τ, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨p, rfl⟩ := he
    exact Finset.filter_subset _ _ (colOf_mem p.1 p.2)
  have hrowdisj : Disjoint σ0.rows τ.rows := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.mem_sdiff.mp (τrows_sub hj)).2 hi
  have hcoldisj : Disjoint σ0.cols τ.cols := by
    rw [Finset.disjoint_left]
    intro j hj hk
    exact (Finset.mem_sdiff.mp (τcols_sub hk)).2 hj
  let σ : PartialMatching a b := σ0.union τ hrowdisj hcoldisj
  -- Cardinality of the repair matching.
  have τcard_nat : τ.card = ∑ d : D, m d := by
    simp only [τ, PartialMatching.card]
    rw [Finset.card_image_of_injective _ edgeOf_inj]
    simp [Fintype.card_sigma]
  have hdisj_edges : Disjoint σ0.edges τ.edges := by
    rw [Finset.disjoint_left]
    intro e heS heT
    exact (Finset.disjoint_left.mp hrowdisj)
      (Finset.mem_image.mpr ⟨e, heS, rfl⟩) (Finset.mem_image.mpr ⟨e, heT, rfl⟩)
  -- Counts in each coarse cell.
  let Ar : D → ℕ := fun d => (Finset.univ.filter (fun i : Fin a => coarse (x i) = d)).card
  let Br : D → ℕ := fun d => (Finset.univ.filter (fun j : Fin b => coarse (y j) = d)).card
  let used : D → ℕ := fun d => (σ0.edges.filter (fun e => coarse (x e.1) = d)).card
  let acl : C → ℕ := fun c => (Finset.univ.filter (fun i : Fin a => leaf (x i) = c)).card
  let bcl : C → ℕ := fun c => (Finset.univ.filter (fun j : Fin b => leaf (y j) = c)).card
  have row_filter_card (d : D) :
      (σ0.rows.filter (fun i => coarse (x i) = d)).card = used d := by
    rw [PartialMatching.card_rows_filter]
  have col_filter_card (d : D) :
      (σ0.cols.filter (fun j => coarse (y j) = d)).card = used d := by
    rw [PartialMatching.card_cols_filter]
    have h : (σ0.edges.filter (fun e => coarse (y e.2) = d)) =
        (σ0.edges.filter (fun e => coarse (x e.1) = d)) := by
      apply Finset.filter_congr
      intro e he
      have hc := hcompat (x e.1) (y e.2) (hleaf e he)
      constructor
      · intro hh
        rwa [← hc] at hh
      · intro hh
        rwa [hc] at hh
    rw [h]
  have used_le_Ar (d : D) : used d ≤ Ar d := by
    rw [← row_filter_card d]
    exact Finset.card_le_card (fun i hi => Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  have used_le_Br (d : D) : used d ≤ Br d := by
    rw [← col_filter_card d]
    exact Finset.card_le_card (fun j hj => Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩)
  have freeR_card (d : D) : (R d).card = Ar d - used d := by
    dsimp only [R, Ar]
    rw [PartialMatching.card_freeRows_filter, row_filter_card d]
  have freeC_card (d : D) : (Cc d).card = Br d - used d := by
    dsimp only [Cc, Br]
    rw [PartialMatching.card_freeCols_filter, col_filter_card d]
  -- The real minimum formula in each coarse cell.
  have m_real (d : D) : (m d : ℝ) =
      (((R d).card : ℝ) + ((Cc d).card : ℝ) - |(Ar d : ℝ) - (Br d : ℝ)|) / 2 := by
    have hm : (m d : ℝ) = min ((R d).card : ℝ) ((Cc d).card : ℝ) := by
      dsimp only [m]
      exact Nat.cast_min _ _
    rw [hm]
    have hR : ((R d).card : ℝ) = (Ar d : ℝ) - (used d : ℝ) := by
      rw [freeR_card d, Nat.cast_sub (used_le_Ar d)]
    have hC : ((Cc d).card : ℝ) = (Br d : ℝ) - (used d : ℝ) := by
      rw [freeC_card d, Nat.cast_sub (used_le_Br d)]
    rw [hR, hC, min_eq_half_sub_abs_real]
    have hdiff : ((Ar d : ℝ) - (used d : ℝ)) - ((Br d : ℝ) - (used d : ℝ)) =
        (Ar d : ℝ) - (Br d : ℝ) := by ring
    rw [hdiff]
  -- Sums of the free counts.
  have sum_freeR : (∑ d : D, ((R d).card : ℝ)) = (σ0.freeRows.card : ℝ) := by
    calc (∑ d : D, ((R d).card : ℝ))
        = ∑ d : D, ∑ i ∈ σ0.freeRows with coarse (x i) = d, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro d _
          dsimp only [R]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ i ∈ σ0.freeRows, (1 : ℝ) := Finset.sum_fiberwise _ _ _
      _ = (σ0.freeRows.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have sum_freeC : (∑ d : D, ((Cc d).card : ℝ)) = (σ0.freeCols.card : ℝ) := by
    calc (∑ d : D, ((Cc d).card : ℝ))
        = ∑ d : D, ∑ j ∈ σ0.freeCols with coarse (y j) = d, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro d _
          dsimp only [Cc]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ j ∈ σ0.freeCols, (1 : ℝ) := Finset.sum_fiberwise _ _ _
      _ = (σ0.freeCols.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have sum_freeR' : (∑ d : D, ((R d).card : ℝ)) = (a : ℝ) - (σ0.card : ℝ) := by
    rw [sum_freeR, PartialMatching.card_freeRows,
      Nat.cast_sub (le_trans σ0.card_le (min_le_left a b))]
  have sum_freeC' : (∑ d : D, ((Cc d).card : ℝ)) = (b : ℝ) - (σ0.card : ℝ) := by
    rw [sum_freeC, PartialMatching.card_freeCols,
      Nat.cast_sub (le_trans σ0.card_le (min_le_right a b))]
  -- Sums of the leaf counts.
  have sum_acl : (∑ c : C, (acl c : ℝ)) = (a : ℝ) := by
    calc (∑ c : C, (acl c : ℝ))
        = ∑ c : C, ∑ i ∈ (Finset.univ : Finset (Fin a)) with leaf (x i) = c, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro c _
          dsimp only [acl]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin a)), (1 : ℝ) := Finset.sum_fiberwise _ _ _
      _ = (a : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          simp
  have sum_bcl : (∑ c : C, (bcl c : ℝ)) = (b : ℝ) := by
    calc (∑ c : C, (bcl c : ℝ))
        = ∑ c : C, ∑ j ∈ (Finset.univ : Finset (Fin b)) with leaf (y j) = c, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro c _
          dsimp only [bcl]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ j ∈ (Finset.univ : Finset (Fin b)), (1 : ℝ) := Finset.sum_fiberwise _ _ _
      _ = (b : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          simp
  -- The initial matching captures the minimum in every leaf cell.
  have sum_min_acl_bcl : (σ0.card : ℝ) =
      ∑ c : C, ((min (acl c) (bcl c) : ℕ) : ℝ) := by
    have hsum : (∑ c : C, (σ0.edges.filter (fun e => leaf (x e.1) = c)).card) = σ0.card := by
      calc (∑ c : C, (σ0.edges.filter (fun e => leaf (x e.1) = c)).card)
          = ∑ c : C, ∑ e ∈ σ0.edges with leaf (x e.1) = c, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro c _
            exact Finset.card_eq_sum_ones _
        _ = ∑ e ∈ σ0.edges, (1 : ℕ) :=
            Finset.sum_fiberwise σ0.edges (fun e => leaf (x e.1)) (fun _ => (1 : ℕ))
        _ = σ0.card := (Finset.card_eq_sum_ones σ0.edges).symm
    calc (σ0.card : ℝ)
        = ((∑ c : C, (σ0.edges.filter (fun e => leaf (x e.1) = c)).card : ℕ) : ℝ) := by
          rw [hsum]
      _ = ∑ c : C, ((σ0.edges.filter (fun e => leaf (x e.1) = c)).card : ℝ) := by
          push_cast
          ring
      _ = ∑ c : C, ((min (acl c) (bcl c) : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [hmax c]
  -- The discrepancy sums in terms of the counts.
  have hDleaf : (∑ c : C, |partitionCount (leaf ∘ x) c - partitionCount (leaf ∘ y) c|) =
      ∑ c : C, |(acl c : ℝ) - (bcl c : ℝ)| := by
    apply Finset.sum_congr rfl
    intro c _
    rw [partitionCount_eq_card_filter (leaf ∘ x) c,
      partitionCount_eq_card_filter (leaf ∘ y) c]
    rfl
  have hDcoarse : (∑ d : D, |partitionCount (coarse ∘ x) d - partitionCount (coarse ∘ y) d|) =
      ∑ d : D, |(Ar d : ℝ) - (Br d : ℝ)| := by
    apply Finset.sum_congr rfl
    intro d _
    rw [partitionCount_eq_card_filter (coarse ∘ x) d,
      partitionCount_eq_card_filter (coarse ∘ y) d]
    rfl
  -- The cardinality identity for the repair matching.
  have τcard_sum : (τ.card : ℝ) = ∑ d : D, (m d : ℝ) := by
    rw [τcard_nat]
    push_cast
    ring
  have τcard_real : (τ.card : ℝ) = (1 / 2 : ℝ) *
      (((a : ℝ) - (σ0.card : ℝ)) + ((b : ℝ) - (σ0.card : ℝ)) -
        ∑ d : D, |(Ar d : ℝ) - (Br d : ℝ)|) := by
    rw [τcard_sum]
    have h : (∑ d : D, (m d : ℝ)) =
        ∑ d : D, (((R d).card : ℝ) + ((Cc d).card : ℝ) -
          |(Ar d : ℝ) - (Br d : ℝ)|) / 2 := by
      apply Finset.sum_congr rfl
      intro d _
      exact m_real d
    rw [h]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      sum_freeR', sum_freeC']
    ring
  have hdiff_counts : ((a : ℝ) - (σ0.card : ℝ)) + ((b : ℝ) - (σ0.card : ℝ)) -
        ∑ d : D, |(Ar d : ℝ) - (Br d : ℝ)|
      = (∑ c : C, |(acl c : ℝ) - (bcl c : ℝ)|) -
        ∑ d : D, |(Ar d : ℝ) - (Br d : ℝ)| := by
    congr 1
    rw [← sum_acl, ← sum_bcl, sum_min_acl_bcl]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [abs_sub_eq_add_sub_two_min_real, Nat.cast_min]
    ring
  have τcard_eq : (τ.card : ℝ) = (1 / 2 : ℝ) *
      ((∑ c : C, |partitionCount (leaf ∘ x) c - partitionCount (leaf ∘ y) c|) -
       (∑ d : D, |partitionCount (coarse ∘ x) d - partitionCount (coarse ∘ y) d|)) := by
    rw [τcard_real, hdiff_counts, hDleaf, ← hDcoarse]
  -- Every repair edge costs at most `B`.
  have τcost_le : τ.cost cost ≤ (τ.card : ℝ) * B := by
    dsimp only [PartialMatching.cost]
    calc (∑ e ∈ τ.edges, cost e.1 e.2) ≤ ∑ _e ∈ τ.edges, B := by
          apply Finset.sum_le_sum
          intro e he
          simp only [τ, Finset.mem_image, Finset.mem_univ, true_and] at he
          obtain ⟨p, rfl⟩ := he
          exact hB (rowOf p.1 p.2) (colOf p.1 p.2) (by rw [rowOf_coarse, colOf_coarse])
      _ = (τ.card : ℝ) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rfl
  -- The repair matching saturates each coarse cell.
  have τfilter (d : D) :
      (τ.edges.filter (fun e => coarse (x e.1) = d)).card = m d := by
    have hset : τ.edges.filter (fun e => coarse (x e.1) = d) =
        Finset.univ.image (fun t : Fin (m d) => edgeOf ⟨d, t⟩) := by
      ext e
      constructor
      · intro he
        rw [Finset.mem_filter] at he
        obtain ⟨he, hc⟩ := he
        simp only [τ, Finset.mem_image, Finset.mem_univ, true_and] at he
        obtain ⟨q, hq⟩ := he
        rw [← hq] at hc ⊢
        have hqd : q.1 = d := by
          rw [← hc]
          exact (rowOf_coarse q.1 q.2).symm
        obtain ⟨d', t⟩ := q
        simp only at hqd ⊢
        subst hqd
        exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
      · intro he
        obtain ⟨t, _, ht⟩ := Finset.mem_image.mp he
        rw [Finset.mem_filter]
        constructor
        · rw [← ht]
          exact Finset.mem_image.mpr
            ⟨(⟨d, t⟩ : Sigma (fun d : D => Fin (m d))), Finset.mem_univ _, rfl⟩
        · rw [← ht]
          exact rowOf_coarse d t
    rw [hset, Finset.card_image_of_injective]
    · simp
    · intro t t' h
      exact rowOf_inj d (congrArg Prod.fst h)
  have σfilter (d : D) :
      (σ.edges.filter (fun e => coarse (x e.1) = d)).card = min (Ar d) (Br d) := by
    have huedges : Disjoint (σ0.edges.filter (fun e => coarse (x e.1) = d))
        (τ.edges.filter (fun e => coarse (x e.1) = d)) :=
      hdisj_edges.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hset : σ.edges.filter (fun e => coarse (x e.1) = d) =
        (σ0.edges.filter (fun e => coarse (x e.1) = d)) ∪
          (τ.edges.filter (fun e => coarse (x e.1) = d)) := by
      dsimp only [σ]
      rw [PartialMatching.union_edges, Finset.filter_union]
    rw [hset, Finset.card_union_of_disjoint huedges]
    have h1 : (σ0.edges.filter (fun e => coarse (x e.1) = d)).card = used d := rfl
    rw [h1, τfilter d]
    have hAr : Ar d = used d + (R d).card := by
      have h := freeR_card d
      have hle := used_le_Ar d
      omega
    have hBr : Br d = used d + (Cc d).card := by
      have h := freeC_card d
      have hle := used_le_Br d
      omega
    have hm : m d = min (R d).card (Cc d).card := rfl
    rw [hAr, hBr, hm, Nat.add_min_add_left]
  have σcard_sum : σ.card =
      ∑ d : D, min (Ar d) (Br d) := by
    calc σ.card = ∑ e ∈ σ.edges, (1 : ℕ) := Finset.card_eq_sum_ones σ.edges
      _ = ∑ d : D, ∑ e ∈ σ.edges with coarse (x e.1) = d, (1 : ℕ) :=
          (Finset.sum_fiberwise σ.edges (fun e => coarse (x e.1)) (fun _ => (1 : ℕ))).symm
      _ = ∑ d : D, (σ.edges.filter (fun e => coarse (x e.1) = d)).card := by
          apply Finset.sum_congr rfl
          intro d _
          exact (Finset.card_eq_sum_ones _).symm
      _ = ∑ d : D, min (Ar d) (Br d) := Finset.sum_congr rfl (fun d _ => σfilter d)
  -- Every edge of the union stays inside a coarse cell.
  have σinside : ∀ e ∈ σ.edges, coarse (x e.1) = coarse (y e.2) := by
    intro e he
    dsimp only [σ] at he
    rw [PartialMatching.union_edges, Finset.mem_union] at he
    rcases he with he | he
    · exact hcompat (x e.1) (y e.2) (hleaf e he)
    · simp only [τ, Finset.mem_image, Finset.mem_univ, true_and] at he
      obtain ⟨p, rfl⟩ := he
      rw [rowOf_coarse, colOf_coarse]
  refine ⟨σ, σinside, σfilter, σcard_sum, ?_⟩
  have hcostτ : τ.cost cost ≤ B * ((1 / 2 : ℝ) *
      ((∑ c : C, |partitionCount (leaf ∘ x) c - partitionCount (leaf ∘ y) c|) -
       (∑ d : D, |partitionCount (coarse ∘ x) d - partitionCount (coarse ∘ y) d|))) := by
    have h := τcost_le
    rw [τcard_eq] at h
    linarith
  rw [show σ.cost cost = σ0.cost cost + τ.cost cost from
    PartialMatching.cost_union cost σ0 τ hrowdisj hcoldisj]
  linarith

/-- If every point lies in the same root cell, a matching that is maximum in
every root cell has global maximum cardinality. -/
theorem card_eq_min_of_root
    {X C : Type*} [Fintype C] [DecidableEq C] {a b : ℕ}
    (leaf : X → C) (x : Fin a → X) (y : Fin b → X)
    (hroot : ∀ u v : X, leaf u = leaf v)
    (σ : PartialMatching a b)
    (hmax : ∀ c : C, (σ.edges.filter (fun e => leaf (x e.1) = c)).card =
      min ((Finset.univ.filter (fun i => leaf (x i) = c)).card)
          ((Finset.univ.filter (fun j => leaf (y j) = c)).card)) :
    σ.card = min a b := by
  classical
  rw [card_eq_sum_min_of_cell_max leaf x y σ hmax]
  by_cases ha : a = 0
  · subst ha
    have hzero : ∀ c : C,
        min ((Finset.univ.filter (fun i : Fin 0 => leaf (x i) = c)).card)
            ((Finset.univ.filter (fun j : Fin b => leaf (y j) = c)).card) = 0 := by
      intro c
      have hempty : (Finset.univ.filter (fun i : Fin 0 => leaf (x i) = c)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i _
        exact Fin.elim0 i
      rw [hempty]
      simp
    simp only [hzero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_zero]
    simp
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    let i0 : Fin a := ⟨0, hapos⟩
    let c0 : C := leaf (x i0)
    have hrow_all (i : Fin a) : leaf (x i) = c0 := hroot (x i) (x i0)
    have hcol_all (j : Fin b) : leaf (y j) = c0 := hroot (y j) (x i0)
    have hAc0 : (Finset.univ.filter (fun i : Fin a => leaf (x i) = c0)).card = a := by
      rw [Finset.filter_true_of_mem]
      · simp
      · intro i _
        exact hrow_all i
    have hBc0 : (Finset.univ.filter (fun j : Fin b => leaf (y j) = c0)).card = b := by
      rw [Finset.filter_true_of_mem]
      · simp
      · intro j _
        exact hcol_all j
    have hsum : (∑ c : C,
        min ((Finset.univ.filter (fun i : Fin a => leaf (x i) = c)).card)
            ((Finset.univ.filter (fun j : Fin b => leaf (y j) = c)).card)) = min a b := by
      rw [Finset.sum_eq_single c0]
      · rw [hAc0, hBc0]
      · intro c _ hc
        have hemptyR : (Finset.univ.filter (fun i : Fin a => leaf (x i) = c)) = ∅ := by
          apply Finset.filter_false_of_mem
          intro i _ hi
          exact hc (((hrow_all i).symm.trans hi).symm)
        rw [hemptyR]
        simp
      · intro hc
        exact absurd (Finset.mem_univ c0) hc
    exact hsum

/-! ## Multilevel hierarchical repair -/

/-- **Hierarchical block repair.**  Let `cell k` be a nested family of finite
partitions, with `cell 0` the root (all points in one cell) and `cell K` the
finest partition.  Suppose `σ0` is supported inside the finest cells and is
maximum-cardinality in every finest cell, and suppose every pair of points that
lies in a common level-`k` cell has cost at most `B (k+1)`.  Then `σ0` extends
to a globally maximum-cardinality matching whose cost exceeds the cost of `σ0`
by at most the sum over `k = 1, ..., K` of `B k` times one half of the increase
of the total absolute cell-count discrepancy from level `k-1` to level `k`.

No nonnegativity assumption on the edge costs is used. -/
theorem exists_maxCardMatching_le_add_hierarchical_repair
    {X : Type*} {K : ℕ} {C : ℕ → Type*}
    [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (cell : (k : ℕ) → X → C k)
    (hnested : ∀ (k l : ℕ), k ≤ l → ∀ u v : X,
      cell l u = cell l v → cell k u = cell k v)
    {a b : ℕ} (x : Fin a → X) (y : Fin b → X)
    (cost : Fin a → Fin b → ℝ)
    (σ0 : PartialMatching a b)
    (hleaf : ∀ e ∈ σ0.edges, cell K (x e.1) = cell K (y e.2))
    (hmax : ∀ c : C K,
      (σ0.edges.filter (fun e => cell K (x e.1) = c)).card =
        min ((Finset.univ.filter (fun i => cell K (x i) = c)).card)
            ((Finset.univ.filter (fun j => cell K (y j) = c)).card))
    (B : ℕ → ℝ)
    (hB : ∀ (k : ℕ), k < K → ∀ i j,
      cell k (x i) = cell k (y j) → cost i j ≤ B (k + 1))
    (hroot : ∀ u v : X, cell 0 u = cell 0 v) :
    ∃ σ : PartialMatching a b,
      σ.card = min a b ∧
      σ.cost cost ≤ σ0.cost cost +
        ∑ k ∈ Finset.range (K + 1), if 0 < k then
          B k * (1 / 2 : ℝ) *
            ((∑ c : C k,
                |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c|) -
             (∑ p : C (k - 1),
                |partitionCount (cell (k - 1) ∘ x) p -
                 partitionCount (cell (k - 1) ∘ y) p|))
        else 0 := by
  classical
  -- The total absolute discrepancy at each level.
  let disc : ℕ → ℝ := fun k =>
    ∑ c : C k, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c|
  -- The repair increment paid when going from level `j` to level `j - 1`.
  let step : ℕ → ℝ := fun j =>
    if 0 < j then B j * ((1 / 2 : ℝ) * (disc j - disc (j - 1))) else 0
  -- The invariant at level `k`: all edges stay inside level-`k` cells, the
  -- matching is maximum in every level-`k` cell, and the accumulated cost is
  -- bounded by the steps strictly above `k`.
  let P : ℕ → PartialMatching a b → Prop := fun k σ =>
    (∀ e ∈ σ.edges, cell k (x e.1) = cell k (y e.2)) ∧
    (∀ c : C k, (σ.edges.filter (fun e => cell k (x e.1) = c)).card =
      min ((Finset.univ.filter (fun i => cell k (x i) = c)).card)
          ((Finset.univ.filter (fun j => cell k (y j) = c)).card)) ∧
    σ.cost cost ≤ σ0.cost cost +
      ∑ j ∈ Finset.range (K + 1), if k < j then step j else 0
  have hPzero : P K σ0 := by
    refine ⟨hleaf, hmax, ?_⟩
    have hzero : (∑ j ∈ Finset.range (K + 1), if K < j then step j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ite_eq_right (by have h := Finset.mem_range.mp hj; omega)]
    rw [hzero]
    linarith
  have key : ∀ k : ℕ, k ≤ K → ∃ σ, P k σ := by
    have aux : ∀ m : ℕ, ∀ k : ℕ, k ≤ K → K - k ≤ m → ∃ σ, P k σ := by
      intro m
      induction m with
      | zero =>
          intro k hk hkm
          have hkK : k = K := by omega
          subst hkK
          exact ⟨σ0, hPzero⟩
      | succ m ih =>
          intro k hk hkm
          by_cases hkK : k = K
          · subst hkK
            exact ⟨σ0, hPzero⟩
          · have hklt : k < K := by omega
            have hle : k + 1 ≤ K := by omega
            obtain ⟨σ₁, hP₁⟩ := ih (k + 1) hle (by omega)
            obtain ⟨hinside₁, hmax₁, hcost₁⟩ := hP₁
            -- One repair step from level `k+1` to level `k`.
            obtain ⟨σ₂, hinside₂, hmax₂, _, hcost₂⟩ :=
              exists_maxCardMatching_le_add_repair
                (leaf := cell (k + 1)) (coarse := cell k)
                (hcompat := fun u v h => hnested k (k + 1) (by omega) u v h)
                (x := x) (y := y) (cost := cost) (σ0 := σ₁)
                hinside₁ hmax₁ (B := B (k + 1))
                (hB := fun i j h => hB k hklt i j h)
            refine ⟨σ₂, hinside₂, hmax₂, ?_⟩
            have hnotmem : k + 1 ∉ (Finset.range (K + 1)).filter (fun j => k + 1 < j) := by
              simp only [Finset.mem_filter, Finset.mem_range]
              omega
            have hSsplit : (∑ j ∈ Finset.range (K + 1), if k < j then step j else 0)
                = step (k + 1) +
                  ∑ j ∈ Finset.range (K + 1), if k + 1 < j then step j else 0 := by
              conv_lhs =>
                rw [← Finset.sum_filter (fun j => k < j) (step)]
              conv_rhs =>
                rw [← Finset.sum_filter (fun j => k + 1 < j) (step)]
              have hset : (Finset.range (K + 1)).filter (fun j => k < j) =
                  insert (k + 1)
                    ((Finset.range (K + 1)).filter (fun j => k + 1 < j)) := by
                ext j
                simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
                omega
              rw [hset, Finset.sum_insert hnotmem]
            have hstep : step (k + 1) =
                B (k + 1) * ((1 / 2 : ℝ) * (disc (k + 1) - disc k)) := by
              dsimp only [step]
              rw [ite_eq_left (Nat.succ_pos k), Nat.add_sub_cancel]
            have hcost₂' : σ₂.cost cost ≤ σ₁.cost cost + step (k + 1) := by
              rw [hstep]
              simpa only [disc] using hcost₂
            rw [hSsplit]
            linarith
    intro k hk
    exact aux (K - k) k hk le_rfl
  obtain ⟨σ, hP⟩ := key 0 (Nat.zero_le K)
  obtain ⟨_, hmax0, hcost⟩ := hP
  refine ⟨σ, card_eq_min_of_root (cell 0) x y hroot σ hmax0, ?_⟩
  have hS0 : (∑ j ∈ Finset.range (K + 1), if 0 < j then step j else 0) =
      ∑ k ∈ Finset.range (K + 1), if 0 < k then
        B k * (1 / 2 : ℝ) *
          ((∑ c : C k,
              |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c|) -
           (∑ p : C (k - 1),
              |partitionCount (cell (k - 1) ∘ x) p -
               partitionCount (cell (k - 1) ∘ y) p|))
      else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : 0 < k
    · rw [ite_eq_left hk, ite_eq_left hk]
      dsimp only [step, disc]
      rw [ite_eq_left hk]
      ring
    · rw [ite_eq_right hk, ite_eq_right hk]
  rw [← hS0]
  exact hcost

end OTSelector
