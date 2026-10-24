import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** Two finite vertex sets and an arbitrary real edge cost.
* **Objects:** A finite edge set with at most one edge at each vertex.
* **Proof detail:** Count used and unused vertices; add a free row/column edge; iterate the cardinality increase.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** The complete-bipartite extension cost estimates and maxCardValue infimum encoding are proved here; the cited chapter supplies the matching definition and augmentation method.
-/

/-!
# Partial matchings between two finite types

A partial matching of `Fin m` into `Fin n` is a finite set of edges with at most
one edge at each row and at each column.  We record the matching as a `Finset` of
pairs together with the two uniqueness properties.  The module proves:

* every matching has at most `min m n` edges;
* a maximum-cardinality matching exists;
* a matching can be augmented to maximum cardinality by adding edges through
  previously unused rows and columns, and each added edge contributes at most a
  prescribed upper bound to the cost.

These are the finite combinatorial inputs of the multi-scale matching pressure:
a block decomposition produces partial matchings, and the unmatched points are
repaired through unused rows and columns.
-/

open scoped BigOperators

namespace OTSelector

/-- A partial matching of `Fin m` into `Fin n`. -/
structure PartialMatching (m n : ℕ) where
  /-- The set of matched row-column pairs. -/
  edges : Finset (Fin m × Fin n)
  /-- Each row occurs at most once. -/
  row_inj : ∀ e ∈ edges, ∀ e' ∈ edges, e.1 = e'.1 → e = e'
  /-- Each column occurs at most once. -/
  col_inj : ∀ e ∈ edges, ∀ e' ∈ edges, e.2 = e'.2 → e = e'

namespace PartialMatching

variable {m n : ℕ}

/-- The set of rows used by a partial matching. -/
def rows (σ : PartialMatching m n) : Finset (Fin m) := σ.edges.image Prod.fst

/-- The set of columns used by a partial matching. -/
def cols (σ : PartialMatching m n) : Finset (Fin n) := σ.edges.image Prod.snd

/-- The cardinality of a partial matching. -/
def card (σ : PartialMatching m n) : ℕ := σ.edges.card

/-- The total cost of a partial matching. -/
def cost (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n) : ℝ :=
  ∑ e ∈ σ.edges, c e.1 e.2

@[simp] theorem card_mk (edges : Finset (Fin m × Fin n)) (h₁ h₂) :
    card ⟨edges, h₁, h₂⟩ = edges.card := rfl

@[simp] theorem edges_mk (edges : Finset (Fin m × Fin n)) (h₁ h₂) :
    (⟨edges, h₁, h₂⟩ : PartialMatching m n).edges = edges := rfl

theorem card_rows (σ : PartialMatching m n) : σ.rows.card = σ.card := by
  classical
  unfold rows card
  rw [Finset.card_image_of_injOn]
  intro e he e' he' h
  exact σ.row_inj e he e' he' h

theorem card_cols (σ : PartialMatching m n) : σ.cols.card = σ.card := by
  classical
  unfold cols card
  rw [Finset.card_image_of_injOn]
  intro e he e' he' h
  exact σ.col_inj e he e' he' h

/-- A matching has at most `min m n` edges. -/
theorem card_le (σ : PartialMatching m n) : σ.card ≤ min m n := by
  have hr : σ.card ≤ m := by
    rw [← σ.card_rows]
    simpa using Finset.card_le_univ σ.rows
  have hc : σ.card ≤ n := by
    rw [← σ.card_cols]
    simpa using Finset.card_le_univ σ.cols
  omega

/-- The matched pair at diagonal index `k`. -/
def diagPair (m n : ℕ) (k : Fin (min m n)) : Fin m × Fin n :=
  (⟨k.val, lt_of_lt_of_le k.isLt (min_le_left m n)⟩,
   ⟨k.val, lt_of_lt_of_le k.isLt (min_le_right m n)⟩)

theorem diagPair_fst_eq {m n : ℕ} {a b : Fin (min m n)}
    (h : (diagPair m n a).1 = (diagPair m n b).1) : a = b :=
  Fin.ext (by simpa [diagPair] using congrArg Fin.val h)

theorem diagPair_snd_eq {m n : ℕ} {a b : Fin (min m n)}
    (h : (diagPair m n a).2 = (diagPair m n b).2) : a = b :=
  Fin.ext (by simpa [diagPair] using congrArg Fin.val h)

theorem diagPair_injective (m n : ℕ) : Function.Injective (diagPair m n) := by
  intro a b h
  exact diagPair_fst_eq (by rw [h])

/-- The diagonal maximum-cardinality matching. -/
noncomputable def diagonal (m n : ℕ) : PartialMatching m n where
  edges := Finset.univ.image (diagPair m n)
  row_inj := by
    intro e he e' he' hrow
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he'
    rw [diagPair_fst_eq hrow]
  col_inj := by
    intro e he e' he' hcol
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he'
    rw [diagPair_snd_eq hcol]

/-- The diagonal matching has maximum cardinality. -/
theorem card_diagonal (m n : ℕ) : (diagonal m n).card = min m n := by
  classical
  unfold card diagonal
  rw [Finset.card_image_of_injective _ (diagPair_injective m n)]
  simp

/-- Every total cost is bounded by the cardinality times a uniform edge bound. -/
theorem cost_le_card_mul (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n)
    {B : ℝ} (hB : ∀ i j, c i j ≤ B) :
    σ.cost c ≤ (σ.card : ℝ) * B := by
  classical
  unfold cost card
  calc
    ∑ e ∈ σ.edges, c e.1 e.2 ≤ ∑ _e ∈ σ.edges, B :=
      Finset.sum_le_sum fun e _ ↦ hB e.1 e.2
    _ = (σ.edges.card : ℝ) * B := by simp [Finset.sum_const, nsmul_eq_mul]

/-! ## Augmentation -/

/-- Rows not used by a partial matching. -/
def freeRows (σ : PartialMatching m n) : Finset (Fin m) := Finset.univ \ σ.rows

/-- Columns not used by a partial matching. -/
def freeCols (σ : PartialMatching m n) : Finset (Fin n) := Finset.univ \ σ.cols

theorem card_freeRows (σ : PartialMatching m n) :
    σ.freeRows.card = m - σ.card := by
  rw [freeRows, Finset.card_sdiff_of_subset (Finset.subset_univ σ.rows), Finset.card_univ,
    Fintype.card_fin, σ.card_rows]

theorem card_freeCols (σ : PartialMatching m n) :
    σ.freeCols.card = n - σ.card := by
  rw [freeCols, Finset.card_sdiff_of_subset (Finset.subset_univ σ.cols), Finset.card_univ,
    Fintype.card_fin, σ.card_cols]

/-- Adding one edge through a free row and a free column preserves a partial matching. -/
def insertEdge (σ : PartialMatching m n) {i : Fin m} {j : Fin n}
    (hi : i ∈ σ.freeRows) (hj : j ∈ σ.freeCols) :
    PartialMatching m n where
  edges := insert (i, j) σ.edges
  row_inj := by
    intro e he e' he' hrow
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp he' with rfl | he'
      · rfl
      · exact absurd (Finset.mem_image.mpr ⟨e', he', hrow.symm⟩)
          (Finset.mem_sdiff.mp hi).2
    · rcases Finset.mem_insert.mp he' with rfl | he'
      · exact absurd (Finset.mem_image.mpr ⟨e, he, hrow⟩)
          (Finset.mem_sdiff.mp hi).2
      · exact σ.row_inj e he e' he' hrow
  col_inj := by
    intro e he e' he' hcol
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp he' with rfl | he'
      · rfl
      · exact absurd (Finset.mem_image.mpr ⟨e', he', hcol.symm⟩)
          (Finset.mem_sdiff.mp hj).2
    · rcases Finset.mem_insert.mp he' with rfl | he'
      · exact absurd (Finset.mem_image.mpr ⟨e, he, hcol⟩)
          (Finset.mem_sdiff.mp hj).2
      · exact σ.col_inj e he e' he' hcol

theorem edges_subset_insertEdge (σ : PartialMatching m n) {i : Fin m} {j : Fin n}
    (hi : i ∈ σ.freeRows) (hj : j ∈ σ.freeCols) :
    σ.edges ⊆ (σ.insertEdge hi hj).edges := by
  intro e he
  exact Finset.mem_insert_of_mem he

theorem card_insertEdge (σ : PartialMatching m n) {i : Fin m} {j : Fin n}
    (hi : i ∈ σ.freeRows) (hj : j ∈ σ.freeCols) :
    (σ.insertEdge hi hj).card = σ.card + 1 := by
  classical
  unfold card insertEdge
  rw [Finset.card_insert_of_notMem]
  · intro hmem
    have hri : i ∈ σ.rows := Finset.mem_image.mpr ⟨(i, j), hmem, rfl⟩
    exact (Finset.mem_sdiff.mp hi).2 hri

theorem cost_insertEdge (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n)
    {i : Fin m} {j : Fin n} (hi : i ∈ σ.freeRows) (hj : j ∈ σ.freeCols) :
    (σ.insertEdge hi hj).cost c = σ.cost c + c i j := by
  classical
  unfold cost insertEdge
  rw [Finset.sum_insert]
  · ring
  · intro hmem
    have hri : i ∈ σ.rows := Finset.mem_image.mpr ⟨(i, j), hmem, rfl⟩
    exact (Finset.mem_sdiff.mp hi).2 hri

/-- A matching below maximum cardinality has at least one free row and one free column. -/
theorem freeRows_nonempty_of_lt (σ : PartialMatching m n) (h : σ.card < min m n) :
    σ.freeRows.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have h0 : σ.freeRows.card = 0 := by rw [hempty]; simp
  rw [σ.card_freeRows] at h0
  omega

theorem freeCols_nonempty_of_lt (σ : PartialMatching m n) (h : σ.card < min m n) :
    σ.freeCols.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have h0 : σ.freeCols.card = 0 := by rw [hempty]; simp
  rw [σ.card_freeCols] at h0
  omega

/-- Add `k` new edges through free rows and free columns; every added edge costs
at most `B`.  The resulting matching is an extension of the original one. -/
theorem exists_augment (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n)
    {B : ℝ} (hB : ∀ i j, c i j ≤ B) :
    ∀ k : ℕ, k ≤ min m n - σ.card →
      ∃ τ : PartialMatching m n,
        σ.edges ⊆ τ.edges ∧ τ.card = σ.card + k ∧
          τ.cost c ≤ σ.cost c + (k : ℝ) * B := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨σ, subset_rfl, by simp, by simp⟩
  | succ k ih =>
      intro hk
      have hk' : k ≤ min m n - σ.card := by omega
      obtain ⟨τ, hsub, hcard, hcost⟩ := ih hk'
      have hlt : τ.card < min m n := by omega
      obtain ⟨i, hi⟩ := τ.freeRows_nonempty_of_lt hlt
      obtain ⟨j, hj⟩ := τ.freeCols_nonempty_of_lt hlt
      refine ⟨τ.insertEdge hi hj, hsub.trans (τ.edges_subset_insertEdge hi hj),
        τ.card_insertEdge hi hj ▸ by omega, ?_⟩
      rw [τ.cost_insertEdge c hi hj]
      have hnew : c i j ≤ B := hB i j
      have hkr : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hkr]
      nlinarith [hcost, hnew]

/-- A maximum-cardinality matching with cost at most the original matching cost
plus the uniform edge bound for every added edge. -/
theorem exists_maxCardinality_cost_le (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n)
    {B : ℝ} (hB : ∀ i j, c i j ≤ B) :
    ∃ τ : PartialMatching m n,
      τ.card = min m n ∧
        τ.cost c ≤ σ.cost c + ((min m n - σ.card : ℕ) : ℝ) * B := by
  obtain ⟨τ, hsub, hcard, hcost⟩ := exists_augment c σ hB (min m n - σ.card) le_rfl
  refine ⟨τ, ?_, ?_⟩
  · rw [hcard]
    have := σ.card_le
    omega
  · convert hcost using 1

/-- A sub-matching of a partial matching, obtained by keeping a subset of its edges. -/
def subMatching (σ : PartialMatching m n) (s : Finset (Fin m × Fin n)) (hs : s ⊆ σ.edges) :
    PartialMatching m n where
  edges := s
  row_inj := fun e he e' he' h ↦ σ.row_inj e (hs he) e' (hs he') h
  col_inj := fun e he e' he' h ↦ σ.col_inj e (hs he) e' (hs he') h

@[simp] theorem subMatching_edges (σ : PartialMatching m n) (s : Finset (Fin m × Fin n))
    (hs : s ⊆ σ.edges) : (σ.subMatching s hs).edges = s := rfl

/-- Every partial matching contains a sub-matching of any smaller cardinality. -/
theorem exists_subMatching_card (σ : PartialMatching m n) {k : ℕ} (hk : k ≤ σ.card) :
    ∃ (s : Finset (Fin m × Fin n)) (hs : s ⊆ σ.edges),
      (σ.subMatching s hs).card = k := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hk
  exact ⟨s, hs, hcard⟩

/-- If all edge costs are nonnegative, a sub-matching costs at most the original matching. -/
theorem cost_subMatching_le (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n)
    (s : Finset (Fin m × Fin n)) (hs : s ⊆ σ.edges)
    (hnonneg : ∀ i j, 0 ≤ c i j) :
    (σ.subMatching s hs).cost c ≤ σ.cost c := by
  classical
  unfold cost subMatching
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun e _ _ ↦ hnonneg e.1 e.2)

/-- A matching that is optimal among all matchings of its own cardinality. -/
def IsMinCard (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n) : Prop :=
  ∀ ρ : PartialMatching m n, ρ.card = σ.card → σ.cost c ≤ ρ.cost c

/-- With nonnegative costs, a minimum matching of smaller cardinality costs at most any
maximum-cardinality matching.  Dropping edges from the maximum matching produces a feasible
smaller matching whose cost is no larger. -/
theorem IsMinCard.cost_le_of_max (c : Fin m → Fin n → ℝ) {σ τ : PartialMatching m n}
    (hσ : σ.IsMinCard c) (hτ : τ.card = min m n) (hnonneg : ∀ i j, 0 ≤ c i j) :
    σ.cost c ≤ τ.cost c := by
  have hk : σ.card ≤ τ.card := by rw [hτ]; exact σ.card_le
  obtain ⟨s, hs, hcard⟩ := τ.exists_subMatching_card hk
  have hmin := hσ (τ.subMatching s hs) hcard
  have hle := τ.cost_subMatching_le c s hs hnonneg
  linarith

/-- The least cost of a maximum-cardinality partial matching. -/
noncomputable def maxCardValue (c : Fin m → Fin n → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c}

/-- The maximum-cardinality value of a nonnegative cost matrix is nonnegative. -/
theorem maxCardValue_nonneg {c : Fin m → Fin n → ℝ}
    (h : ∀ i j, 0 ≤ c i j) : 0 ≤ maxCardValue c := by
  classical
  unfold maxCardValue
  apply le_csInf
  · exact ⟨_, diagonal m n, card_diagonal m n, rfl⟩
  · rintro v ⟨σ, -, rfl⟩
    exact Finset.sum_nonneg fun e _ => h e.1 e.2

theorem maxCardValue_le (c : Fin m → Fin n → ℝ) {σ : PartialMatching m n}
    (hσ : σ.card = min m n) (hnonneg : ∀ i j, 0 ≤ c i j) :
    maxCardValue c ≤ σ.cost c := by
  classical
  apply csInf_le
  · exact ⟨0, fun v hv ↦ by
      obtain ⟨ρ, _, rfl⟩ := hv
      exact Finset.sum_nonneg fun e _ ↦ hnonneg e.1 e.2⟩
  · exact ⟨σ, hσ, rfl⟩

theorem le_maxCardValue (c : Fin m → Fin n → ℝ) {σ : PartialMatching m n}
    (hσ : σ.IsMinCard c) (hnonneg : ∀ i j, 0 ≤ c i j) :
    σ.cost c ≤ maxCardValue c := by
  classical
  apply le_csInf
  · exact ⟨(diagonal m n).cost c, ⟨diagonal m n, card_diagonal m n, rfl⟩⟩
  · intro v hv
    obtain ⟨τ, hτ, rfl⟩ := hv
    exact IsMinCard.cost_le_of_max c hσ hτ hnonneg

/-- The maximum-cardinality value exceeds a minimum matching of smaller cardinality by at
most the number of missing edges times a uniform cost bound. -/
theorem maxCardValue_le_minCard_add (c : Fin m → Fin n → ℝ) {σ : PartialMatching m n}
    (hB : ∀ i j, c i j ≤ B) (hnonneg : ∀ i j, 0 ≤ c i j) :
    maxCardValue c ≤ σ.cost c + ((min m n - σ.card : ℕ) : ℝ) * B := by
  obtain ⟨τ, hτ, hcost⟩ := exists_maxCardinality_cost_le c σ hB
  exact (maxCardValue_le c hτ hnonneg).trans hcost

end PartialMatching

end OTSelector
