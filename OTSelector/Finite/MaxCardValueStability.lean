import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.BlockMatchingComparison
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Finite.MatchingEmbedding
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching

/-!
# Finite.MaxCardValueStability

**Conditions:** Finite row/column equivalences or δ adjoined rows; quantitative comparisons assume B≥0 and |c|≤B.

**Objects:** Reindexed matching values and the restricted old-row matching value.

**Proof detail:** Transport both feasible sets along inverse equivalences; for size changes delete at most δ edges and repair free endpoints, charging at most B per deleted or appended edge.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/



/-!
## Lemma skeleton

* **Conditions:** The reindexing results use equivalences of finite row and column types; costs are pulled back through the inverse equivalences. The adding-rows results compare Fin a with its original copy inside Fin(a+delta), for arbitrary natural a,b,delta. The quantitative perturbation bounds assume B >= 0 and abs(c(i,j)) <= B uniformly. The empty-column value identity permits an arbitrary row size and imposes no cost assumption.
* **Objects:** reindex: mapEmbedding for equivalences of the original finite index sets; old and new rows: indices i with i.val < a and its complement inside Fin(a+delta); restricted cost: the same ambient matrix evaluated on the old-row embedding; delta: the actual number of adjoined source endpoints; no asymptotic or fitted parameter
* **Proof detail:** Transport feasible matchings along inverse finite equivalences to identify both objective sets. Partition the enlarged source cloud into old and new rows and use the block-plus-repair construction for the forward bound. Restrict a full enlarged optimum to edges using old rows; at most delta edges are removed. Repair the remaining old rectangle by a matching of free endpoints; bound both deletion and repair costs using abs(c) <= B. Combine the two one-sided inequalities to get the absolute bound.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Sheldon Axler, *Supplement for Measure, Integration & Real Analysis*, Section C, Definitions 0.32 and 0.35, pp. 18–19.
  https://measure.axler.net/SupplementMIRA.pdf#page=18
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** Reindexing, deletion and free-endpoint repair yield the signed-cost two-sided value estimate. Its coefficient two is proved by local cost accounting; no probabilistic or spatial assumption is present.
-/

/-!
# Stability of the maximum-cardinality value under adding points

When extra source points are adjoined to a cloud, the optimal maximum-cardinality
value changes by at most twice the uniform edge bound per added point.  The
upper bound is the block construction (old block optimal plus repair of the new
points); the lower bound keeps the old edges of a big optimum and augments them
inside the old rectangle.

This is the deterministic count-continuity estimate used to compare the
finite-volume pressure at different sample sizes.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

namespace PartialMatching

variable {m n m' n' : ℕ}

/-- Transport a partial matching along equivalences of the row and column types. -/
def reindex (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') (σ : PartialMatching m n) :
    PartialMatching m' n' :=
  mapEmbedding e.toEmbedding f.toEmbedding σ

theorem card_reindex (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n')
    (σ : PartialMatching m n) :
    (reindex e f σ).card = σ.card :=
  card_mapEmbedding e.toEmbedding f.toEmbedding σ

theorem cost_reindex (c : Fin m → Fin n → ℝ) (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n')
    (σ : PartialMatching m n) :
    (reindex e f σ).cost (fun i j ↦ c (e.symm i) (f.symm j)) = σ.cost c := by
  simpa [reindex] using cost_mapEmbedding e.toEmbedding f.toEmbedding σ
    (fun i j ↦ c (e.symm i) (f.symm j))

/-- Reindexing rows and columns by equivalences does not change the value. -/
theorem maxCardValue_reindex (c : Fin m → Fin n → ℝ) (e : Fin m ≃ Fin m')
    (f : Fin n ≃ Fin n') :
    maxCardValue (fun i j ↦ c (e.symm i) (f.symm j)) = maxCardValue c := by
  classical
  have hm : m = m' := by simpa using Fintype.card_congr e
  have hn : n = n' := by simpa using Fintype.card_congr f
  subst hm
  subst hn
  unfold maxCardValue
  congr 1
  ext v
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨reindex e.symm f.symm σ, ?_, ?_⟩
    · rw [card_reindex, hσ]
    · have h := cost_reindex (fun i j ↦ c (e.symm i) (f.symm j)) e.symm f.symm σ
      simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using h.symm
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨reindex e f σ, ?_, ?_⟩
    · rw [card_reindex, hσ]
    · exact (cost_reindex c e f σ).symm

/-- A matching into an empty column type is empty, so its value is zero. -/
theorem maxCardValue_of_empty_cols {m : ℕ} (c : Fin m → Fin 0 → ℝ) :
    maxCardValue c = 0 := by
  classical
  have hempty : ∀ σ : PartialMatching m 0, σ.cost c = 0 := by
    intro σ
    have hedges : σ.edges = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨i, j⟩ -
      exact j.elim0
    unfold cost
    rw [hedges]
    simp
  unfold maxCardValue
  have hset : {v : ℝ | ∃ σ : PartialMatching m 0, σ.card = min m 0 ∧ v = σ.cost c} = {0} := by
    ext v
    constructor
    · rintro ⟨σ, -, rfl⟩
      simp [hempty σ]
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨diagonal m 0, card_diagonal m 0, (hempty _).symm⟩
  rw [hset]
  simp

variable {a b δ : ℕ}

/-- The old rows among `Fin (a + δ)` number `a`. -/
theorem card_old_rows :
    (Finset.univ.filter (fun i : Fin (a + δ) => i.val < a)).card = a := by
  classical
  have himg : Finset.univ.filter (fun i : Fin (a + δ) => i.val < a)
      = (Finset.univ : Finset (Fin a)).image (Fin.castLE (Nat.le_add_right a δ)) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter] at hi
      exact Finset.mem_image.mpr ⟨⟨i.val, hi.2⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro hi
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [← hj]; exact j.isLt⟩
  rw [himg, Finset.card_image_of_injOn]
  · simp
  · intro x _ y _ h
    exact Fin.castLE_injective (Nat.le_add_right a δ) h

/-- The new rows among `Fin (a + δ)` number `δ`. -/
theorem card_new_rows :
    (Finset.univ.filter (fun i : Fin (a + δ) => ¬ i.val < a)).card = δ := by
  classical
  have := card_old_rows (a := a) (δ := δ)
  have hcompl := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (a + δ)))) (p := fun i => i.val < a)
  simp only [Finset.card_univ, Fintype.card_fin] at hcompl
  omega

/-- Adjoining `δ` source points changes the maximum-cardinality value by at most
`B * δ` from above, when all edge costs are bounded by `B` in absolute value. -/
theorem maxCardValue_add_rows_le (c : Fin (a + δ) → Fin b → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    maxCardValue c ≤
      maxCardValue (fun i : Fin a => fun j : Fin b =>
        c (Fin.castLE (Nat.le_add_right a δ) i) j) + B * (δ : ℝ) := by
  classical
  let blockS : Fin (a + δ) → Bool := fun i => decide (i.val < a)
  let blockT : Fin b → Bool := fun _ => true
  have hupper : ∀ i j, c i j ≤ B := fun i j => (abs_le.mp (hB i j)).2
  have hmain := maxCardValue_le_sum_block_maxCardValue blockS blockT c hupper
  have hsizeS_true : blockSizeS blockS true = a := by
    simp only [blockSizeS, blockFinset, blockS, decide_eq_true_eq]
    exact card_old_rows
  have hsizeS_false : blockSizeS blockS false = δ := by
    simp only [blockSizeS, blockFinset, blockS, decide_eq_false_iff_not]
    exact card_new_rows
  have hsizeT_true : blockSizeT blockT true = b := by
    simp only [blockSizeT, blockFinset, blockT]
    simp
  have hsizeT_false : blockSizeT blockT false = 0 := by
    simp only [blockSizeT, blockFinset, blockT]
    simp
  have hnew : maxCardValue (blockCost blockS blockT c false) = 0 := by
    have hre := maxCardValue_reindex (blockCost blockS blockT c false)
      (Equiv.refl (Fin (blockSizeS blockS false))) (finCongr hsizeT_false)
    rw [← hre]
    exact maxCardValue_of_empty_cols _
  have hold : maxCardValue (blockCost blockS blockT c true) =
      maxCardValue (fun i : Fin a => fun j : Fin b =>
        c (Fin.castLE (Nat.le_add_right a δ) i) j) := by
    let eFun : Fin (blockSizeS blockS true) → Fin a := fun i =>
      ⟨(blockEmbeddingS blockS true i).val, by
        have hmem := blockEmbeddingS_mem blockS true i
        simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and, blockS] at hmem
        exact of_decide_eq_true hmem⟩
    have heInj : Function.Injective eFun := by
      intro i j h
      have hv : (blockEmbeddingS blockS true i).val =
          (blockEmbeddingS blockS true j).val := by
        simpa only [eFun] using congrArg Fin.val h
      exact blockEmbeddingS_injective blockS true (Fin.ext hv)
    have heBij : Function.Bijective eFun :=
      Fintype.bijective_iff_injective_and_card eFun |>.mpr ⟨heInj, by simp [hsizeS_true]⟩
    let e : Fin (blockSizeS blockS true) ≃ Fin a := Equiv.ofBijective eFun heBij
    have hembed : ∀ i, blockEmbeddingS blockS true i =
        Fin.castLE (Nat.le_add_right a δ) (e i) := by
      intro i
      exact Fin.ext rfl
    let fFun : Fin (blockSizeT blockT true) → Fin b := fun j =>
      ⟨(blockEmbeddingT blockT true j).val, by
        have hmem := blockEmbeddingT_mem blockT true j
        simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and, blockT] at hmem
        omega⟩
    have hfInj : Function.Injective fFun := by
      intro i j h
      have hv : (blockEmbeddingT blockT true i).val =
          (blockEmbeddingT blockT true j).val := by
        simpa only [fFun] using congrArg Fin.val h
      exact blockEmbeddingT_injective blockT true (Fin.ext hv)
    have hfBij : Function.Bijective fFun :=
      Fintype.bijective_iff_injective_and_card fFun |>.mpr ⟨hfInj, by simp [hsizeT_true]⟩
    let f : Fin (blockSizeT blockT true) ≃ Fin b := Equiv.ofBijective fFun hfBij
    have hembedT : ∀ j, blockEmbeddingT blockT true j = f j := by
      intro j
      exact Fin.ext rfl
    have hcost : blockCost blockS blockT c true =
        fun i j => (fun i' : Fin a => fun j' : Fin b =>
          c (Fin.castLE (Nat.le_add_right a δ) i') j') (e i) (f j) := by
      funext i j
      simp only [blockCost, hembed, hembedT]
    rw [hcost]
    have hre := maxCardValue_reindex
      (fun i : Fin a => fun j : Fin b => c (Fin.castLE (Nat.le_add_right a δ) i) j)
      e.symm f.symm
    simpa only [Equiv.symm_symm] using hre
  have hsum : (∑ t : Bool, maxCardValue (blockCost blockS blockT c t)) =
      maxCardValue (fun i : Fin a => fun j : Fin b =>
        c (Fin.castLE (Nat.le_add_right a δ) i) j) := by
    rw [Fintype.sum_bool]
    simp only [hnew, hold]
    ring
  have hJ : (∑ t : Bool, min (blockSizeS blockS t) (blockSizeT blockT t)) = min a b := by
    rw [Fintype.sum_bool]
    simp only [hsizeS_true, hsizeS_false, hsizeT_true, hsizeT_false]
    simp
  have hres : min (a + δ - ∑ t : Bool, min (blockSizeS blockS t) (blockSizeT blockT t))
      (b - ∑ t : Bool, min (blockSizeS blockS t) (blockSizeT blockT t)) ≤ δ := by
    rw [hJ]
    rcases le_total a b with h | h
    · have hmin : min a b = a := min_eq_left h
      rw [hmin]
      have h1 : a + δ - a = δ := by omega
      rw [h1]
      exact min_le_left _ _
    · have hmin : min a b = b := min_eq_right h
      rw [hmin]
      have h1 : b - b = 0 := by omega
      rw [h1, min_zero]
      exact Nat.zero_le δ
  rw [hsum] at hmain
  have hBnonneg : 0 ≤ B := hB0
  have hres' : ((min (a + δ - ∑ t : Bool, min (blockSizeS blockS t) (blockSizeT blockT t))
      (b - ∑ t : Bool, min (blockSizeS blockS t) (blockSizeT blockT t)) : ℕ) : ℝ) ≤ (δ : ℝ) := by
    exact_mod_cast hres
  nlinarith [hmain, mul_le_mul_of_nonneg_left hres' hBnonneg]

/-- Removing `δ` source points changes the maximum-cardinality value by at most
`2 B δ` from below, when all edge costs are bounded by `B` in absolute value. -/
theorem maxCardValue_le_add_rows (c : Fin (a + δ) → Fin b → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    maxCardValue (fun i : Fin a => fun j : Fin b =>
        c (Fin.castLE (Nat.le_add_right a δ) i) j) ≤
      maxCardValue c + 2 * B * (δ : ℝ) := by
  classical
  let smallCost : Fin a → Fin b → ℝ := fun i j =>
    c (Fin.castLE (Nat.le_add_right a δ) i) j
  obtain ⟨σ, hσ, hσc⟩ := exists_cost_eq_maxCardValue c
  let keep : Finset (Fin (a + δ) × Fin b) :=
    σ.edges.filter (fun p => p.1.val < a)
  let removed : Finset (Fin (a + δ) × Fin b) := σ.edges \ keep
  let smallMap : {p // p ∈ keep} → Fin a × Fin b := fun q =>
    ((⟨q.1.1.val, (Finset.mem_filter.mp q.2).2⟩ : Fin a), q.1.2)
  let smallEdges : Finset (Fin a × Fin b) := keep.attach.image smallMap
  have hsmallMap_inj : Set.InjOn smallMap ↑keep.attach := by
    intro q _ q' _ h
    have hrow : q.1.1.val = q'.1.1.val :=
      congrArg (fun p : Fin a × Fin b => p.1.val) h
    have hcol : q.1.2 = q'.1.2 :=
      congrArg (fun p : Fin a × Fin b => p.2) h
    have h1 : q.1.1 = q'.1.1 := Fin.ext hrow
    have h2 : q.1 = q'.1 := Prod.ext h1 hcol
    exact Subtype.ext h2
  let κ : PartialMatching a b :=
    { edges := smallEdges
      row_inj := by
        intro e he e' he' hrow
        obtain ⟨q, -, hq⟩ := Finset.mem_image.mp he
        obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp he'
        have hrow' : q.1.1.val = q'.1.1.val := by
          have h := hrow
          rw [← hq, ← hq'] at h
          exact congrArg (fun x : Fin a => x.val) h
        have hrow'' : q.1.1 = q'.1.1 := Fin.ext hrow'
        have hfull : q.1 = q'.1 := σ.row_inj q.1 (Finset.mem_filter.mp q.2).1
          q'.1 (Finset.mem_filter.mp q'.2).1 hrow''
        have hqq : q = q' := Subtype.ext hfull
        rw [← hq, ← hq', hqq]
      col_inj := by
        intro e he e' he' hcol
        obtain ⟨q, -, hq⟩ := Finset.mem_image.mp he
        obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp he'
        have hcol' : q.1.2 = q'.1.2 := by
          have h := hcol
          rw [← hq, ← hq'] at h
          exact h
        have hfull : q.1 = q'.1 := σ.col_inj q.1 (Finset.mem_filter.mp q.2).1
          q'.1 (Finset.mem_filter.mp q'.2).1 hcol'
        have hqq : q = q' := Subtype.ext hfull
        rw [← hq, ← hq', hqq] }
  have hκcard : κ.card = keep.card := by
    show smallEdges.card = keep.card
    rw [Finset.card_image_of_injOn hsmallMap_inj, Finset.card_attach]
  have hκcost : κ.cost smallCost = ∑ p ∈ keep, c p.1 p.2 := by
    show ∑ e ∈ smallEdges, smallCost e.1 e.2 = ∑ p ∈ keep, c p.1 p.2
    rw [Finset.sum_image hsmallMap_inj]
    trans ∑ q ∈ keep.attach, c q.1.1 q.1.2
    · refine Finset.sum_congr rfl fun q _ => ?_
      show c (Fin.castLE (Nat.le_add_right a δ)
        (⟨q.1.1.val, (Finset.mem_filter.mp q.2).2⟩ : Fin a)) q.1.2 =
          c q.1.1 q.1.2
      rw [show Fin.castLE (Nat.le_add_right a δ)
        (⟨q.1.1.val, (Finset.mem_filter.mp q.2).2⟩ : Fin a) = q.1.1 from Fin.ext rfl]
    · simpa only using Finset.sum_attach keep
        (fun p : Fin (a + δ) × Fin b => c p.1 p.2)
  -- The removed edges inject into `Fin δ`.
  have hremoved_card : removed.card ≤ δ := by
    let g : {p // p ∈ removed} → Fin δ := fun q =>
      ⟨q.1.1.val - a, by
        have hlt : q.1.1.val < a + δ := q.1.1.isLt
        have hnkeep : q.1 ∉ keep := (Finset.mem_sdiff.mp q.2).2
        have hge : a ≤ q.1.1.val := by
          by_contra hc
          push_neg at hc
          exact hnkeep (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q.2).1, hc⟩)
        omega⟩
    have hg_inj : Function.Injective g := by
      intro q q' h
      have hv : q.1.1.val - a = q'.1.1.val - a := congrArg Fin.val h
      have hge_q : a ≤ q.1.1.val := by
        have hnkeep : q.1 ∉ keep := (Finset.mem_sdiff.mp q.2).2
        by_contra hc
        push_neg at hc
        exact hnkeep (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q.2).1, hc⟩)
      have hge_q' : a ≤ q'.1.1.val := by
        have hnkeep : q'.1 ∉ keep := (Finset.mem_sdiff.mp q'.2).2
        by_contra hc
        push_neg at hc
        exact hnkeep (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q'.2).1, hc⟩)
      have hrow : q.1.1.val = q'.1.1.val := by omega
      have hrow' : q.1.1 = q'.1.1 := Fin.ext hrow
      have hfull : q.1 = q'.1 := σ.row_inj q.1 (Finset.mem_sdiff.mp q.2).1
        q'.1 (Finset.mem_sdiff.mp q'.2).1 hrow'
      exact Subtype.ext hfull
    have := Fintype.card_le_of_injective g hg_inj
    rwa [Fintype.card_coe, Fintype.card_fin] at this
  -- The partition of the big edge set.
  have hkeep_sub : keep ⊆ σ.edges := Finset.filter_subset _ _
  have hpartition : σ.edges = keep ∪ removed :=
    (Finset.union_sdiff_of_subset hkeep_sub).symm
  have hdisj : Disjoint keep removed := Finset.disjoint_sdiff
  have hcard_split : σ.card = keep.card + removed.card := by
    unfold PartialMatching.card
    rw [hpartition, Finset.card_union_of_disjoint hdisj]
  have hsum_split : σ.cost c = (∑ p ∈ keep, c p.1 p.2) +
      ∑ p ∈ removed, c p.1 p.2 := by
    unfold PartialMatching.cost
    rw [hpartition, Finset.sum_union hdisj]
  have hremoved_lower : -B * (removed.card : ℝ) ≤ ∑ p ∈ removed, c p.1 p.2 := by
    have hterm : ∀ p ∈ removed, (-B : ℝ) ≤ c p.1 p.2 :=
      fun p _ => (abs_le.mp (hB p.1 p.2)).1
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    linarith
  -- Augment the kept old edges to a maximum-cardinality old matching.
  obtain ⟨τ, hτcard, hτcost⟩ := exists_maxCardinality_cost_le smallCost κ
    (fun i j => (abs_le.mp (hB (Fin.castLE (Nat.le_add_right a δ) i) j)).2)
  have hvalue_le : maxCardValue smallCost ≤
      κ.cost smallCost + ((min a b - κ.card : ℕ) : ℝ) * B := by
    refine (maxCardValue_le_of_card smallCost hτcard).trans ?_
    exact hτcost
  -- Cardinality comparison.
  have hres_le_removed : min a b - κ.card ≤ removed.card := by
    have hmin_le : min a b ≤ min (a + δ) b := min_le_min (Nat.le_add_right a δ) le_rfl
    have hκle : κ.card ≤ min a b := κ.card_le
    omega
  have hkeepcost_le : (∑ p ∈ keep, c p.1 p.2) ≤
      σ.cost c + B * (removed.card : ℝ) := by
    linarith
  calc maxCardValue smallCost ≤ κ.cost smallCost + ((min a b - κ.card : ℕ) : ℝ) * B := hvalue_le
    _ = (∑ p ∈ keep, c p.1 p.2) + ((min a b - κ.card : ℕ) : ℝ) * B := by rw [hκcost]
    _ ≤ (σ.cost c + B * (removed.card : ℝ)) + (removed.card : ℝ) * B := by
        have h1 := mul_le_mul_of_nonneg_left (by exact_mod_cast hres_le_removed :
          ((min a b - κ.card : ℕ) : ℝ) ≤ (removed.card : ℝ)) hB0
        linarith
    _ = σ.cost c + 2 * B * (removed.card : ℝ) := by ring
    _ ≤ maxCardValue c + 2 * B * (δ : ℝ) := by
        rw [← hσc]
        have h1 : B * (removed.card : ℝ) ≤ B * (δ : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hremoved_card) hB0
        nlinarith

/-- Two-sided count stability: adjoining or removing `δ` source points changes the
maximum-cardinality value by at most `2 B δ`. -/
theorem abs_maxCardValue_sub_le_add_rows (c : Fin (a + δ) → Fin b → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    |maxCardValue c -
      maxCardValue (fun i : Fin a => fun j : Fin b =>
        c (Fin.castLE (Nat.le_add_right a δ) i) j)| ≤ 2 * B * (δ : ℝ) := by
  have h1 := maxCardValue_add_rows_le c hB0 hB
  have h2 := maxCardValue_le_add_rows c hB0 hB
  rw [abs_sub_le_iff]
  constructor <;> linarith

end PartialMatching

end OTSelector
