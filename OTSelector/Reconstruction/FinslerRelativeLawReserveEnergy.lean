import OTSelector.MeasureTheory.MatchingGridDisplacementFlux
import OTSelector.Finite.HierarchicalPartialMatching
import OTSelector.Finite.MatchingUnion

/-!
# Quantitative hierarchical repair of adaptive orphan clouds

The retained core may depend arbitrarily on all original samples. A hierarchy
matching is constructed on its actual unused indices and lifted back to the
original arrays. The added cost is bounded by original histogram discrepancies
and the retained core's crossing flux. Legality of the added edges is recorded
separately; this unrestricted completion does not assert clock legality.
-/

open scoped BigOperators
noncomputable section

namespace OTSelector.PartialMatching

variable {m n a b : ℕ}

/-- Injective index maps transport a finite matching without changing its cost
or cardinality. -/
def embedIndices (ρ : PartialMatching a b) (s : Fin a → Fin m) (t : Fin b → Fin n)
    (hs : Function.Injective s) (ht : Function.Injective t) : PartialMatching m n where
  edges := ρ.edges.image (fun e ↦ (s e.1, t e.2))
  row_inj := by
    intro e he e' he' h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp he'
    exact congrArg (fun e ↦ (s e.1, t e.2)) (ρ.row_inj p hp p' hp' (hs h))
  col_inj := by
    intro e he e' he' h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp he'
    exact congrArg (fun e ↦ (s e.1, t e.2)) (ρ.col_inj p hp p' hp' (ht h))

theorem card_embedIndices (ρ : PartialMatching a b) (s : Fin a → Fin m)
    (t : Fin b → Fin n) (hs : Function.Injective s) (ht : Function.Injective t) :
    (ρ.embedIndices s t hs ht).card = ρ.card := by
  classical
  unfold card embedIndices
  apply Finset.card_image_of_injective
  intro e e' h
  exact Prod.ext (hs (congrArg Prod.fst h)) (ht (congrArg Prod.snd h))

theorem cost_embedIndices (ρ : PartialMatching a b) (s : Fin a → Fin m)
    (t : Fin b → Fin n) (hs : Function.Injective s) (ht : Function.Injective t)
    (cost : Fin m → Fin n → ℝ) :
    (ρ.embedIndices s t hs ht).cost cost = ρ.cost (fun i j ↦ cost (s i) (t j)) := by
  classical
  unfold OTSelector.PartialMatching.cost embedIndices
  rw [Finset.sum_image]
  intro e _ e' _ h
  exact Prod.ext (hs (congrArg Prod.fst h)) (ht (congrArg Prod.snd h))

/-- A fixed enumeration of a finite index set. -/
def finsetIndex {α : Type*} (S : Finset α) (i : Fin S.card) : α :=
  ((Finset.equivFin S).symm i).1

theorem finsetIndex_mem {α : Type*} (S : Finset α) (i : Fin S.card) :
    finsetIndex S i ∈ S := ((Finset.equivFin S).symm i).2

theorem finsetIndex_injective {α : Type*} (S : Finset α) :
    Function.Injective (finsetIndex S) := by
  intro i j h
  exact (Finset.equivFin S).symm.injective (Subtype.ext h)

theorem sum_finsetIndex {α : Type*} (S : Finset α) (f : α → ℝ) :
    (∑ i : Fin S.card, f (finsetIndex S i)) = ∑ i ∈ S, f i := by
  classical
  calc
    _ = ∑ i : S, f i := (Equiv.sum_comp (Finset.equivFin S).symm (fun i : S ↦ f i))
    _ = _ := Finset.sum_coe_sort S f

end OTSelector.PartialMatching

namespace OTSelector.Reconstruction

open OTSelector.PartialMatching

/-- Retained edges joining distinct cells of a fixed finite partition. -/
def retainedPartitionCrossings {m n : ℕ} {C : Type*}
    (σ : OTSelector.PartialMatching m n) (a : Fin m → C) (b : Fin n → C) : ℝ := by
  classical
  exact ((σ.edges.filter fun e ↦ a e.1 ≠ b e.2).card : ℝ)

/-- Actual hierarchical completion of an arbitrary retained core. The bound
uses the original clouds and the core's crossing count at each level. -/
theorem exists_completion_hierarchy_original_flux_bound
    {X : Type*} {K m n : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (σ : OTSelector.PartialMatching m n)
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ x y : X,
      cell l x = cell l y → cell k x = cell k y)
    (x : Fin m → X) (y : Fin n → X) (cost : Fin m → Fin n → ℝ)
    (base : ℝ) (hb : 0 ≤ base) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hcost : ∀ i j, cost i j ≤
      base + ∑ k, weight k * partitionDistance (cell k (x i)) (cell k (y j))) :
    ∃ τ : OTSelector.PartialMatching m n,
      τ.card = min m n ∧ σ.edges ⊆ τ.edges ∧
      (∑ e ∈ τ.edges \ σ.edges, cost e.1 e.2) ≤
        (max (m - σ.card) (n - σ.card) : ℝ) * base + (1 / 2 : ℝ) *
          ∑ k, weight k *
            ((∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c|) +
              2 * retainedPartitionCrossings σ (cell k ∘ x) (cell k ∘ y) +
              |(m : ℝ) - (n : ℝ)|) := by
  classical
  let s := finsetIndex σ.freeRows
  let t := finsetIndex σ.freeCols
  have hs := finsetIndex_injective σ.freeRows
  have ht := finsetIndex_injective σ.freeCols
  obtain ⟨ρ, hρcard, hρcost⟩ := exists_partialMatching_hierarchy_cost_bound
    cell hnested (x ∘ s) (y ∘ t) (fun i j ↦ cost (s i) (t j)) base hb weight hw
    (fun i j ↦ hcost (s i) (t j))
  let υ := ρ.embedIndices s t hs ht
  have hrows : Disjoint σ.rows υ.rows := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_sdiff.mp (finsetIndex_mem σ.freeRows e.1)).2 hi
  have hcols : Disjoint σ.cols υ.cols := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_sdiff.mp (finsetIndex_mem σ.freeCols e.2)).2 hj
  have hedge : Disjoint σ.edges υ.edges := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact (Finset.disjoint_left.mp hrows)
      (Finset.mem_image.mpr ⟨e, he, rfl⟩) (Finset.mem_image.mpr ⟨e, he', rfl⟩)
  refine ⟨σ.union υ hrows hcols, ?_, Finset.subset_union_left, ?_⟩
  · rw [card_union, card_embedIndices, hρcard, card_freeRows, card_freeCols]
    have h := σ.card_le
    omega
  · have hsdiff : (σ.edges ∪ υ.edges) \ σ.edges = υ.edges := by
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hedge.symm]
    change (∑ e ∈ (σ.edges ∪ υ.edges) \ σ.edges, cost e.1 e.2) ≤ _
    rw [hsdiff]
    change υ.cost cost ≤ _
    rw [cost_embedIndices]
    apply hρcost.trans
    have hm : σ.card ≤ m := le_trans σ.card_le (min_le_left m n)
    have hn : σ.card ≤ n := le_trans σ.card_le (min_le_right m n)
    have hsR : (σ.freeRows.card : ℝ) = (m : ℝ) - σ.card := by
      rw [σ.card_freeRows, Nat.cast_sub hm]
    have htR : (σ.freeCols.card : ℝ) = (n : ℝ) - σ.card := by
      rw [σ.card_freeCols, Nat.cast_sub hn]
    rw [hsR, htR]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left _ (hw k)
    have hdiff : |((m : ℝ) - σ.card) - ((n : ℝ) - σ.card)| =
        |(m : ℝ) - (n : ℝ)| := by
      congr 1
      ring
    rw [hdiff]
    apply add_le_add_left
    have h := sum_abs_free_cell_imbalance_le_original_add_crossings σ
      (fun i ↦ cell k (x i)) (fun j ↦ cell k (y j))
    have hS (c : C k) : partitionCount (cell k ∘ (x ∘ s)) c =
        ∑ i ∈ σ.freeRows, if cell k (x i) = c then (1 : ℝ) else 0 :=
      by simpa only [partitionCount, partitionIndicator, Function.comp_def, s] using
        sum_finsetIndex σ.freeRows (fun i ↦ if cell k (x i) = c then (1 : ℝ) else 0)
    have hT (c : C k) : partitionCount (cell k ∘ (y ∘ t)) c =
        ∑ j ∈ σ.freeCols, if cell k (y j) = c then (1 : ℝ) else 0 :=
      by simpa only [partitionCount, partitionIndicator, Function.comp_def, t] using
        sum_finsetIndex σ.freeCols (fun i ↦ if cell k (y i) = c then (1 : ℝ) else 0)
    simp_rw [hS, hT]
    simpa only [partitionCount, partitionIndicator, Function.comp_apply,
      retainedPartitionCrossings] using h

end OTSelector.Reconstruction
