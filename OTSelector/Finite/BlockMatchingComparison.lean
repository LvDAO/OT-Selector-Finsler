import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import OTSelector.Finite.PartialMatching


/-!
## Lemma skeleton

* **Conditions:** N is any natural number, including zero; source and target both have index type Fin N. The block-label type beta is finite and has decidable equality; blockS and blockT are arbitrary label maps. Cost c is an arbitrary real matrix for decomposition identities. cost_residualEdges_le assumes only c(i,j) <= B. The final maxCardValue_blockMatching_le additionally assumes c >= 0.
* **Objects:** blockFinset: fiber of a finite block-label map; blockMatchSize: min(source block size, target block size); sourceBlockSubset,targetBlockSubset: chosen subsets of their original block fibers, both of cardinality blockMatchSize; residualSource,residualTarget: complements of the selected within-block endpoints; their cardinalities agree; blockEquiv,residualEquiv: finite-set bijections used to select actual edges; blockMatching: full cardinality N matching assembled from within-block edges and residual edges; B: a pointwise real upper bound on residual edge costs
* **Proof detail:** Partition each cloud by label, choose equally many source and target endpoints in each block, and prove all chosen blocks disjoint. Use finite cardinality equality to construct a bijection in each selected block and a bijection of the remaining endpoints. Combine the disjoint graphs, prove row/column injectivity by membership in unique block fibers or their complements, and count the edges. Split the finite cost sum over the disjoint block and residual graphs; bound every residual summand by B and compare the full matching with the infimum.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean
* Sheldon Axler, *Supplement for Measure, Integration & Real Analysis*, Section C, Definitions 0.32 and 0.35, pp. 18–19.
  https://measure.axler.net/SupplementMIRA.pdf#page=18

**Relationship to the sources:** The block and residual construction uses explicit bijections in complete bipartite rectangles, not Hall’s theorem for a legal-edge graph. Finite cost bounds and the final infimum comparison are locally derived.
-/

/-!
# One-sided block comparison for maximum-cardinality matchings

Split the source and target index sets into common blocks.  Match each block
internally as far as its two counts allow, then pair the residual source points
with the residual target points arbitrarily across blocks.  When the total
source and target counts agree, the resulting matching has maximum cardinality,
and its cost is at most the sum of the block optima plus one uniform edge bound
times the total count discrepancy.

This is the deterministic core of the finite-volume matching pressure: the
count discrepancy of independent Poisson inputs has expectation of order the
square root of the number of points, while the edge bound is the squared block
diameter.
-/

open scoped BigOperators

namespace OTSelector

variable {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

/-- The source indices in one block. -/
def blockFinset (block : Fin N → β) (b : β) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ block i = b

@[simp] theorem mem_blockFinset {block : Fin N → β} {b : β} {i : Fin N} :
    i ∈ blockFinset block b ↔ block i = b := by
  simp [blockFinset]

theorem blockFinset_pairwiseDisjoint (block : Fin N → β) :
    Set.PairwiseDisjoint ((Finset.univ : Finset β) : Set β) (blockFinset block) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [mem_blockFinset] at hi hj
  exact hab (hi.symm.trans hj)

theorem biUnion_blockFinset (block : Fin N → β) :
    (Finset.univ.biUnion (blockFinset block)) = Finset.univ := by
  ext i
  simp [blockFinset]

theorem sum_card_blockFinset (block : Fin N → β) :
    ∑ b, (blockFinset block b).card = N := by
  rw [← Finset.card_biUnion (blockFinset_pairwiseDisjoint block), biUnion_blockFinset]
  simp [Finset.card_univ, Fintype.card_fin]

/-! ## The block selection and the constructed matching -/

variable (blockS blockT : Fin N → β) (c : Fin N → Fin N → ℝ)

/-- The block size on the source side. -/
def blockSizeS (b : β) : ℕ := (blockFinset blockS b).card

/-- The block size on the target side. -/
def blockSizeT (b : β) : ℕ := (blockFinset blockT b).card

/-- The matched cardinality inside one block. -/
def blockMatchSize (b : β) : ℕ := min (blockSizeS blockS b) (blockSizeT blockT b)

/-- A chosen subset of each source block of the maximum possible cardinality. -/
noncomputable def sourceBlockSubset (b : β) : Finset (Fin N) :=
  (Finset.exists_subset_card_eq
    (min_le_left (blockSizeS blockS b) (blockSizeT blockT b))).choose

theorem sourceBlockSubset_subset (b : β) :
    sourceBlockSubset blockS blockT b ⊆ blockFinset blockS b :=
  (Finset.exists_subset_card_eq
    (min_le_left (blockSizeS blockS b) (blockSizeT blockT b))).choose_spec.1

theorem sourceBlockSubset_card (b : β) :
    (sourceBlockSubset blockS blockT b).card = blockMatchSize blockS blockT b :=
  (Finset.exists_subset_card_eq
    (min_le_left (blockSizeS blockS b) (blockSizeT blockT b))).choose_spec.2

/-- A chosen subset of each target block of the maximum possible cardinality. -/
noncomputable def targetBlockSubset (b : β) : Finset (Fin N) :=
  (Finset.exists_subset_card_eq
    (min_le_right (blockSizeS blockS b) (blockSizeT blockT b))).choose

theorem targetBlockSubset_subset (b : β) :
    targetBlockSubset blockS blockT b ⊆ blockFinset blockT b :=
  (Finset.exists_subset_card_eq
    (min_le_right (blockSizeS blockS b) (blockSizeT blockT b))).choose_spec.1

theorem targetBlockSubset_card (b : β) :
    (targetBlockSubset blockS blockT b).card = blockMatchSize blockS blockT b :=
  (Finset.exists_subset_card_eq
    (min_le_right (blockSizeS blockS b) (blockSizeT blockT b))).choose_spec.2

/-- The residual source indices after all block matchings. -/
noncomputable def residualSource : Finset (Fin N) :=
  Finset.univ \ Finset.univ.biUnion (sourceBlockSubset blockS blockT)

/-- The residual target indices after all block matchings. -/
noncomputable def residualTarget : Finset (Fin N) :=
  Finset.univ \ Finset.univ.biUnion (targetBlockSubset blockS blockT)

theorem sourceBlockSubset_pairwiseDisjoint :
    Set.PairwiseDisjoint ((Finset.univ : Finset β) : Set β)
      (sourceBlockSubset blockS blockT) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hia : i ∈ blockFinset blockS a := sourceBlockSubset_subset blockS blockT a hi
  have hib : i ∈ blockFinset blockS b := sourceBlockSubset_subset blockS blockT b hj
  simp only [mem_blockFinset] at hia hib
  exact hab (hia.symm.trans hib)

theorem targetBlockSubset_pairwiseDisjoint :
    Set.PairwiseDisjoint ((Finset.univ : Finset β) : Set β)
      (targetBlockSubset blockS blockT) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hia : i ∈ blockFinset blockT a := targetBlockSubset_subset blockS blockT a hi
  have hib : i ∈ blockFinset blockT b := targetBlockSubset_subset blockS blockT b hj
  simp only [mem_blockFinset] at hia hib
  exact hab (hia.symm.trans hib)

theorem card_biUnion_sourceBlockSubset :
    (Finset.univ.biUnion (sourceBlockSubset blockS blockT)).card =
      ∑ b, blockMatchSize blockS blockT b := by
  rw [Finset.card_biUnion (sourceBlockSubset_pairwiseDisjoint blockS blockT)]
  simp [sourceBlockSubset_card]

theorem card_biUnion_targetBlockSubset :
    (Finset.univ.biUnion (targetBlockSubset blockS blockT)).card =
      ∑ b, blockMatchSize blockS blockT b := by
  rw [Finset.card_biUnion (targetBlockSubset_pairwiseDisjoint blockS blockT)]
  simp [targetBlockSubset_card]

theorem sum_blockMatchSize_le (block : Fin N → β) :
    (∑ b, blockMatchSize block block b) ≤ N := by
  calc
    ∑ b, blockMatchSize block block b ≤ ∑ b, blockSizeS block b :=
      Finset.sum_le_sum fun b _ ↦ min_le_left _ _
    _ = N := sum_card_blockFinset block

theorem card_residualSource :
    (residualSource blockS blockT).card =
      N - ∑ b, blockMatchSize blockS blockT b := by
  rw [residualSource, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, card_biUnion_sourceBlockSubset]

theorem card_residualTarget :
    (residualTarget blockS blockT).card =
      N - ∑ b, blockMatchSize blockS blockT b := by
  rw [residualTarget, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, card_biUnion_targetBlockSubset]

theorem card_residualSource_eq_residualTarget :
    (residualSource blockS blockT).card = (residualTarget blockS blockT).card := by
  rw [card_residualSource, card_residualTarget]

/-- A chosen bijection between the residual source and target indices. -/
noncomputable def residualEquiv :
    ↥(residualSource blockS blockT) ≃ ↥(residualTarget blockS blockT) :=
  (Finset.equivFinOfCardEq (card_residualSource_eq_residualTarget blockS blockT)).trans
    (Finset.equivFin (residualTarget blockS blockT)).symm

/-- A chosen bijection inside one block between the selected source and target subsets. -/
noncomputable def blockEquiv (b : β) :
    ↥(sourceBlockSubset blockS blockT b) ≃ ↥(targetBlockSubset blockS blockT b) :=
  (Finset.equivFinOfCardEq (by
    rw [sourceBlockSubset_card, targetBlockSubset_card])).trans
    (Finset.equivFin (targetBlockSubset blockS blockT b)).symm

/-- The edges inside one block. -/
noncomputable def blockEdges (b : β) : Finset (Fin N × Fin N) :=
  (sourceBlockSubset blockS blockT b).attach.image fun x ↦
    (x.1, (blockEquiv blockS blockT b x).1)

/-- The repair edges between residual indices. -/
noncomputable def residualEdges : Finset (Fin N × Fin N) :=
  (residualSource blockS blockT).attach.image fun x ↦
    (x.1, (residualEquiv blockS blockT x).1)

/-- All edges of the constructed maximum-cardinality matching. -/
noncomputable def blockMatchingEdges : Finset (Fin N × Fin N) :=
  Finset.univ.biUnion (blockEdges blockS blockT) ∪ residualEdges blockS blockT


/-! ## Membership and uniqueness of the constructed edges -/

theorem mem_blockEdges {b : β} {i j : Fin N} :
    (i, j) ∈ blockEdges blockS blockT b ↔
      ∃ h : i ∈ sourceBlockSubset blockS blockT b,
        (blockEquiv blockS blockT b ⟨i, h⟩).1 = j := by
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
    have hxi : x.1 = i := congrArg Prod.fst hx
    have hxj : (blockEquiv blockS blockT b x).1 = j := congrArg Prod.snd hx
    have hsub : (⟨i, hxi ▸ x.2⟩ : ↥(sourceBlockSubset blockS blockT b)) = x :=
      Subtype.ext hxi.symm
    refine ⟨hxi ▸ x.2, ?_⟩
    rw [hsub]
    exact hxj
  · rintro ⟨h, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨i, h⟩, Finset.mem_attach _ _, rfl⟩

theorem fst_mem_blockEdges {b : β} {e : Fin N × Fin N}
    (he : e ∈ blockEdges blockS blockT b) :
    e.1 ∈ sourceBlockSubset blockS blockT b := by
  obtain ⟨h, _⟩ := (mem_blockEdges blockS blockT).mp he
  exact h

theorem snd_mem_blockEdges {b : β} {e : Fin N × Fin N}
    (he : e ∈ blockEdges blockS blockT b) :
    e.2 ∈ targetBlockSubset blockS blockT b := by
  obtain ⟨h, hj⟩ := (mem_blockEdges blockS blockT).mp he
  rw [← hj]
  exact (blockEquiv blockS blockT b ⟨e.1, h⟩).2

theorem mem_residualEdges {i j : Fin N} :
    (i, j) ∈ residualEdges blockS blockT ↔
      ∃ h : i ∈ residualSource blockS blockT,
        (residualEquiv blockS blockT ⟨i, h⟩).1 = j := by
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
    have hxi : x.1 = i := congrArg Prod.fst hx
    have hxj : (residualEquiv blockS blockT x).1 = j := congrArg Prod.snd hx
    have hsub : (⟨i, hxi ▸ x.2⟩ : ↥(residualSource blockS blockT)) = x :=
      Subtype.ext hxi.symm
    refine ⟨hxi ▸ x.2, ?_⟩
    rw [hsub]
    exact hxj
  · rintro ⟨h, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨i, h⟩, Finset.mem_attach _ _, rfl⟩

theorem fst_mem_residualEdges {e : Fin N × Fin N}
    (he : e ∈ residualEdges blockS blockT) :
    e.1 ∈ residualSource blockS blockT := by
  obtain ⟨h, _⟩ := (mem_residualEdges blockS blockT).mp he
  exact h

theorem snd_mem_residualEdges {e : Fin N × Fin N}
    (he : e ∈ residualEdges blockS blockT) :
    e.2 ∈ residualTarget blockS blockT := by
  obtain ⟨h, hj⟩ := (mem_residualEdges blockS blockT).mp he
  rw [← hj]
  exact (residualEquiv blockS blockT ⟨e.1, h⟩).2

theorem blockEdges_pairwiseDisjoint :
    Set.PairwiseDisjoint ((Finset.univ : Finset β) : Set β)
      (blockEdges blockS blockT) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro e ha hb
  have h1 : e.1 ∈ sourceBlockSubset blockS blockT a := fst_mem_blockEdges blockS blockT ha
  have h2 : e.1 ∈ sourceBlockSubset blockS blockT b := fst_mem_blockEdges blockS blockT hb
  have h1' := sourceBlockSubset_subset blockS blockT a h1
  have h2' := sourceBlockSubset_subset blockS blockT b h2
  simp only [mem_blockFinset] at h1' h2'
  exact hab (h1'.symm.trans h2')

theorem biUnion_blockEdges_disjoint_residualEdges :
    Disjoint (Finset.univ.biUnion (blockEdges blockS blockT))
      (residualEdges blockS blockT) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  have hb : e ∈ Finset.univ.biUnion (blockEdges blockS blockT) := he
  obtain ⟨b, _, hb'⟩ := Finset.mem_biUnion.mp hb
  have hrow : e.1 ∈ sourceBlockSubset blockS blockT b := fst_mem_blockEdges blockS blockT hb'
  have hres : e.1 ∈ residualSource blockS blockT := fst_mem_residualEdges blockS blockT he'
  simp only [residualSource, Finset.mem_sdiff, Finset.mem_univ, true_and] at hres
  exact hres (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hrow⟩)

theorem blockMatchingEdges_row_inj :
    ∀ e ∈ blockMatchingEdges blockS blockT,
      ∀ e' ∈ blockMatchingEdges blockS blockT, e.1 = e'.1 → e = e' := by
  intro e he e' he' hrow
  rw [blockMatchingEdges, Finset.mem_union] at he he'
  rcases he with he | he <;> rcases he' with he' | he'
  · obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp he
    obtain ⟨b', _, hb'⟩ := Finset.mem_biUnion.mp he'
    by_cases hbb : b = b'
    · subst hbb
      obtain ⟨h1, hj1⟩ := (mem_blockEdges blockS blockT).mp hb
      obtain ⟨h2, hj2⟩ := (mem_blockEdges blockS blockT).mp hb'
      have hsub : (⟨e.1, h1⟩ : ↥(sourceBlockSubset blockS blockT b)) = ⟨e'.1, h2⟩ :=
        Subtype.ext hrow
      have h2eq : e.2 = e'.2 := by
        rw [← hj1, ← hj2, hsub]
      exact Prod.ext hrow h2eq
    · have h1 : e.1 ∈ blockFinset blockS b :=
        sourceBlockSubset_subset blockS blockT b (fst_mem_blockEdges blockS blockT hb)
      have h2 : e'.1 ∈ blockFinset blockS b' :=
        sourceBlockSubset_subset blockS blockT b' (fst_mem_blockEdges blockS blockT hb')
      simp only [mem_blockFinset] at h1 h2
      exact absurd (h1.symm.trans ((congrArg blockS hrow).trans h2)) hbb
  · exact absurd hrow (by
      have h1 : e.1 ∈ sourceBlockSubset blockS blockT
          (Finset.mem_biUnion.mp he).choose :=
        fst_mem_blockEdges blockS blockT (Finset.mem_biUnion.mp he).choose_spec.2
      have hres := fst_mem_residualEdges blockS blockT he'
      simp only [residualSource, Finset.mem_sdiff, Finset.mem_univ, true_and] at hres
      intro h
      exact hres (h ▸ Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, h1⟩))
  · exact absurd hrow.symm (by
      have h1 : e'.1 ∈ sourceBlockSubset blockS blockT
          (Finset.mem_biUnion.mp he').choose :=
        fst_mem_blockEdges blockS blockT (Finset.mem_biUnion.mp he').choose_spec.2
      have hres := fst_mem_residualEdges blockS blockT he
      simp only [residualSource, Finset.mem_sdiff, Finset.mem_univ, true_and] at hres
      intro h
      exact hres (h ▸ Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, h1⟩))
  · obtain ⟨h1, hj1⟩ := (mem_residualEdges blockS blockT).mp he
    obtain ⟨h2, hj2⟩ := (mem_residualEdges blockS blockT).mp he'
    have hsub : (⟨e.1, h1⟩ : ↥(residualSource blockS blockT)) = ⟨e'.1, h2⟩ :=
      Subtype.ext hrow
    have h2eq : e.2 = e'.2 := by
      rw [← hj1, ← hj2, hsub]
    exact Prod.ext hrow h2eq

theorem blockMatchingEdges_col_inj :
    ∀ e ∈ blockMatchingEdges blockS blockT,
      ∀ e' ∈ blockMatchingEdges blockS blockT, e.2 = e'.2 → e = e' := by
  intro e he e' he' hcol
  rw [blockMatchingEdges, Finset.mem_union] at he he'
  rcases he with he | he <;> rcases he' with he' | he'
  · obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp he
    obtain ⟨b', _, hb'⟩ := Finset.mem_biUnion.mp he'
    by_cases hbb : b = b'
    · subst hbb
      obtain ⟨h1, hj1⟩ := (mem_blockEdges blockS blockT).mp hb
      obtain ⟨h2, hj2⟩ := (mem_blockEdges blockS blockT).mp hb'
      have hy : (blockEquiv blockS blockT b ⟨e.1, h1⟩) =
          (blockEquiv blockS blockT b ⟨e'.1, h2⟩) := by
        apply Subtype.ext
        rw [hj1, hj2, hcol]
      have hsub := (blockEquiv blockS blockT b).injective hy
      have hrow : e.1 = e'.1 := congrArg Subtype.val hsub
      exact Prod.ext hrow hcol
    · have h1 : e.2 ∈ blockFinset blockT b :=
        targetBlockSubset_subset blockS blockT b (snd_mem_blockEdges blockS blockT hb)
      have h2 : e'.2 ∈ blockFinset blockT b' :=
        targetBlockSubset_subset blockS blockT b' (snd_mem_blockEdges blockS blockT hb')
      simp only [mem_blockFinset] at h1 h2
      exact absurd (h1.symm.trans ((congrArg blockT hcol).trans h2)) hbb
  · exact absurd hcol (by
      have h1 : e.2 ∈ targetBlockSubset blockS blockT
          (Finset.mem_biUnion.mp he).choose :=
        snd_mem_blockEdges blockS blockT (Finset.mem_biUnion.mp he).choose_spec.2
      have hres := snd_mem_residualEdges blockS blockT he'
      simp only [residualTarget, Finset.mem_sdiff, Finset.mem_univ, true_and] at hres
      intro h
      exact hres (h ▸ Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, h1⟩))
  · exact absurd hcol.symm (by
      have h1 : e'.2 ∈ targetBlockSubset blockS blockT
          (Finset.mem_biUnion.mp he').choose :=
        snd_mem_blockEdges blockS blockT (Finset.mem_biUnion.mp he').choose_spec.2
      have hres := snd_mem_residualEdges blockS blockT he
      simp only [residualTarget, Finset.mem_sdiff, Finset.mem_univ, true_and] at hres
      intro h
      exact hres (h ▸ Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, h1⟩))
  · obtain ⟨h1, hj1⟩ := (mem_residualEdges blockS blockT).mp he
    obtain ⟨h2, hj2⟩ := (mem_residualEdges blockS blockT).mp he'
    have hy : (residualEquiv blockS blockT ⟨e.1, h1⟩) =
        (residualEquiv blockS blockT ⟨e'.1, h2⟩) := by
      apply Subtype.ext
      rw [hj1, hj2, hcol]
    have hsub := (residualEquiv blockS blockT).injective hy
    have hrow : e.1 = e'.1 := congrArg Subtype.val hsub
    exact Prod.ext hrow hcol

/-- The constructed edges form a genuine partial matching. -/
noncomputable def blockMatching : PartialMatching N N where
  edges := blockMatchingEdges blockS blockT
  row_inj := blockMatchingEdges_row_inj blockS blockT
  col_inj := blockMatchingEdges_col_inj blockS blockT

/-! ## Cardinality and cost of the constructed matching -/

theorem card_blockEdges (b : β) :
    (blockEdges blockS blockT b).card = blockMatchSize blockS blockT b := by
  unfold blockEdges
  rw [Finset.card_image_of_injOn]
  · simp [sourceBlockSubset_card]
  · intro x _ y _ h
    exact Subtype.ext (congrArg Prod.fst h)

theorem card_biUnion_blockEdges :
    (Finset.univ.biUnion (blockEdges blockS blockT)).card =
      ∑ b, blockMatchSize blockS blockT b := by
  rw [Finset.card_biUnion (blockEdges_pairwiseDisjoint blockS blockT)]
  simp [card_blockEdges]

theorem card_residualEdges :
    (residualEdges blockS blockT).card = (residualSource blockS blockT).card := by
  unfold residualEdges
  rw [Finset.card_image_of_injOn]
  · simp
  · intro x _ y _ h
    exact Subtype.ext (congrArg Prod.fst h)

theorem sum_blockMatchSize_le_N :
    (∑ b, blockMatchSize blockS blockT b) ≤ N := by
  calc
    (∑ b, blockMatchSize blockS blockT b) ≤ ∑ b, blockSizeS blockS b :=
      Finset.sum_le_sum fun b _ ↦ min_le_left _ _
    _ = N := sum_card_blockFinset blockS

theorem card_blockMatchingEdges :
    (blockMatchingEdges blockS blockT).card = N := by
  rw [blockMatchingEdges,
    Finset.card_union_of_disjoint (biUnion_blockEdges_disjoint_residualEdges blockS blockT),
    card_biUnion_blockEdges, card_residualEdges, card_residualSource]
  have h := sum_blockMatchSize_le_N blockS blockT
  omega

/-- Total cost of a finite set of edges. -/
def edgeCost (c : Fin N → Fin N → ℝ) (e : Finset (Fin N × Fin N)) : ℝ :=
  ∑ p ∈ e, c p.1 p.2

theorem cost_blockMatchingEdges :
    edgeCost c (blockMatchingEdges blockS blockT) =
      (∑ b, edgeCost c (blockEdges blockS blockT b)) +
        edgeCost c (residualEdges blockS blockT) := by
  unfold edgeCost blockMatchingEdges
  rw [Finset.sum_union (biUnion_blockEdges_disjoint_residualEdges blockS blockT),
    Finset.sum_biUnion (blockEdges_pairwiseDisjoint blockS blockT)]

theorem cost_residualEdges_le {B : ℝ} (hB : ∀ i j, c i j ≤ B) :
    edgeCost c (residualEdges blockS blockT) ≤
      B * (residualSource blockS blockT).card := by
  unfold edgeCost residualEdges
  calc
    (∑ e ∈ (residualSource blockS blockT).attach.image
        (fun x ↦ (x.1, (residualEquiv blockS blockT x).1)),
          c e.1 e.2) ≤
        ∑ _e ∈ (residualSource blockS blockT).attach.image
          (fun x ↦ (x.1, (residualEquiv blockS blockT x).1)), B :=
      Finset.sum_le_sum fun e _ ↦ hB e.1 e.2
    _ = (((residualSource blockS blockT).attach.image
          (fun x ↦ (x.1, (residualEquiv blockS blockT x).1))).card : ℝ) * B := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (residualEdges blockS blockT).card * B := by
      congr 1
    _ = (residualSource blockS blockT).card * B := by rw [card_residualEdges]
    _ = B * (residualSource blockS blockT).card := by ring

/-- The global maximum-cardinality value is at most the sum of the chosen block
pairing costs plus a uniform edge bound times the residual count. -/
theorem maxCardValue_blockMatching_le {B : ℝ}
    (hB : ∀ i j, c i j ≤ B) (hnonneg : ∀ i j, 0 ≤ c i j) :
    PartialMatching.maxCardValue c ≤
      (∑ b, edgeCost c (blockEdges blockS blockT b)) +
        B * (residualSource blockS blockT).card := by
  have hcard : (blockMatching blockS blockT).card = min N N := by
    simp only [blockMatching, PartialMatching.card, card_blockMatchingEdges, min_self]
  have hmax := PartialMatching.maxCardValue_le c hcard hnonneg
  have hcost : (blockMatching blockS blockT).cost c ≤
      (∑ b, edgeCost c (blockEdges blockS blockT b)) +
        B * (residualSource blockS blockT).card := by
    have heq : (blockMatching blockS blockT).cost c =
        edgeCost c (blockMatchingEdges blockS blockT) := rfl
    rw [heq, cost_blockMatchingEdges]
    have := cost_residualEdges_le blockS blockT c hB
    linarith
  linarith
end OTSelector
