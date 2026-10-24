import OTSelector.Reconstruction.MarkedStationaryValueLegalHierarchy
import OTSelector.Reconstruction.MarkedStationaryValueLegalScalarRepair
import OTSelector.Finite.MaxCardValueRowStability

/-!
# Legal pressure stability under deletion of original vertices

Restrict the same original optimum, count its lost edges by the deleted vertex
sets, and repair its true legal cardinality deficit by short alternating chains.
Both signed comparisons are uniform in cloud size and use only a fixed class
count. No distribution is assigned to the adaptively retained endpoints.
-/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
namespace PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {J : Type*} [Fintype J]

/-- Delete vertices, keeping the exact induced legal graph on the old indices. -/
def vertexDeletedGraph (allowed : Finset (Fin m × Fin n))
    (S : Finset (Fin m)) (T : Finset (Fin n)) : Finset (Fin m × Fin n) := by
  classical
  exact allowed.filter fun p ↦ p.1 ∉ S ∧ p.2 ∉ T

theorem legalMaximumCard_mono {allowed small : Finset (Fin m × Fin n)}
    (h : small ⊆ allowed) : legalMaximumCard small ≤ legalMaximumCard allowed := by
  obtain ⟨σ, hσ, hcard⟩ := exists_legalMaximumCard small
  rw [← hcard]
  exact card_le_legalMaximumCard (h.trans' hσ)

theorem card_deleted_matching_edges_le (σ : OTSelector.PartialMatching m n)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    (σ.edges.filter fun p ↦ p.1 ∈ S ∨ p.2 ∈ T).card ≤ S.card + T.card := by
  classical
  have hc : (σ.edges.filter fun p ↦ p.2 ∈ T).card ≤ T.card := by
    have hsub : (σ.edges.filter fun p ↦ p.2 ∈ T).image Prod.snd ⊆ T := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hp).2
    have hinj : Set.InjOn (Prod.snd : Fin m × Fin n → Fin n)
        {p | p ∈ σ.edges.filter fun p ↦ p.2 ∈ T} := by
      intro p hp q hq hpq
      exact σ.col_inj p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hsub : (σ.edges.filter fun p ↦ p.1 ∈ S ∨ p.2 ∈ T) ⊆
      (σ.edges.filter fun p ↦ p.1 ∈ S) ∪ (σ.edges.filter fun p ↦ p.2 ∈ T) := by
    intro p hp
    obtain ⟨he, hs | ht⟩ := Finset.mem_filter.mp hp
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hs⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, ht⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (σ.card_filter_rows_le S) hc))

/-- Restrict the original matching; every lost edge touches a deleted vertex.
The remaining endpoints may be adaptive, and no probability law is assigned. -/
theorem exists_vertex_deleted_core
    (allowed : Finset (Fin m × Fin n)) (S : Finset (Fin m)) (T : Finset (Fin n))
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal allowed σ)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB : ∀ i j, |c i j| ≤ B) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal (vertexDeletedGraph allowed S T) τ ∧ τ.card ≤ σ.card ∧
      σ.card - τ.card ≤ S.card + T.card ∧
      τ.cost c ≤ σ.cost c + ((σ.card - τ.card : ℕ) : ℝ) * B := by
  classical
  let kept := σ.edges.filter fun p ↦ p.1 ∉ S ∧ p.2 ∉ T
  have hsub : kept ⊆ σ.edges := Finset.filter_subset _ _
  let τ := σ.subMatching kept hsub
  have hτ : IsLegal (vertexDeletedGraph allowed S T) τ := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hσ h.1, h.2⟩
  have hcard : τ.card ≤ σ.card := Finset.card_le_card hsub
  have hcomp : σ.edges \ kept = σ.edges.filter fun p ↦ p.1 ∈ S ∨ p.2 ∈ T := by
    ext p
    simp [kept]
    tauto
  have hcount : (σ.edges \ kept).card = σ.card - τ.card :=
    Finset.card_sdiff_of_subset hsub
  have hlost : σ.card - τ.card ≤ S.card + T.card := by
    rw [← hcount, hcomp]
    exact card_deleted_matching_edges_le σ S T
  refine ⟨τ, hτ, hcard, hlost, ?_⟩
  have hcost := Finset.sum_sdiff (f := fun p : Fin m × Fin n ↦ c p.1 p.2) hsub
  have hlow : -(((σ.edges \ kept).card : ℝ) * B) ≤
      ∑ p ∈ σ.edges \ kept, c p.1 p.2 := by
    calc
      _ = ∑ _p ∈ σ.edges \ kept, (-B) := by simp
      _ ≤ _ := Finset.sum_le_sum fun p _ ↦ (abs_le.mp (hB p.1 p.2)).1
  change (∑ p ∈ kept, c p.1 p.2) ≤ _
  change (∑ p ∈ σ.edges \ kept, c p.1 p.2) + (∑ p ∈ kept, c p.1 p.2) = σ.cost c at hcost
  rw [hcount] at hlow
  linarith

/-- Deleting original vertices reduces the legal rank by at most their count. -/
theorem legalMaximumCard_vertexDeletedGraph_defect_le
    (allowed : Finset (Fin m × Fin n)) (S : Finset (Fin m)) (T : Finset (Fin n)) :
    legalMaximumCard allowed - legalMaximumCard (vertexDeletedGraph allowed S T) ≤
      S.card + T.card := by
  obtain ⟨σ, hσ, hcard⟩ := exists_legalMaximumCard allowed
  obtain ⟨τ, hτ, _, hmiss, _⟩ := exists_vertex_deleted_core allowed S T σ hσ
    (fun _ _ ↦ 0) (B := 0) (by simp)
  have ht := card_le_legalMaximumCard hτ
  omega

/-- Fixed finite source classes give a vertex-count stability bound for the
literal signed legal minimum, including both directions of the comparison. -/
theorem abs_legalMaximumValue_vertexDeletedGraph_sub_le
    (allowed : Finset (Fin m × Fin n)) (S : Finset (Fin m)) (T : Finset (Fin n))
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    |legalMaximumValue (vertexDeletedGraph allowed S T) c - legalMaximumValue allowed c| ≤
      ((S.card + T.card : ℕ) : ℝ) * (2 * (Fintype.card (Option J) : ℝ) * B) := by
  classical
  let small := vertexDeletedGraph allowed S T
  let K : ℝ := 2 * (Fintype.card (Option J) : ℝ) * B
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hsub : small ⊆ allowed := Finset.filter_subset _ _
  have hrank : legalMaximumCard small ≤ legalMaximumCard allowed := legalMaximumCard_mono hsub
  have hdef := legalMaximumCard_vertexDeletedGraph_defect_le allowed S T
  have hbig : legalMaximumValue allowed c ≤ legalMaximumValue small c +
      ((S.card + T.card : ℕ) : ℝ) * K := by
    obtain ⟨σ, hσ, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue small c
    have hv := legalMaximumValue_le_cost_add_class_deficit σ (hsub.trans' hσ)
      sourceClass sourceAllows hallowed c hB0 hB
    rw [hcard, hcost] at hv
    refine hv.trans (add_le_add le_rfl ?_)
    calc
      _ ≤ ((legalMaximumCard allowed - legalMaximumCard small : ℕ) : ℝ) * K := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        simp only [K, Fintype.card_option, Nat.cast_add, Nat.cast_one]
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hdef) hK
  have hsmall : legalMaximumValue small c ≤ legalMaximumValue allowed c +
      ((S.card + T.card : ℕ) : ℝ) * K := by
    obtain ⟨σ, hσ, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed c
    obtain ⟨τ, hτ, hτcard, hlost, hτcost⟩ := exists_vertex_deleted_core allowed S T σ hσ c hB
    have hsmallgraph : small = spatialLegalBlock allowed
        (fun i ↦ decide (i ∉ S)) (fun j ↦ decide (j ∉ T)) true := by
      ext p
      simp [small, vertexDeletedGraph, spatialLegalBlock]
    obtain ⟨label, allows, hclasses⟩ := spatialLegalBlock_exists_classes allowed
      (fun i ↦ decide (i ∉ S)) (fun j ↦ decide (j ∉ T)) true sourceClass sourceAllows hallowed
    rw [← hsmallgraph] at hclasses
    have hv := legalMaximumValue_le_cost_add_class_deficit τ hτ label allows hclasses c hB0 hB
    have hdef' : legalMaximumCard small - τ.card ≤ σ.card - τ.card := Nat.sub_le_sub_right
      (by omega : legalMaximumCard small ≤ σ.card) _
    have hA : 0 ≤ (2 * (Fintype.card (Option J) : ℝ) - 1) * B := by
      apply mul_nonneg _ hB0
      have hc : (0 : ℝ) ≤ (Fintype.card J : ℝ) := Nat.cast_nonneg _
      simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]
      linarith
    have hmul := mul_le_mul_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hdef') hA
    have hlostR : ((σ.card - τ.card : ℕ) : ℝ) ≤ ((S.card + T.card : ℕ) : ℝ) :=
      (Nat.cast_le (α := ℝ)).mpr hlost
    have hlast := mul_le_mul_of_nonneg_right hlostR hK
    rw [hcost] at hτcost
    dsimp only [K] at hlast
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The deletion estimate only needs cost bounds on the original legal graph. -/
theorem abs_legalMaximumValue_vertexDeletedGraph_sub_le_of_allowed
    (allowed : Finset (Fin m × Fin n)) (S : Finset (Fin m)) (T : Finset (Fin n))
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, (i, j) ∈ allowed → |c i j| ≤ B) :
    |legalMaximumValue (vertexDeletedGraph allowed S T) c - legalMaximumValue allowed c| ≤
      ((S.card + T.card : ℕ) : ℝ) * (2 * (Fintype.card (Option J) : ℝ) * B) := by
  have hc : legalMaximumValue (vertexDeletedGraph allowed S T) (allowedMaskedCost allowed c) =
      legalMaximumValue (vertexDeletedGraph allowed S T) c := by
    apply legalMaximumValue_congr_on_allowed
    intro i j hij
    have he := (Finset.mem_filter.mp hij).1
    simp only [allowedMaskedCost, he, ite_true]
  simpa only [hc, legalMaximumValue_allowedMaskedCost] using
    abs_legalMaximumValue_vertexDeletedGraph_sub_le allowed S T sourceClass sourceAllows
      hallowed (allowedMaskedCost allowed c) hB0 (abs_allowedMaskedCost_le allowed c hB0 hB)

end PartialMatching

/-- Original compact scalar bins produce every graph-class datum in the
vertex deletion estimate, without a separate neighborhood assumption. -/
theorem FiniteScalarBins.abs_legalMaximumValue_vertexDeletedGraph_sub_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ)
    (hsource : ∀ i, source i ∈ I) (hsep : ∀ i j, gap ≤ |target j - source i|)
    (S : Finset (Fin m)) (T : Finset (Fin n))
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, (i, j) ∈ scalarClockLegalGraph source target → |c i j| ≤ B) :
    |PartialMatching.legalMaximumValue
        (PartialMatching.vertexDeletedGraph (scalarClockLegalGraph source target) S T) c -
      PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c| ≤
      ((S.card + T.card : ℕ) : ℝ) * (2 * ((D.count : ℝ) + 1) * B) := by
  obtain ⟨label, allows, hallowed⟩ := D.exists_source_neighborhood_classes hgap source target
    hsource hsep
  simpa only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    PartialMatching.abs_legalMaximumValue_vertexDeletedGraph_sub_le_of_allowed
      (scalarClockLegalGraph source target) S T label allows hallowed c hB0 hB

end OTSelector.Reconstruction
