import OTSelector.Reconstruction.MarkedStationaryValueLegalEmbedding
import OTSelector.Reconstruction.MarkedStationaryValueLegalDeletion

/-! Exact count continuity for actual embedded finite legal subclouds. -/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {a b m n : ℕ} {J : Type*} [Fintype J]

/-- Arbitrary embedded finite subclouds have the expected vertex-count
stability bound; no padded dummy vertices or altered costs are introduced. -/
theorem abs_legalMaximumValue_inducedLegalGraph_sub_le
    (allowed : Finset (Fin m × Fin n)) (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, (i, j) ∈ allowed → |c i j| ≤ B) :
    |legalMaximumValue (inducedLegalGraph allowed e f) (fun i j ↦ c (e i) (f j)) -
      legalMaximumValue allowed c| ≤
      (((m - a) + (n - b) : ℕ) : ℝ) * (2 * (Fintype.card (Option J) : ℝ) * B) := by
  classical
  let S : Finset (Fin m) := Finset.univ \ Finset.univ.image e
  let T : Finset (Fin n) := Finset.univ \ Finset.univ.image f
  let small := vertexDeletedGraph allowed S T
  have hS : S.card = m - a := by
    simp [S, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_image_of_injective _ e.injective]
  have hT : T.card = n - b := by
    simp [T, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_image_of_injective _ f.injective]
  have hcarry : ∀ p ∈ small, p.1 ∈ range e ∧ p.2 ∈ range f := by
    intro p hp
    obtain ⟨_, hs, ht⟩ := Finset.mem_filter.mp hp
    simpa only [S, T, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not,
      Finset.mem_image, exists_prop_of_true, Set.mem_range] using And.intro hs ht
  have hgraph : inducedLegalGraph small e f = inducedLegalGraph allowed e f := by
    ext p
    simp [inducedLegalGraph, small, vertexDeletedGraph, S, T]
  have hvalue : legalMaximumValue small c =
      legalMaximumValue (inducedLegalGraph allowed e f) (fun i j ↦ c (e i) (f j)) := by
    rw [← legalMaximumValue_inducedLegalGraph small e f hcarry c, hgraph]
  have hv := abs_legalMaximumValue_vertexDeletedGraph_sub_le_of_allowed allowed S T
    sourceClass sourceAllows hallowed c hB0 hB
  simpa only [← hvalue, hS, hT] using hv

end PartialMatching

theorem FiniteScalarBins.abs_legalMaximumValue_subcloud_sub_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    {a b m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ)
    (hsource : ∀ i, source i ∈ I) (hsep : ∀ i j, gap ≤ |target j - source i|)
    (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, (i, j) ∈ scalarClockLegalGraph source target → |c i j| ≤ B) :
    |PartialMatching.legalMaximumValue (scalarClockLegalGraph (source ∘ e) (target ∘ f))
        (fun i j ↦ c (e i) (f j)) -
      PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c| ≤
      (((m - a) + (n - b) : ℕ) : ℝ) * (2 * ((D.count : ℝ) + 1) * B) := by
  obtain ⟨label, allows, hallowed⟩ := D.exists_source_neighborhood_classes hgap source target
    hsource hsep
  simpa only [PartialMatching.inducedLegalGraph_scalarClockLegalGraph, Fintype.card_option,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    PartialMatching.abs_legalMaximumValue_inducedLegalGraph_sub_le
      (scalarClockLegalGraph source target) e f label allows hallowed c hB0 hB

end OTSelector.Reconstruction
