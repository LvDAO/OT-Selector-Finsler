import OTSelector.Finite.MatchingEmbedding
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialDefect
import OTSelector.Reconstruction.MarkedStationaryValueLegalScalarRepair

/-!
# Legal values on actual finite subclouds

Embedding or enumerating a spatial subcloud preserves its legal maximum rank
and signed minimum exactly. The statements also cover an empty color cloud.
-/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {a b m n : ℕ}

/-- The literal allowed graph on two embedded finite subclouds. -/
def inducedLegalGraph (allowed : Finset (Fin m × Fin n))
    (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n) : Finset (Fin a × Fin b) := by
  classical
  exact Finset.univ.filter fun p ↦ (e p.1, f p.2) ∈ allowed

theorem isLegal_mapEmbedding (allowed : Finset (Fin m × Fin n))
    (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n) (σ : OTSelector.PartialMatching a b)
    (hσ : IsLegal (inducedLegalGraph allowed e f) σ) :
    IsLegal allowed (σ.mapEmbedding e f) := by
  intro p hp
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  exact (Finset.mem_filter.mp (hσ hu)).2

theorem isLegal_comapEmbedding (allowed : Finset (Fin m × Fin n))
    (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n) (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) :
    IsLegal (inducedLegalGraph allowed e f) (σ.comapEmbedding e f) := by
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ (Finset.mem_filter.mp hp).2⟩

/-- Enumerating all active rows and columns preserves the actual legal rank. -/
theorem legalMaximumCard_inducedLegalGraph
    (allowed : Finset (Fin m × Fin n)) (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (hcarry : ∀ p ∈ allowed, p.1 ∈ range e ∧ p.2 ∈ range f) :
    legalMaximumCard (inducedLegalGraph allowed e f) = legalMaximumCard allowed := by
  apply le_antisymm
  · obtain ⟨σ, hσ, hcard⟩ := exists_legalMaximumCard (inducedLegalGraph allowed e f)
    rw [← hcard, ← OTSelector.PartialMatching.card_mapEmbedding e f σ]
    exact card_le_legalMaximumCard (isLegal_mapEmbedding allowed e f σ hσ)
  · obtain ⟨σ, hσ, hcard⟩ := exists_legalMaximumCard allowed
    rw [← hcard, ← OTSelector.PartialMatching.card_comapEmbedding e f σ
      (fun p hp ↦ hcarry p (hσ hp))]
    exact card_le_legalMaximumCard (isLegal_comapEmbedding allowed e f σ hσ)

/-- The exact signed legal minimum is invariant under subcloud enumeration. -/
theorem legalMaximumValue_inducedLegalGraph
    (allowed : Finset (Fin m × Fin n)) (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (hcarry : ∀ p ∈ allowed, p.1 ∈ range e ∧ p.2 ∈ range f)
    (c : Fin m → Fin n → ℝ) :
    legalMaximumValue (inducedLegalGraph allowed e f) (fun i j ↦ c (e i) (f j)) =
      legalMaximumValue allowed c := by
  have hrank := legalMaximumCard_inducedLegalGraph allowed e f hcarry
  apply le_antisymm
  · obtain ⟨σ, hσ, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed c
    have hσcarry := fun p hp ↦ hcarry p (hσ hp)
    have hcard' : (σ.comapEmbedding e f).card =
        legalMaximumCard (inducedLegalGraph allowed e f) := by
      rw [OTSelector.PartialMatching.card_comapEmbedding e f σ hσcarry, hcard, hrank]
    refine (legalMaximumValue_le _ (isLegal_comapEmbedding allowed e f σ hσ) hcard').trans_eq ?_
    rw [OTSelector.PartialMatching.cost_comapEmbedding e f σ hσcarry, hcost]
  · obtain ⟨σ, hσ, hcard, hcost⟩ :=
      exists_cost_eq_legalMaximumValue (inducedLegalGraph allowed e f) (fun i j ↦ c (e i) (f j))
    have hcard' : (σ.mapEmbedding e f).card = legalMaximumCard allowed := by
      rw [OTSelector.PartialMatching.card_mapEmbedding, hcard, hrank]
    refine (legalMaximumValue_le c (isLegal_mapEmbedding allowed e f σ hσ) hcard').trans_eq ?_
    rw [OTSelector.PartialMatching.cost_mapEmbedding, hcost]

/-- Inducing a strict clock-order graph is exactly the strict clock-order
graph of the actual finite subcloud observations. -/
theorem inducedLegalGraph_scalarClockLegalGraph
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n) :
    inducedLegalGraph (scalarClockLegalGraph source target) e f =
      scalarClockLegalGraph (source ∘ e) (target ∘ f) := by
  classical
  ext p
  simp [inducedLegalGraph, scalarClockLegalGraph]

section Spatial

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The canonical finite source-block enumeration is an embedding. -/
def spatialSourceEmbedding (s : Fin m → β) (b : β) :
    Fin (OTSelector.blockSizeS s b) ↪ Fin m :=
  ⟨OTSelector.blockEmbeddingS s b, OTSelector.blockEmbeddingS_injective s b⟩

/-- The canonical finite target-block enumeration is an embedding. -/
def spatialTargetEmbedding (t : Fin n → β) (b : β) :
    Fin (OTSelector.blockSizeT t b) ↪ Fin n :=
  ⟨OTSelector.blockEmbeddingT t b, OTSelector.blockEmbeddingT_injective t b⟩

theorem mem_range_spatialSourceEmbedding (s : Fin m → β) (b : β) (i : Fin m)
    (hi : s i = b) : i ∈ range (spatialSourceEmbedding s b) := by
  classical
  let x : OTSelector.blockFinset s b := ⟨i, OTSelector.mem_blockFinset.mpr hi⟩
  exact ⟨Finset.equivFin (OTSelector.blockFinset s b) x,
    by simp [spatialSourceEmbedding, OTSelector.blockEmbeddingS, x]⟩

theorem mem_range_spatialTargetEmbedding (t : Fin n → β) (b : β) (j : Fin n)
    (hj : t j = b) : j ∈ range (spatialTargetEmbedding t b) := by
  classical
  let x : OTSelector.blockFinset t b := ⟨j, OTSelector.mem_blockFinset.mpr hj⟩
  exact ⟨Finset.equivFin (OTSelector.blockFinset t b) x,
    by simp [spatialTargetEmbedding, OTSelector.blockEmbeddingT, x]⟩

theorem inducedLegalGraph_spatialLegalBlock
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β) (b : β) :
    inducedLegalGraph (spatialLegalBlock allowed s t b)
      (spatialSourceEmbedding s b) (spatialTargetEmbedding t b) =
      inducedLegalGraph allowed (spatialSourceEmbedding s b) (spatialTargetEmbedding t b) := by
  classical
  ext p
  have hs := OTSelector.mem_blockFinset.mp (OTSelector.blockEmbeddingS_mem s b p.1)
  have ht := OTSelector.mem_blockFinset.mp (OTSelector.blockEmbeddingT_mem t b p.2)
  simp only [inducedLegalGraph, Finset.mem_filter, Finset.mem_univ, true_and,
    spatialLegalBlock, spatialSourceEmbedding, spatialTargetEmbedding, Function.Embedding.coeFn_mk,
    hs, ht, and_true]

/-- The ambient child graph has exactly the rank of the actual enumerated
finite subcloud graph. -/
theorem legalMaximumCard_spatialLegalBlock_eq
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β) (b : β) :
    legalMaximumCard (spatialLegalBlock allowed s t b) =
      legalMaximumCard (inducedLegalGraph allowed
        (spatialSourceEmbedding s b) (spatialTargetEmbedding t b)) := by
  have hcarry : ∀ p ∈ spatialLegalBlock allowed s t b,
      p.1 ∈ range (spatialSourceEmbedding s b) ∧
      p.2 ∈ range (spatialTargetEmbedding t b) := by
    intro p hp
    exact ⟨mem_range_spatialSourceEmbedding s b p.1 (Finset.mem_filter.mp hp).2.1,
      mem_range_spatialTargetEmbedding t b p.2 (Finset.mem_filter.mp hp).2.2⟩
  rw [← legalMaximumCard_inducedLegalGraph _ _ _ hcarry, inducedLegalGraph_spatialLegalBlock]

theorem legalMaximumValue_spatialLegalBlock_eq
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β) (b : β)
    (c : Fin m → Fin n → ℝ) :
    legalMaximumValue (spatialLegalBlock allowed s t b) c =
      legalMaximumValue (inducedLegalGraph allowed
        (spatialSourceEmbedding s b) (spatialTargetEmbedding t b))
        (fun i j ↦ c (spatialSourceEmbedding s b i) (spatialTargetEmbedding t b j)) := by
  have hcarry : ∀ p ∈ spatialLegalBlock allowed s t b,
      p.1 ∈ range (spatialSourceEmbedding s b) ∧
      p.2 ∈ range (spatialTargetEmbedding t b) := by
    intro p hp
    exact ⟨mem_range_spatialSourceEmbedding s b p.1 (Finset.mem_filter.mp hp).2.1,
      mem_range_spatialTargetEmbedding t b p.2 (Finset.mem_filter.mp hp).2.2⟩
  rw [← legalMaximumValue_inducedLegalGraph _ _ _ hcarry c, inducedLegalGraph_spatialLegalBlock]

/-- The spatial-block deficiency in the hierarchy is literally the source
count minus the legal rank on the enumerated clock subcloud. -/
theorem scalarClockSourceDefect_spatialLegalBlock_eq
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (s : Fin m → β) (t : Fin n → β) (b : β) :
    (OTSelector.blockFinset s b).card - legalMaximumCard
      (spatialLegalBlock (scalarClockLegalGraph source target) s t b) =
    OTSelector.blockSizeS s b - legalMaximumCard
      (scalarClockLegalGraph (source ∘ spatialSourceEmbedding s b)
        (target ∘ spatialTargetEmbedding t b)) := by
  rw [legalMaximumCard_spatialLegalBlock_eq, inducedLegalGraph_scalarClockLegalGraph]
  rfl

theorem scalarClockValue_spatialLegalBlock_eq
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (s : Fin m → β) (t : Fin n → β) (b : β) (c : Fin m → Fin n → ℝ) :
    legalMaximumValue (spatialLegalBlock (scalarClockLegalGraph source target) s t b) c =
      legalMaximumValue
        (scalarClockLegalGraph (source ∘ spatialSourceEmbedding s b)
          (target ∘ spatialTargetEmbedding t b))
        (fun i j ↦ c (spatialSourceEmbedding s b i) (spatialTargetEmbedding t b j)) := by
  rw [legalMaximumValue_spatialLegalBlock_eq, inducedLegalGraph_scalarClockLegalGraph]

end Spatial
end OTSelector.Reconstruction.PartialMatching
