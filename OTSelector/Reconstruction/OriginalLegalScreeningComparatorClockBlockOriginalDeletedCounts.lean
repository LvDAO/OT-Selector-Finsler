import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockOriginalDeletedCountsKept
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockOriginalDeletedCountsLabels

/-! Actual blockwise reserve deletion has the exact excess cardinality on unchanged FULL labels. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q m n : ℕ} {μ ν : Measure ℝ}

/-- Genuine sorted capacities and literal FULL main-plus-raw count identities give
the exact source/target excess deletions in every actual block. The original reserve
indices are mapped by their true embeddings; no desired deletion-cardinality is assumed. -/
theorem originalClockBlocks_mapped_global_deletion_cards
    (G : OriginalStageClockGrid)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (K : Set (Fin q → ℝ)) (scene : LegalMarkedOptimalInputScene q)
    (source target : MarkedCloudSpace q ℝ) (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ)
    (hCs : ∀ block, Cs block ⊆ G.sourceBlockCell μ ν block)
    (hCt : ∀ block, Ct block ⊆ G.targetBlockCell μ ν block)
    (hsCap : ∀ block, originalReserveBlockExcess K 0 1
      (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
      ((scene,target),source.1,fun i ↦ (source.2 i).2) ≤
        originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Cs block))
    (htCap : ∀ block, originalReserveBlockExcess K 1 0
      (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
      ((scene,source),target.1,fun i ↦ (target.2 i).2) ≤
        originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ct block))
    (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
    (hx : ∀ i, G.sourceLabel (x i).2 < G.count) (hy : ∀ j, G.targetLabel (y j).2 < G.count)
    (rs : Fin source.1 ↪ Fin m) (rt : Fin target.1 ↪ Fin n)
    (hxs : ∀ j, (x (rs j)).2 = (source.2 j).2) (hyt : ∀ j, (y (rt j)).2 = (target.2 j).2)
    (hfullS : ∀ block, (Finset.univ.filter (fun i ↦ (x i).2 ∈ G.sourceBlockCell μ ν block)).card =
      originalMainPhysicalBlockCount K (G.sourceBlockCell μ ν block) 0 scene +
        originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (G.sourceBlockCell μ ν block))
    (hfullT : ∀ block, (Finset.univ.filter (fun j ↦ (y j).2 ∈ G.targetBlockCell μ ν block)).card =
      originalMainPhysicalBlockCount K (G.targetBlockCell μ ν block) 1 scene +
        originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (G.targetBlockCell μ ν block)) :
    let c := fun i ↦ G.sourceBlockLabel h₀ hN (x i).2 (hx i)
    let d := fun j ↦ G.targetBlockLabel h₀ hN (y j).2 (hy j)
    let Ds := Finset.univ \ originalReserveBlocksKeptFin K 0 1 (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs
      ((scene,target),source.1,fun i ↦ (source.2 i).2)
    let Dt := Finset.univ \ originalReserveBlocksKeptFin K 1 0 (G.targetBlockCell μ ν) (G.sourceBlockCell μ ν) Ct
      ((scene,source),target.1,fun i ↦ (target.2 i).2)
    ∀ block : G.ClockSlabBlock μ ν,
      ((Ds.map rs).filter (fun i ↦ c i = block)).card =
        (Finset.univ.filter (fun i ↦ c i = block)).card - (Finset.univ.filter (fun j ↦ d j = block)).card ∧
      ((Dt.map rt).filter (fun j ↦ d j = block)).card =
        (Finset.univ.filter (fun j ↦ d j = block)).card - (Finset.univ.filter (fun i ↦ c i = block)).card := by
  classical
  dsimp only
  let c := fun i ↦ G.sourceBlockLabel h₀ hN (x i).2 (hx i)
  let d := fun j ↦ G.targetBlockLabel h₀ hN (y j).2 (hy j)
  let Ds := Finset.univ \ originalReserveBlocksKeptFin K 0 1 (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs
    ((scene,target),source.1,fun i ↦ (source.2 i).2)
  let Dt := Finset.univ \ originalReserveBlocksKeptFin K 1 0 (G.targetBlockCell μ ν) (G.sourceBlockCell μ ν) Ct
    ((scene,source),target.1,fun i ↦ (target.2 i).2)
  have hdis := G.blockCells_disjoint h₀ hN
  intro block
  have hS : (Finset.univ.filter (fun i ↦ c i = block)).card =
      originalMainPhysicalBlockCount K (G.sourceBlockCell μ ν block) 0 scene +
        originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (G.sourceBlockCell μ ν block) := by
    rw [G.sourceBlockLabel_filter_eq_clock_filter h₀ hN x hx]
    exact hfullS block
  have hT : (Finset.univ.filter (fun j ↦ d j = block)).card =
      originalMainPhysicalBlockCount K (G.targetBlockCell μ ν block) 1 scene +
        originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (G.targetBlockCell μ ν block) := by
    rw [G.targetBlockLabel_filter_eq_clock_filter h₀ hN y hy]
    exact hfullT block
  have hmapS : ((Ds.map rs).filter (fun i ↦ c i = block)).card =
      originalReserveBlockExcess K 0 1 (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((scene,target),source.1,fun i ↦ (source.2 i).2) := by
    have hc := originalEmbeddedDeletion_filter_card rs Ds c block
      (fun i : Fin source.1 ↦ (source.2 i).2 ∈ G.sourceBlockCell μ ν block) (fun i ↦ by
        change G.sourceBlockLabel h₀ hN (x (rs i)).2 (hx (rs i)) = block ↔ _
        rw [G.sourceBlockLabel_eq_iff_mem h₀ hN (x (rs i)).2 (hx (rs i)) block,hxs i])
    have hd := originalReserveBlocksDeletedFin_block_card K 0 1
      (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs hdis.1
      ((scene,target),source.1,fun i ↦ (source.2 i).2) block (hCs block) (hsCap block)
    convert hc.trans hd using 1
    congr 1
    ext i
    simp only [Finset.mem_filter]
  have hmapT : ((Dt.map rt).filter (fun j ↦ d j = block)).card =
      originalReserveBlockExcess K 1 0 (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((scene,source),target.1,fun i ↦ (target.2 i).2) := by
    have hc := originalEmbeddedDeletion_filter_card rt Dt d block
      (fun j : Fin target.1 ↦ (target.2 j).2 ∈ G.targetBlockCell μ ν block) (fun j ↦ by
        change G.targetBlockLabel h₀ hN (y (rt j)).2 (hy (rt j)) = block ↔ _
        rw [G.targetBlockLabel_eq_iff_mem h₀ hN (y (rt j)).2 (hy (rt j)) block,hyt j])
    have hd := originalReserveBlocksDeletedFin_block_card K 1 0
      (G.targetBlockCell μ ν) (G.sourceBlockCell μ ν) Ct hdis.2
      ((scene,source),target.1,fun i ↦ (target.2 i).2) block (hCt block) (htCap block)
    convert hc.trans hd using 1
    congr 1
    ext j
    simp only [Finset.mem_filter]
  exact ⟨hmapS.trans (by rw [hS,hT]; rfl),hmapT.trans (by rw [hT,hS]; rfl)⟩

end OTSelector.Reconstruction
