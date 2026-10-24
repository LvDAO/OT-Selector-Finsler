import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockKeptUnion
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockBalance

/-! Global original kept sets inherit actual per-block balance and support. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {B : Type*} [Fintype B]

/-- Every kept original mark belongs to its actual repaired block. -/
theorem originalReserveBlocksKeptFin_mark_mem_union (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (z : OriginalReserveSceneAux q) (i : Fin z.2.1)
    (hi : i ∈ originalReserveBlocksKeptFin K own other S T C z) : z.2.2 i ∈ ⋃ b, S b := by
  have hmem := (Finset.mem_filter.mp hi).2
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hmem
  exact mem_iUnion.mpr ⟨b,(Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2⟩

/-- In one whole clock block, the global Fin kept set has exactly the
actual block deletion's count on the unchanged original indices. -/
theorem originalReserveBlocksKeptFin_block_count (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (hdis : Pairwise (Disjoint on S))
    (z : OriginalReserveSceneAux q) (positions : ℕ → Fin q → ℝ) (b : B) :
    originalStageRemainingReserveClassCount ⟨z.2.1,fun i ↦ (positions i,z.2.2 i)⟩
      (originalReserveBlocksKeptFin K own other S T C z) (S b) =
      (originalReserveBlockKept K own other (S b) (T b) (C b) z).card := by
  rw [originalReserveBlocksKeptFin_class_count K own other S T C hdis z positions b (Subset.rfl)]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2

/-- Real extreme-class capacities in each actual block give simultaneous
balance for one global original kept set. The counts are literal main-scene
and original reserve counts, rather than a desired gamma endpoint premise. -/
theorem originalReserveBlocksKeptFin_actual_balance
    (K : Set (Fin q → ℝ)) (scene : LegalMarkedOptimalInputScene q)
    (source target : MarkedCloudSpace q ℝ)
    (S T Cs Ct : B → Set ℝ)
    (hS : Pairwise (Disjoint on S)) (hT : Pairwise (Disjoint on T))
    (hCs : ∀ b, Cs b ⊆ S b) (hCt : ∀ b, Ct b ⊆ T b)
    (hs : ∀ b, originalReserveBlockExcess K 0 1 (S b) (T b)
        ((scene,target),source.1,fun i ↦ (source.2 i).2) ≤
      originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Cs b))
    (ht : ∀ b, originalReserveBlockExcess K 1 0 (T b) (S b)
        ((scene,source),target.1,fun i ↦ (target.2 i).2) ≤
      originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ct b)) :
    ∀ b, originalMainPhysicalBlockCount K (S b) 0 scene +
        originalStageRemainingReserveClassCount source
          (originalReserveBlocksKeptFin K 0 1 S T Cs
            ((scene,target),source.1,fun i ↦ (source.2 i).2)) (S b) =
      originalMainPhysicalBlockCount K (T b) 1 scene +
        originalStageRemainingReserveClassCount target
          (originalReserveBlocksKeptFin K 1 0 T S Ct
            ((scene,source),target.1,fun i ↦ (target.2 i).2)) (T b) := by
  intro b
  have hsc := originalReserveBlocksKeptFin_block_count K 0 1 S T Cs hS
    ((scene,target),source.1,fun i ↦ (source.2 i).2) (fun i ↦ (source.2 i).1) b
  have htc := originalReserveBlocksKeptFin_block_count K 1 0 T S Ct hT
    ((scene,source),target.1,fun i ↦ (target.2 i).2) (fun i ↦ (target.2 i).1) b
  change originalStageRemainingReserveClassCount source
    (originalReserveBlocksKeptFin K 0 1 S T Cs
      ((scene,target),source.1,fun i ↦ (source.2 i).2)) (S b) = _ at hsc
  change originalStageRemainingReserveClassCount target
    (originalReserveBlocksKeptFin K 1 0 T S Ct
      ((scene,source),target.1,fun i ↦ (target.2 i).2)) (T b) = _ at htc
  rw [hsc,htc]
  exact originalReserveBlockKept_actual_balance K scene source target (hCs b) (hCt b) (hs b) (ht b)

end OTSelector.Reconstruction
