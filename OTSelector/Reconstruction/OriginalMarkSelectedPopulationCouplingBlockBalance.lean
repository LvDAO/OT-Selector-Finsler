import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockSelection

/-! Actual per-block reserve deletion balances the two original color counts. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Counting original marks is monotone under true block inclusion. -/
theorem originalReserveBlockCount_mono (n : ℕ) (marks : ℕ → ℝ)
    {C S : Set ℝ} (hCS : C ⊆ S) :
    originalReserveBlockCount n marks C ≤ originalReserveBlockCount n marks S := by
  apply Finset.card_le_card
  intro i hi
  have h := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨h.1, hCS h.2⟩

/-- Each balanced-law block may have its own actual sample imbalance. Deleting
that block's actual signed excess from real extreme-class capacity balances
the actual counts in that block, without any assumption on other blocks. -/
theorem originalReserveBlockKept_actual_balance {q : ℕ}
    (K : Set (Fin q → ℝ)) (scene : LegalMarkedOptimalInputScene q)
    (source target : MarkedCloudSpace q ℝ)
    {S T Cs Ct : Set ℝ} (hCs : Cs ⊆ S) (hCt : Ct ⊆ T)
    (hs : originalReserveBlockExcess K 0 1 S T
        ((scene,target),source.1,fun i ↦ (source.2 i).2) ≤
      originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) Cs)
    (ht : originalReserveBlockExcess K 1 0 T S
        ((scene,source),target.1,fun i ↦ (target.2 i).2) ≤
      originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) Ct) :
    originalMainPhysicalBlockCount K S 0 scene +
        (originalReserveBlockKept K 0 1 S T Cs
          ((scene,target),source.1,fun i ↦ (source.2 i).2)).card =
      originalMainPhysicalBlockCount K T 1 scene +
        (originalReserveBlockKept K 1 0 T S Ct
          ((scene,source),target.1,fun i ↦ (target.2 i).2)).card := by
  rw [originalReserveBlockKept_card K 0 1 hCs _ hs,
    originalReserveBlockKept_card K 1 0 hCt _ ht]
  have hss := hs.trans (originalReserveBlockCount_mono source.1 (fun i ↦ (source.2 i).2) hCs)
  have htt := ht.trans (originalReserveBlockCount_mono target.1 (fun i ↦ (target.2 i).2) hCt)
  dsimp only [originalReserveBlockExcess] at *
  omega

/-- On an actual count fibre, no more than the originally observed reserve
count is retained. This controls all random-count population moments. -/
theorem originalReserveBlockKept_card_le_observed {q : ℕ}
    (K : Set (Fin q → ℝ)) (own other : Fin 2) (S T C : Set ℝ)
    (z : OriginalReserveSceneAux q) :
    (originalReserveBlockKept K own other S T C z).card ≤ z.2.1 := by
  have hsub : originalReserveBlockKept K own other S T C z ⊆ Finset.range z.2.1 := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1
  simpa only [Finset.card_range] using Finset.card_le_card hsub

end OTSelector.Reconstruction
