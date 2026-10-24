import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveUniformClockSlack
import OTSelector.Reconstruction.MarkedStationaryValueLegalReserveRemovalHall

/-!
# Original Poisson reserve observations supply the actual legal completion

The reserve observations retain their original indices inside the complete
finite problem.  Their uniform count event is used before, and remains valid
after, arbitrary choices of a legal core and its unmatched endpoints.
-/
open Set Function MeasureTheory
open scoped BigOperators Classical NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Embedding the unchanged original reserve observations into the complete
input preserves every literal clock-set count, including strict endpoints. -/
theorem card_filter_originalReserve_image
    (q : ℕ) {m : ℕ} (z : MarkedCloudSpace q ℝ) (e : Fin z.1 ↪ Fin m)
    (clock : Fin m → ℝ) (hclock : ∀ i, clock (e i) = (z.2 i).2) (U : Set ℝ) :
    ((Finset.univ.image e).filter (fun i ↦ clock i ∈ U)).card =
      originalReserveClockCount q U z := by
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ e.injective]
  unfold originalReserveClockCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hclock]

namespace PartialMatching

/-- A realized uniform reserve event and the actual post-selection removal
budget construct a full legal matching extending the original core. -/
theorem exists_originalReserve_clock_completion
    (q : ℕ) {m n : ℕ} (z : TwoMarkedCloudSpace q ℝ ℝ)
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (es : Fin z.1.1 ↪ Fin m) (et : Fin z.2.1 ↪ Fin n)
    (hes : ∀ i, source (es i) = (z.1.2 i).2)
    (het : ∀ j, target (et j) = (z.2.2 j).2)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (K : Set ℝ) (hK : ∀ i ∈ σ.freeRows, source i ∈ K)
    (r : ℝ≥0) (η : ℝ)
    (hgood : z ∈ originalReserveUniformClockSlackEvent q r η K)
    (hbudget : ((σ.freeRows \ Finset.univ.image es).card : ℝ) +
      ((Finset.univ.image et \ σ.freeCols).card : ℝ) ≤ (r : ℝ) * η / 2) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ τ.card = m ∧ σ.edges ⊆ τ.edges := by
  apply exists_legal_clock_completion_of_adaptive_reserve_slack source target σ hσ
    (Finset.univ.image es) (Finset.univ.image et) K hK ((r : ℝ) * η / 2) ?_ hbudget
  intro c hc
  have hs := card_filter_originalReserve_image q z.1 es source hes (Ici c)
  have ht := card_filter_originalReserve_image q z.2 et target het (Ioi c)
  simp only [mem_Ici] at hs
  simp only [mem_Ioi] at ht
  rw [hs, ht]
  exact hgood c hc

/-- The same realized input gives the exact legal residual capacity of the
original core, which is needed when evaluating the original legal objective. -/
theorem originalReserve_clock_capacity
    (q : ℕ) {m n : ℕ} (z : TwoMarkedCloudSpace q ℝ ℝ)
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (es : Fin z.1.1 ↪ Fin m) (et : Fin z.2.1 ↪ Fin n)
    (hes : ∀ i, source (es i) = (z.1.2 i).2)
    (het : ∀ j, target (et j) = (z.2.2 j).2)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (K : Set ℝ) (hK : ∀ i ∈ σ.freeRows, source i ∈ K)
    (r : ℝ≥0) (η : ℝ)
    (hgood : z ∈ originalReserveUniformClockSlackEvent q r η K)
    (hbudget : ((σ.freeRows \ Finset.univ.image es).card : ℝ) +
      ((Finset.univ.image et \ σ.freeCols).card : ℝ) ≤ (r : ℝ) * η / 2) :
    legalMaximumCard (scalarClockLegalGraph source target) = m ∧
      σ.card + legalMaximumCard (residualAllowed (scalarClockLegalGraph source target) σ) = m := by
  apply legal_capacity_of_reserve_slack source target σ hσ
    (Finset.univ.image es) (Finset.univ.image et) K hK ((r : ℝ) * η / 2) ?_ hbudget
  intro c hc
  have hs := card_filter_originalReserve_image q z.1 es source hes (Ici c)
  have ht := card_filter_originalReserve_image q z.2 et target het (Ioi c)
  simp only [mem_Ici] at hs
  simp only [mem_Ioi] at ht
  rw [hs, ht]
  exact hgood c hc

end PartialMatching
end OTSelector.Reconstruction
