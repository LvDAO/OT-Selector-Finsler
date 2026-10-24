import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonMap
import OTSelector.Reconstruction.MarkedStationaryValueLegalCloud

/-! Exact mark pushforward for the original pressure at every real scale. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- The original Poisson experiment and its real-scale normalization commute
with the exact mark map; positions, counts and original marginal laws stay fixed. -/
theorem legalMarkedScalePressure_eq_pullback
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (γ : Measure C) [IsProbabilityMeasure γ] (δ : Measure D) [IsProbabilityMeasure δ]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hγ : α.map f = γ) (hδ : β.map g = δ)
    {sourceClock : C → ℝ} {targetClock : D → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (kin : C → D → (Fin q → ℝ) → ℝ)
    (hkin : Measurable (Function.uncurry (fun p : C × D ↦ kin p.1 p.2)))
    (probe : C → D → ℝ) (hp : Measurable (Function.uncurry probe)) (R t : ℝ) :
    legalMarkedScalePressure q sourceClock targetClock γ δ kin probe R t =
      legalMarkedScalePressure q (sourceClock ∘ f) (targetClock ∘ g) α β
        (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) R t := by
  by_cases hR : 0 < R
  · simp only [legalMarkedScalePressure,hR,ite_true]
    rw [legalMarkedPressure_eq_pullback q α β γ δ hf hg hγ hδ hs ht _ kin hkin probe hp t]
  · simp only [legalMarkedScalePressure,hR,ite_false]

end OTSelector.Reconstruction
