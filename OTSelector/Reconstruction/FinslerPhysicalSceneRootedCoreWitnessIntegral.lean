import OTSelector.Reconstruction.FinslerPhysicalSceneRootedAveragePacking

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- Abstract double-integral algebra keeps original actual-plan expressions
opaque when separating their measurable discarded-mass term. -/
theorem physicalScene_lintegral_lintegral_add_of_measurable_right
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (ρ : Measure Z) [SFinite ρ]
    (F G : Ω → Z → ℝ≥0∞) (hG : Measurable (fun v : Ω × Z ↦ G v.1 v.2)) :
    (∫⁻ w, ∫⁻ z, F w z + G w z ∂ρ ∂P) =
      (∫⁻ w, ∫⁻ z, F w z ∂ρ ∂P) + ∫⁻ w, ∫⁻ z, G w z ∂ρ ∂P := by
  calc
    _ = ∫⁻ w, (∫⁻ z, F w z ∂ρ) + ∫⁻ z, G w z ∂ρ ∂P := by
      apply lintegral_congr
      intro w
      exact lintegral_add_right _ (hG.comp (measurable_const.prodMk measurable_id))
    _ = _ := lintegral_add_right _ hG.lintegral_prod_right'

/-- A root screen preserves a pointwise discarded-mass bound, with the same
original discarded mass and both original integrals. -/
theorem physicalScene_lintegral_screened_le_of_pointwise_loss
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (ρ : Measure Z) [SFinite ρ]
    (full good loss : Ω → Z → ℝ≥0∞)
    (hLoss : Measurable (fun v : Ω × Z ↦ loss v.1 v.2))
    (hpoint : ∀ w z, full w z ≤ good w z + loss w z) (E : Set Z) :
    (∫⁻ w, ∫⁻ z, E.indicator (full w) z ∂ρ ∂P) ≤
      (∫⁻ w, ∫⁻ z, E.indicator (good w) z ∂ρ ∂P) + ∫⁻ w, ∫⁻ z, loss w z ∂ρ ∂P := by
  calc
    _ ≤ ∫⁻ w, ∫⁻ z, E.indicator (good w) z + loss w z ∂ρ ∂P := by
      apply lintegral_mono
      intro w
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ E
      · simpa only [indicator_of_mem hz] using hpoint w z
      · simp only [indicator_of_notMem hz, zero_add]
        exact bot_le
    _ = _ := physicalScene_lintegral_lintegral_add_of_measurable_right P ρ
      (fun w z ↦ E.indicator (good w) z) loss hLoss

end OTSelector.Reconstruction
