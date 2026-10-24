import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonPrefix
import OTSelector.Probability.MarkedBlockLaw

/-! Exact original count/sequence and finite-block law readouts for arbitrary spatial probabilities. -/
open Set Function MeasureTheory ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Regroup four independent original observations without changing any coordinate. -/
theorem originalShapeHolePoisson_shuffle
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] :
    MeasurePreserving (fun z : (A × B) × (C × D) ↦ ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      ((μ.prod ν).prod (ρ.prod σ)) ((μ.prod ρ).prod (ν.prod σ)) := by
  have h0 := measurePreserving_prodAssoc μ ν (ρ.prod σ)
  have h1 := (MeasurePreserving.id μ).prod ((measurePreserving_prodAssoc ν ρ σ).symm MeasurableEquiv.prodAssoc)
  have h2 := (MeasurePreserving.id μ).prod ((Measure.measurePreserving_swap (μ := ν) (ν := ρ)).prod (MeasurePreserving.id σ))
  have h3 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ρ ν σ)
  have h4 := (measurePreserving_prodAssoc μ ρ (ν.prod σ)).symm MeasurableEquiv.prodAssoc
  exact h4.comp (h3.comp (h2.comp (h1.comp h0)))

end OTSelector.Reconstruction
