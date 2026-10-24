import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedPopulationAtoms

/-! The actual same full unit-input experiment carries the original source
and target fine-class RN families, with their full expected endpoint energies. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The same full experiment's true source sampler constructs actual original
fine-class laws with literal physical density and the Poisson energy rate. -/
theorem source_blockClassOrientedAtomLaws (hR : 0 < R) (hq : 4 < q)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    let f := originalReserveUnitSourceSamplerView q θ hθ1
    let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
    let E := originalReserveBlockClassOrientedAtomEnergy b R 0 1 S T C D ∘ f
    (∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      OriginalReserveBlockClassOrientedAtomSpec b R 0 1 S T C D (f p)) ∧
      Integrable E (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) ∧
      (∫ p, E p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))) ≤
        ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1-θ))
    (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (markedPoissonLaw q ℝ β rate)
  have h := originalReserveBlockClassOrientedAtomLaws P α rate b hR 0 1 hS hT hC hD hq
  have hp : MeasurePreserving (originalReserveUnitSourceSamplerView q θ hθ1)
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
      (P.prod (markedPoissonLaw q ℝ α rate)) :=
    ⟨measurable_originalReserveUnitSourceSamplerView q θ hθ1, X.fullLaw_source_sampler⟩
  exact ⟨hp.quasiMeasurePreserving.ae h.1, hp.integrable_comp_of_integrable h.2.1,
    (hp.hasLaw.integral_comp h.2.1.aestronglyMeasurable).trans_le h.2.2⟩

/-- The actual target uses the same full experiment and its genuine reordered
sampler, retaining the unchanged original target labels and the same frame. -/
theorem target_blockClassOrientedAtomLaws (hR : 0 < R) (hq : 4 < q)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    let f := originalReserveUnitTargetSamplerView q θ hθ1
    let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
    let E := originalReserveBlockClassOrientedAtomEnergy b R 1 0 S T C D ∘ f
    (∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      OriginalReserveBlockClassOrientedAtomSpec b R 1 0 S T C D (f p)) ∧
      Integrable E (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) ∧
      (∫ p, E p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))) ≤
        ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1-θ))
    (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (markedPoissonLaw q ℝ α rate)
  have h := originalReserveBlockClassOrientedAtomLaws P β rate b hR 1 0 hS hT hC hD hq
  have hp : MeasurePreserving (originalReserveUnitTargetSamplerView q θ hθ1)
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
      (P.prod (markedPoissonLaw q ℝ β rate)) :=
    ⟨measurable_originalReserveUnitTargetSamplerView q θ hθ1, X.fullLaw_target_sampler⟩
  exact ⟨hp.quasiMeasurePreserving.ae h.1, hp.integrable_comp_of_integrable h.2.1,
    (hp.hasLaw.integral_comp h.2.1.aestronglyMeasurable).trans_le h.2.2⟩

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
