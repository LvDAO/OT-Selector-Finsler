import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedFamilyClockGrid

/-! Global original reserve RN families in the same actual full unit experiment. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal Classical
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

/-- The same actual full experiment carries one source RN family on its
literal global kept original labels, with the uniform full-grid energy budget. -/
theorem source_globalReserveAtomLaws (G : OriginalStageClockGrid)
    (h₀ : G.clockSlabSurplus α β 0 = 0) (hN : G.clockSlabSurplus α β G.count = 0)
    (hR : 0 < R) (hq : 4 < q) :
    let H := G.sourceReserveFineBlockPartition h₀ hN
    let f := originalReserveUnitSourceSamplerView q θ hθ1
    let J := (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
    (∀ᵐ p ∂J, H.AtomSpec b R 0 1 (f p)) ∧
      Integrable (H.atomEnergy b R 0 1 ∘ f) J ∧
      (∫ p, H.atomEnergy b R 0 1 (f p) ∂J) /
        volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
        (G.count : ℝ)*((q : ℝ)*dyadicMatchingConstant q*θ^(1-2/(q : ℝ))) := by
  let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1-θ))
    (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (markedPoissonLaw q ℝ β rate)
  have h := G.sourceReserveGlobalAtomLaws h₀ hN P b hR hθ.le hq
  have hp : MeasurePreserving (originalReserveUnitSourceSamplerView q θ hθ1)
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
      (P.prod (markedPoissonLaw q ℝ α rate)) :=
    ⟨measurable_originalReserveUnitSourceSamplerView q θ hθ1, X.fullLaw_source_sampler⟩
  refine ⟨hp.quasiMeasurePreserving.ae h.1, hp.integrable_comp_of_integrable h.2.1, ?_⟩
  exact (congrArg (fun t : ℝ ↦ t / volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
    (hp.hasLaw.integral_comp h.2.1.aestronglyMeasurable)).trans_le h.2.2

/-- The target family uses actual target Ioc blocks, source opposite blocks,
and the actual last target deletion classes in this same full experiment. -/
theorem target_globalReserveAtomLaws (G : OriginalStageClockGrid)
    (h₀ : G.clockSlabSurplus α β 0 = 0) (hN : G.clockSlabSurplus α β G.count = 0)
    (hR : 0 < R) (hq : 4 < q) :
    let H := G.targetReserveFineBlockPartition h₀ hN
    let f := originalReserveUnitTargetSamplerView q θ hθ1
    let J := (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
    (∀ᵐ p ∂J, H.AtomSpec b R 1 0 (f p)) ∧
      Integrable (H.atomEnergy b R 1 0 ∘ f) J ∧
      (∫ p, H.atomEnergy b R 1 0 (f p) ∂J) /
        volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
        (G.count : ℝ)*((q : ℝ)*dyadicMatchingConstant q*θ^(1-2/(q : ℝ))) := by
  let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1-θ))
    (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (markedPoissonLaw q ℝ α rate)
  have h := G.targetReserveGlobalAtomLaws h₀ hN P b hR hθ.le hq
  have hp : MeasurePreserving (originalReserveUnitTargetSamplerView q θ hθ1)
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
      (P.prod (markedPoissonLaw q ℝ β rate)) :=
    ⟨measurable_originalReserveUnitTargetSamplerView q θ hθ1, X.fullLaw_target_sampler⟩
  refine ⟨hp.quasiMeasurePreserving.ae h.1, hp.integrable_comp_of_integrable h.2.1, ?_⟩
  exact (congrArg (fun t : ℝ ↦ t / volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
    (hp.hasLaw.integral_comp h.2.1.aestronglyMeasurable)).trans_le h.2.2

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
