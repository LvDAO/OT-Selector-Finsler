import OTSelector.Reconstruction.OriginalRootEnergyDensity

/-! Actual original allocation energy produces its own integrable root density.
The global energy bound is used once, with the original experiment unchanged. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- The actual original feasible allocation and its finite mean physical energy
produce a canonical root density. Both every root-set energy and the global
energy bound are retained, with no conditional or local balance hypothesis. -/
theorem exists_originalAllocation_rootEnergyDensity
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
      M → Fin (n + 1) → ℝ)
    (hmeas : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ allocation z.1 z.2 j))
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (allocation z))
    (label : M → Z) (hlabel : Measurable label)
    (energy : M × M → ℝ≥0∞) (henergy : Measurable energy)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫⁻ z, ∫⁻ p, energy (p.1, z.1 p.2)
      ∂semidiscreteAllocationMeasure μ (allocation z)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
        ENNReal.ofReal C) :
    ∃ f : Z → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
      Integrable f (μ.map label) ∧
      (∫ z, f z ∂μ.map label) ≤ C ∧
      ∀ K : Set Z, MeasurableSet K →
        (∫ z in K, f z ∂μ.map label) =
          (∫⁻ z, ∫⁻ p in (fun p : M × M ↦ label p.1) ⁻¹' K, energy p
            ∂physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) z
            ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))).toReal := by
  let Γ := originalGlobalAllocationMeanPlan μ ν n allocation
  have hmean : (∫⁻ p, energy p ∂Γ) ≤ ENNReal.ofReal C := by
    rw [lintegral_originalGlobalAllocationMeanPlan μ ν n allocation hmeas energy henergy]
    rw [lintegral_physicalSceneGlobalAllocationFamily_eq _ μ allocation
      (fun z ↦ z.1) (fun z ↦ z.2) hfeas (fun _ ↦ energy) (fun _ ↦ henergy)]
    exact hbound
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmean
  obtain ⟨hm, hn, hi, hsets, htotal⟩ := integrable_originalSourceRootEnergyDensity
    Γ μ (originalGlobalAllocationMeanPlan_source μ ν n allocation hmeas hfeas)
    label hlabel energy hfinite
  refine ⟨_, hm, hn, hi, htotal.le.trans
    (ENNReal.toReal_le_of_le_ofReal hC hmean), ?_⟩
  intro K hK
  rw [hsets K hK]
  congr 1
  let H := (fun p : M × M ↦ label p.1) ⁻¹' K
  have hH : MeasurableSet H := hK.preimage (hlabel.comp measurable_fst)
  have hread : Measurable (H.indicator energy) := henergy.indicator hH
  calc
    _ = ∫⁻ p, H.indicator energy p ∂Γ := (lintegral_indicator hH energy).symm
    _ = _ := lintegral_originalGlobalAllocationMeanPlan μ ν n allocation hmeas _ hread
    _ = _ := lintegral_congr (fun z ↦ lintegral_indicator hH energy)

end OTSelector.Reconstruction
