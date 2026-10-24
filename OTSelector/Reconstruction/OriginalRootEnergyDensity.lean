import OTSelector.Reconstruction.OriginalGlobalAllocationMeanPlan
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The actual source-root energy measure has a canonical integrable density.
The density retains the original full plan and its exact total energy. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- Physical energy of the unchanged plan, assigned to its original source root. -/
def originalSourceRootEnergyMeasure (Γ : Measure (M × M)) (a : M → Z)
    (energy : M × M → ℝ≥0∞) : Measure Z :=
  (Γ.withDensity energy).map (fun p ↦ a p.1)

/-- The energy on each root set is exactly the original physical plan's energy
on the corresponding source set. -/
theorem originalSourceRootEnergyMeasure_apply
    (Γ : Measure (M × M)) (a : M → Z) (ha : Measurable a)
    (energy : M × M → ℝ≥0∞) {K : Set Z} (hK : MeasurableSet K) :
    originalSourceRootEnergyMeasure Γ a energy K =
      ∫⁻ p in (fun p : M × M ↦ a p.1) ⁻¹' K, energy p ∂Γ := by
  rw [originalSourceRootEnergyMeasure,
    Measure.map_apply (show Measurable (fun p : M × M ↦ a p.1) from
      ha.comp measurable_fst) hK]
  exact withDensity_apply energy (hK.preimage (show Measurable
    (fun p : M × M ↦ a p.1) from ha.comp measurable_fst))

/-- No original source-null root set carries energy. This uses the exact full
source marginal, irrespective of conditional density zeros or retained columns. -/
theorem originalSourceRootEnergyMeasure_absolutelyContinuous
    (Γ : Measure (M × M)) (μ : Measure M) (hsource : Γ.map Prod.fst = μ)
    (a : M → Z) (ha : Measurable a) (energy : M × M → ℝ≥0∞) :
    originalSourceRootEnergyMeasure Γ a energy ≪ μ.map a := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro K hK hnull
  rw [Measure.map_apply ha hK] at hnull
  rw [originalSourceRootEnergyMeasure,
    Measure.map_apply (show Measurable (fun p : M × M ↦ a p.1) from
      ha.comp measurable_fst) hK]
  apply withDensity_absolutelyContinuous Γ energy
  change Γ (Prod.fst ⁻¹' (a ⁻¹' K)) = 0
  rw [← Measure.map_apply measurable_fst (hK.preimage ha), hsource]
  exact hnull

/-- The original root energy measure retains the entire original physical energy. -/
theorem originalSourceRootEnergyMeasure_univ
    (Γ : Measure (M × M)) (a : M → Z) (ha : Measurable a)
    (energy : M × M → ℝ≥0∞) :
    originalSourceRootEnergyMeasure Γ a energy univ = ∫⁻ p, energy p ∂Γ := by
  rw [originalSourceRootEnergyMeasure_apply Γ a ha energy MeasurableSet.univ,
    preimage_univ, Measure.restrict_univ]

/-- Finite original energy produces its own canonical integrable root density,
with exact integrals on every measurable root set and exact total energy. -/
theorem integrable_originalSourceRootEnergyDensity
    (Γ : Measure (M × M)) (μ : Measure M) [IsFiniteMeasure μ]
    (hsource : Γ.map Prod.fst = μ)
    (a : M → Z) (ha : Measurable a) (energy : M × M → ℝ≥0∞)
    (hfinite : (∫⁻ p, energy p ∂Γ) ≠ ⊤) :
    let rootLaw := μ.map a
    let E := originalSourceRootEnergyMeasure Γ a energy
    let f := fun z ↦ (E.rnDeriv rootLaw z).toReal
    Measurable f ∧ (∀ z, 0 ≤ f z) ∧ Integrable f rootLaw ∧
      (∀ K : Set Z, MeasurableSet K →
        (∫ z in K, f z ∂rootLaw) = (∫⁻ p in (fun p : M × M ↦ a p.1) ⁻¹' K,
          energy p ∂Γ).toReal) ∧
      (∫ z, f z ∂rootLaw) = (∫⁻ p, energy p ∂Γ).toReal := by
  let E := originalSourceRootEnergyMeasure Γ a energy
  have hE : E univ ≠ ⊤ := by
    rw [originalSourceRootEnergyMeasure_univ Γ a ha energy]
    exact hfinite
  let _ : IsFiniteMeasure E := ⟨hE.lt_top⟩
  have hAC : E ≪ μ.map a :=
    originalSourceRootEnergyMeasure_absolutelyContinuous Γ μ hsource a ha energy
  refine ⟨(Measure.measurable_rnDeriv E (μ.map a)).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ.map a) hE)
  · intro K hK
    rw [Measure.setIntegral_toReal_rnDeriv hAC K]
    exact congrArg ENNReal.toReal (originalSourceRootEnergyMeasure_apply Γ a ha energy hK)
  · rw [Measure.integral_toReal_rnDeriv hAC]
    exact congrArg ENNReal.toReal (originalSourceRootEnergyMeasure_univ Γ a ha energy)

end OTSelector.Reconstruction
