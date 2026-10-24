import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSupportedProbeExtension

/-! Original supported probe gaps inherit the ambient readout limit exactly. -/
open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {M I : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Ambient continuous gap convergence gives the exact supported selector
readouts under any changing original feasible experiments and any index
filter. Support projection never has to be globally continuous. -/
theorem tendsto_originalAllocation_supported_probe_gap_of_continuous
    {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)] (l : Filter I)
    (n : I → ℕ) (R : ∀ i, Measure (Ω i))
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (ap am : ∀ i, Ω i → M → Fin (n i + 1) → ℝ)
    (Y : ∀ i, Ω i → Fin (n i + 1) → M) (p : ∀ i, Ω i → Fin (n i + 1) → ℝ)
    (hfp : ∀ i, ∀ᵐ w ∂R i, IsSemidiscreteAllocation (μ : Measure M) (p i w) (ap i w))
    (hfm : ∀ i, ∀ᵐ w ∂R i, IsSemidiscreteAllocation (μ : Measure M) (p i w) (am i w))
    (hY : ∀ i, ∀ᵐ w ∂R i, ∀ k, Y i w k ∈ K)
    (hgap : ∀ g : (M × M) →ᵇ ℝ,
      (∀ i, Integrable (fun w ↦
        |(∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
          ∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w|) (R i)) ∧
      Tendsto (fun i ↦ ∫ w,
        |(∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
          ∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w| ∂R i)
        l (𝓝 0) ∧
      Tendsto (fun i ↦ ∫⁻ w, ENNReal.ofReal
        |(∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
          ∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w| ∂R i)
        l (𝓝 0)) (f : (K × K) →ᵇ ℝ) :
    let supported := fun e : M × M ↦ f
      (supportProjection μ K hK.measurableSet hμ e.1,
        supportProjection ν K hK.measurableSet hν e.2)
    (∀ i, Integrable (fun w ↦
      |(∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
        ∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w|) (R i)) ∧
    Tendsto (fun i ↦ ∫ w,
      |(∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
        ∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w| ∂R i)
      l (𝓝 0) ∧
    Tendsto (fun i ↦ ∫⁻ w, ENNReal.ofReal
      |(∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
        ∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w| ∂R i)
      l (𝓝 0) := by
  intro supported
  obtain ⟨g, _, _, hg⟩ := exists_original_supported_probe_ambient_extension μ ν K hK hμ hν f
  let old := fun i w ↦
    |(∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
      ∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w|
  let new := fun i w ↦
    |(∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
      ∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w|
  have heq (i : I) : old i =ᵐ[R i] new i := by
    have hh := ae_originalAllocation_supported_probe_eq_ambient (R i) μ ν K hK hμ hν f g hg
      (ap i) (am i) (Y i) (p i) (hfp i) (hfm i) (hY i)
    filter_upwards [hh] with w hw
    change |(∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (ap i) (Y i) w) -
      ∫ e, supported e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) (am i) (Y i) w| = _
    rw [hw.1, hw.2]
  refine ⟨fun i ↦ (integrable_congr (heq i)).mpr ((hgap g).1 i), ?_, ?_⟩
  · have hf : (fun i ↦ ∫ w, old i w ∂R i) = (fun i ↦ ∫ w, new i w ∂R i) :=
      funext fun i ↦ integral_congr_ae (heq i)
    change Tendsto (fun i ↦ ∫ w, old i w ∂R i) l (𝓝 0)
    rw [hf]
    exact (hgap g).2.1
  · have hf : (fun i ↦ ∫⁻ w, ENNReal.ofReal (old i w) ∂R i) =
        (fun i ↦ ∫⁻ w, ENNReal.ofReal (new i w) ∂R i) := by
      funext i
      exact lintegral_congr_ae ((heq i).mono fun w hw ↦ congrArg ENNReal.ofReal hw)
    change Tendsto (fun i ↦ ∫⁻ w, ENNReal.ofReal (old i w) ∂R i) l (𝓝 0)
    rw [hf]
    exact (hgap g).2.2
end OTSelector.Reconstruction
