import OTSelector.Geometry.FinslerDistanceLocalizationCore
import OTSelector.Reconstruction.FiniteCoefficientCoreMass
import OTSelector.Transport.Coupling.OptimalPlanExistence

/-!
# Original physical mass outside the geometric localization cores

The same coefficient-window loss bounds the original scalar marginal tails.
Disintegration transfers these estimates to the physical cores without changing
root weights or normalizing either original population.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Function OTSelector.Geometry
open scoped ENNReal
namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)

omit [BorelSpace E] in
/-- Conditional scalar tails bound the omitted original physical mass with the
same original root weights. -/
theorem physical_core_complement_le_of_conditional_loss
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (η : Measure M) [IsFiniteMeasure η]
    (hlabel : η.map a = lambda) (hregular : ∀ᵐ x ∂η, x ∈ F.potentialRegularDomain u)
    (hloss : ∀ᵐ z ∂lambda, ∀ i : Fin D.haar.continuous.count,
      z ∈ (D.haar.continuous.coefficient i).roots →
      condDistrib u a η z
        (Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))ᶜ ≤ δ) :
    η (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i)ᶜ ≤
      lambda (⋃ i, (D.haar.continuous.coefficient i).roots)ᶜ +
        δ * lambda (⋃ i, (D.haar.continuous.coefficient i).roots) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  have _instFinite : IsFiniteMeasure lambda := hlabel ▸ inferInstance
  let K := ⋃ i : Fin D.haar.continuous.count, D.corePointDomain i
  have hK : MeasurableSet K := MeasurableSet.iUnion
    (fun i ↦ (D.isCompact_corePointDomain i).measurableSet)
  have hset : (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i)ᶜ =ᵐ[η]
      (fun x ↦ (a x, u x)) ⁻¹' Kᶜ := by
    filter_upwards [hregular] with x hx
    change (x ∈ (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i)ᶜ) =
      (x ∈ (fun y ↦ (a y, u y)) ⁻¹' Kᶜ)
    simp only [mem_compl_iff, mem_iUnion, mem_preimage, physicalCoreDomain,
      mem_ofPred_eq, hx, true_and, K]
  rw [measure_congr hset, ← Measure.map_apply (ha.prodMk hu.continuous.measurable) hK.compl,
    ← compProd_map_condDistrib hu.continuous.measurable.aemeasurable, hlabel]
  exact compProd_compl_iUnion_prod_le lambda (condDistrib u a η)
    (fun i ↦ (D.haar.continuous.coefficient i).roots)
    (fun i ↦ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
      ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))
    (fun i ↦ (D.haar.continuous.coefficient i).roots_compact.measurableSet)
    (fun _ ↦ measurableSet_Icc) hloss

omit [BorelSpace E] in
/-- Any actual ordered conditional coupling controls both original physical
marginal losses on the same geometric core. Only its existence is used. -/
theorem physical_core_complements_le_of_legal_couplings
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (hlabel₀ : η₀.map a = lambda) (hlabel₁ : η₁.map a = lambda)
    (hregular₀ : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hregular₁ : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (hlegal : ∀ᵐ z ∂lambda, ∃ plan : Measure (ℝ × ℝ),
      Vlasov.IsCoupling plan (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
        ∀ᵐ p ∂plan, p.1 ≤ p.2) :
    η₀ (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i)ᶜ ≤
      lambda (⋃ i, (D.haar.continuous.coefficient i).roots)ᶜ +
        δ * lambda (⋃ i, (D.haar.continuous.coefficient i).roots) ∧
    η₁ (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i)ᶜ ≤
      lambda (⋃ i, (D.haar.continuous.coefficient i).roots)ᶜ +
        δ * lambda (⋃ i, (D.haar.continuous.coefficient i).roots) := by
  have htail : ∀ᵐ z ∂lambda, ∀ i : Fin D.haar.continuous.count,
      z ∈ (D.haar.continuous.coefficient i).roots →
      condDistrib u a η₀ z
        (Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))ᶜ ≤ δ ∧
      condDistrib u a η₁ z
        (Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))ᶜ ≤ δ := by
    filter_upwards [hlegal] with z hz
    obtain ⟨plan, hplan, ho⟩ := hz
    intro i hi
    have hb := ((D.haar.continuous.coefficient i).coupling_loss z hi plan hplan ho).le
    constructor
    · rw [← hplan.1, Measure.map_apply measurable_fst measurableSet_Icc.compl]
      apply le_trans (measure_mono ?_) hb
      intro p hp hregion
      exact hp ((D.haar.continuous.coefficient i).window.region_subset hregion).1
    · rw [← hplan.2, Measure.map_apply measurable_snd measurableSet_Icc.compl]
      apply le_trans (measure_mono ?_) hb
      intro p hp hregion
      exact hp ((D.haar.continuous.coefficient i).window.region_subset hregion).2.1
  exact ⟨D.physical_core_complement_le_of_conditional_loss hcomplete hu ha η₀ hlabel₀
      hregular₀ (htail.mono fun z hz i hi ↦ (hz i hi).1),
    D.physical_core_complement_le_of_conditional_loss hcomplete hu ha η₁ hlabel₁
      hregular₁ (htail.mono fun z hz i hi ↦ (hz i hi).2)⟩

omit [BorelSpace E] in
/-- The original optimal face and compact physical carriers provide the ordered
conditional couplings internally. Both physical core losses therefore follow
from the original data, without a conditional coupling existence assumption. -/
theorem physical_core_complements_le_of_optimal_face
    [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (hlabel₀ : η₀.map a = lambda) (hlabel₁ : η₁.map a = lambda)
    (hregular₀ : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hregular₁ : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀ : ∀ᵐ x ∂η₀, x ∈ A) (hη₁ : ∀ᵐ x ∂η₁, x ∈ B)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instStandard : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure η₀
      ∀ plan : Measure (M × M), IsOptimalCoupling edist η₀ η₁ plan ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ η₀.map a = plan ∧
          ∀ᵐ z ∂η₀.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a η₀ z) (condDistrib id a η₁ z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2) :
    η₀ (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i)ᶜ ≤
      lambda (⋃ i, (D.haar.continuous.coefficient i).roots)ᶜ +
        δ * lambda (⋃ i, (D.haar.continuous.coefficient i).roots) ∧
    η₁ (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i)ᶜ ≤
      lambda (⋃ i, (D.haar.continuous.coefficient i).roots)ᶜ +
        δ * lambda (⋃ i, (D.haar.continuous.coefficient i).roots) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure η₀
  obtain ⟨plan, hplan⟩ := exists_isOptimalCoupling_edist_of_compact_carrier η₀ η₁
    (hA.union hB) (hη₀.mono fun _ hx ↦ Or.inl hx) (hη₁.mono fun _ hy ↦ Or.inr hy)
  obtain ⟨k, _, _, hk⟩ := (hface plan).mp hplan
  have hclock₀ := ae_condDistrib_clock_eq_map_id η₀ a hu.continuous.measurable
  have hclock₁ := ae_condDistrib_clock_eq_map_id η₁ a hu.continuous.measurable
  rw [hlabel₀] at hk hclock₀
  rw [hlabel₁] at hclock₁
  apply D.physical_core_complements_le_of_legal_couplings hcomplete hu ha
    hlabel₀ hlabel₁ hregular₀ hregular₁
  filter_upwards [hk, hclock₀, hclock₁] with z hz h₀ h₁
  refine ⟨(k z).map (Prod.map u u), ?_, ?_⟩
  · rw [h₀, h₁]
    exact hz.1.map u u hu.continuous.measurable hu.continuous.measurable
  · exact (ae_map_iff (hu.continuous.measurable.prodMap hu.continuous.measurable).aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).mpr (hz.2.mono fun p hp ↦ hp.2.2.2)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
