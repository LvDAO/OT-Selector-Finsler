import OTSelector.Probability.CavitySemidiscreteSourceMass
import OTSelector.MeasureTheory.NonproperMarginalLocalFiniteness

/-!
# Original random source-window laws

The original environment and independent uniform root give the actual plan's
source-window first moment. This is independent of sample size and applies on the
common almost-sure feasibility event.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {ι A B Ω : Type*} [Fintype ι]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Ω]

/-- The actual environment-root first moment of source-window mass is bounded by
its Haar volume; the original target sample and all its correlations are retained. -/
theorem lintegral_original_rootedPlan_sourceWindow_le {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (a : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun v ↦ a v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (hfeas : ∀ᵐ ω ∂P, IsSemidiscreteAllocation μ (p ω) (fun s ↦ a (ω, s)))
    (N : ℝ) (hN : 0 < N) (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ v : Ω × (ι → ℝ),
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2 {e | e.1.1 ∈ U}
      ∂P.prod (cavityRootMeasure volume D N)) ≤ volume U := by
  have hm : Measurable (fun v : Ω × (ι → ℝ) ↦
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2 {e | e.1.1 ∈ U}) :=
    (Measure.measurable_coe (hU.preimage measurable_fst.fst)).comp
    (measurable_joint_cavitySpatialRootedPlan μ a ham Y hY N)
  have : SFinite (cavityRootMeasure volume D N) := by
    unfold cavityRootMeasure
    infer_instance
  rw [lintegral_prod _ hm.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Ω, volume U ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hfeas] with ω hω
      exact lintegral_cavitySpatialRootedPlan_sourceWindow_le μ (p ω)
        (fun s ↦ a (ω, s)) hω (Y ω) N hN D U hU
    _ = volume U := by simp

/-- The original environment-root escape mass is controlled by the original
allocation's expected energy, before any limiting plan is introduced. -/
theorem lintegral_original_rootedPlan_longEdgeWindow_le {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (a : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun v ↦ a v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (hfeas : ∀ᵐ ω ∂P, IsSemidiscreteAllocation μ (p ω) (fun s ↦ a (ω, s)))
    (N : ℝ) (hN : 0 < N) (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (r : ℝ≥0∞) (hr : r ≠ 0) (hrt : r ≠ ⊤) :
    (∫⁻ v : Ω × (ι → ℝ),
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2 (cavityLongEdgeWindow U r)
      ∂P.prod (cavityRootMeasure volume D N)) ≤
    ∫⁻ ω, (volume U * ∫⁻ e, ENNReal.ofReal (‖(Y ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s))) / r ∂P := by
  have hm : Measurable (fun v : Ω × (ι → ℝ) ↦
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2 (cavityLongEdgeWindow U r)) :=
    (Measure.measurable_coe (measurableSet_cavityLongEdgeWindow hU r)).comp
    (measurable_joint_cavitySpatialRootedPlan μ a ham Y hY N)
  have : SFinite (cavityRootMeasure volume D N) := by
    unfold cavityRootMeasure
    infer_instance
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [hfeas] with ω hω
  exact lintegral_cavitySpatialRootedPlan_longEdgeWindow_le μ (p ω)
    (fun s ↦ a (ω, s)) hω (Y ω) N hN D U hU r hr hrt

/-- A finite bound on the actual expected displacement energy gives the explicit
inverse-threshold escape estimate on the original probability space. -/
theorem lintegral_original_rootedPlan_longEdgeWindow_le_of_energy {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (a : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun v ↦ a v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (hfeas : ∀ᵐ ω ∂P, IsSemidiscreteAllocation μ (p ω) (fun s ↦ a (ω, s)))
    (N : ℝ) (hN : 0 < N) (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hUfinite : volume U ≠ ⊤) (C : ℝ≥0∞)
    (henergy : (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s)) ∂P) ≤ C)
    (r : ℝ≥0∞) (hr : r ≠ 0) (hrt : r ≠ ⊤) :
    (∫⁻ v : Ω × (ι → ℝ),
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2 (cavityLongEdgeWindow U r)
      ∂P.prod (cavityRootMeasure volume D N)) ≤ volume U * C / r := by
  apply (lintegral_original_rootedPlan_longEdgeWindow_le P μ p a ham Y hY hfeas
    N hN D U hU r hr hrt).trans
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hr),
    lintegral_const_mul' _ _ hUfinite]
  gcongr

section Scene
variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [TopologicalSpace B] [BorelSpace B]
  [T2Space B] [LocallyCompactSpace B] [PseudoMetrizableSpace B]
  [SigmaCompactSpace B] [SecondCountableTopology B]

local instance cavitySemidiscreteSourceMassLawLocalInst1 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Both original plan coordinates satisfy the same source-window expectation
bound under the actual correlated rooted scene law. -/
theorem cavityRootedLocalSceneLaw_sourceWindow_bounds {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)) ∧
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s)))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (U : Set (ι → ℝ)) (hU : IsOpen U) :
    (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U}
      ∂(cavityRootedLocalSceneLaw P μ aplus aminus hplusm hminusm Y hY N hN D hD : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))))
        ≤ volume U ∧
    (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U}
      ∂(cavityRootedLocalSceneLaw P μ aplus aminus hplusm hminusm Y hY N hN D hD : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))))
        ≤ volume U := by
  have hm₀ : Measurable (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U}) :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open
      (hU.preimage continuous_fst.fst)).comp continuous_fst).measurable
  have hm₁ : Measurable (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U}) :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open
      (hU.preimage continuous_fst.fst)).comp continuous_snd).measurable
  have hscene := measurable_cavityRootedLocalScene μ aplus aminus hplusm hminusm Y hY N
  constructor
  · change (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U}
      ∂(P.prod (cavityRootMeasure volume D N)).map
        (cavityRootedLocalScene μ aplus aminus Y N)) ≤ _
    rw [lintegral_map hm₀ hscene]
    apply le_trans _ (lintegral_original_rootedPlan_sourceWindow_le P μ p aplus
      hplusm Y hY (hfeas.mono fun _ h ↦ h.1) N hN D U hU.measurableSet)
    apply lintegral_mono
    intro v
    change (finitePlanLocalVersion
      (fun v : Ω × (ι → ℝ) ↦ cavitySpatialRootedPlan μ
        (fun s ↦ aplus (v.1, s)) (Y v.1) N v.2) v :
      Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U} ≤ _
    rw [coe_finitePlanLocalVersion]
    split_ifs <;> simp
  · change (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U}
      ∂(P.prod (cavityRootMeasure volume D N)).map
        (cavityRootedLocalScene μ aplus aminus Y N)) ≤ _
    rw [lintegral_map hm₁ hscene]
    apply le_trans _ (lintegral_original_rootedPlan_sourceWindow_le P μ p aminus
      hminusm Y hY (hfeas.mono fun _ h ↦ h.2) N hN D U hU.measurableSet)
    apply lintegral_mono
    intro v
    change (finitePlanLocalVersion
      (fun v : Ω × (ι → ℝ) ↦ cavitySpatialRootedPlan μ
        (fun s ↦ aminus (v.1, s)) (Y v.1) N v.2) v :
      Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) {e | e.1.1 ∈ U} ≤ _
    rw [coe_finitePlanLocalVersion]
    split_ifs <;> simp

end Scene
end OTSelector.Probability
