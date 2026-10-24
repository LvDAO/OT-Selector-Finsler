import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessPopulation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessIntegral

/-!
# Full actual cycle witnesses differ from retained physical core witnesses

The same source-restricted global plans are observed throughout. Their full
capped witness exceeds its actual endpoint-core restriction by at most the
original Haar source-window volume times the two original population losses.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

/-- Both original integrals retain the capped witness inequality, paying the
actual physical endpoint loss once in the common bounded source window. -/
theorem lintegral_physicalSceneRooted_average_witness_le_core_and_mass_loss
    (Penv : Measure Ω) (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (E : Set (M × M)) (hE : MeasurableSet E) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤) (C : ℝ≥0∞)
    (hCp : (∫⁻ w, Γp w Eᶜ ∂Penv) ≤ C)
    (hCm : (∫⁻ w, Γm w Eᶜ ∂Penv) ≤ C)
    (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (hT₀ : T₀ ⊆ {e | e.1.1 ∈ U}) (hT₁ : T₁ ⊆ {e | e.1.1 ∈ U}) :
    let avg := fun w z S ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan ((Γp w).restrict S) coord u N z +
        physicalSceneRootedPlan ((Γm w).restrict S) coord u N z)
    (∫⁻ w, ∫⁻ z, min 1 (min (avg w z (H ×ˢ univ) T₀) (avg w z (H ×ˢ univ) T₁))
      ∂cavityRootMeasure volume D N ∂Penv) ≤
      (∫⁻ w, ∫⁻ z, min 1 (min (avg w z (E ∩ (H ×ˢ univ)) T₀)
        (avg w z (E ∩ (H ×ˢ univ)) T₁)) ∂cavityRootMeasure volume D N ∂Penv) + volume U * C := by
  have := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  let avg := fun w z S ↦ (2 : ℝ≥0∞)⁻¹ •
    (physicalSceneRootedPlan ((Γp w).restrict S) coord u N z +
      physicalSceneRootedPlan ((Γm w).restrict S) coord u N z)
  let Q := Eᶜ ∩ (H ×ˢ univ)
  let W : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) := {e | e.1.1 ∈ U}
  have hQ : MeasurableSet Q := hE.compl.inter (hH.prod MeasurableSet.univ)
  have hW : MeasurableSet W := hU.preimage measurable_fst.fst
  have hpM : Measurable (fun v : Ω × (ι → ℝ) ↦
      physicalSceneRootedPlan ((Γp v.1).restrict Q) coord u N v.2 W) :=
    (Measure.measurable_coe hW).comp (measurable_joint_physicalSceneRootedPlan
      (fun w ↦ (Γp w).restrict Q) (measurable_physicalPlan_endpointRestriction Γp hp Q hQ)
      coord hcoord u hu N)
  have hmM : Measurable (fun v : Ω × (ι → ℝ) ↦
      physicalSceneRootedPlan ((Γm v.1).restrict Q) coord u N v.2 W) :=
    (Measure.measurable_coe hW).comp (measurable_joint_physicalSceneRootedPlan
      (fun w ↦ (Γm w).restrict Q) (measurable_physicalPlan_endpointRestriction Γm hm Q hQ)
      coord hcoord u hu N)
  have hLoss : Measurable (fun v : Ω × (ι → ℝ) ↦ avg v.1 v.2 Q W) := by
    change Measurable (fun v : Ω × (ι → ℝ) ↦ (2 : ℝ≥0∞)⁻¹ *
      (physicalSceneRootedPlan ((Γp v.1).restrict Q) coord u N v.2 W +
        physicalSceneRootedPlan ((Γm v.1).restrict Q) coord u N v.2 W))
    exact (hpM.add hmM).const_mul _
  have hLossBound := lintegral_physicalSceneRooted_average_endpoint_loss_le Penv Γp Γm hp hm
    E hE H hH coord hcoord u hu N hN D U hD hU hUf C hCp hCm
  change (∫⁻ w, ∫⁻ z, min 1 (min (avg w z (H ×ˢ univ) T₀) (avg w z (H ×ˢ univ) T₁))
    ∂cavityRootMeasure volume D N ∂Penv) ≤
    (∫⁻ w, ∫⁻ z, min 1 (min (avg w z (E ∩ (H ×ˢ univ)) T₀)
      (avg w z (E ∩ (H ×ˢ univ)) T₁)) ∂cavityRootMeasure volume D N ∂Penv) + volume U * C
  calc
    _ ≤ ∫⁻ w, ∫⁻ z, min 1 (min (avg w z (E ∩ (H ×ˢ univ)) T₀)
        (avg w z (E ∩ (H ×ˢ univ)) T₁)) + avg w z Q W
        ∂cavityRootMeasure volume D N ∂Penv :=
      lintegral_mono fun w ↦ lintegral_mono fun z ↦
        physicalSceneRootedPlan_average_witness_le_core_and_loss (Γp w) (Γm w)
          H E hE coord hcoord u hu N z T₀ T₁ W hT₀ hT₁
    _ = (∫⁻ w, ∫⁻ z, min 1 (min (avg w z (E ∩ (H ×ˢ univ)) T₀)
        (avg w z (E ∩ (H ×ˢ univ)) T₁)) ∂cavityRootMeasure volume D N ∂Penv) +
        ∫⁻ w, ∫⁻ z, avg w z Q W ∂cavityRootMeasure volume D N ∂Penv :=
      physicalScene_lintegral_lintegral_add_of_measurable_right Penv (cavityRootMeasure volume D N)
        (fun w z ↦ min 1 (min (avg w z (E ∩ (H ×ˢ univ)) T₀)
          (avg w z (E ∩ (H ×ˢ univ)) T₁))) (fun w z ↦ avg w z Q W) hLoss
    _ ≤ _ := add_le_add le_rfl hLossBound

/-- Original globally feasible opposite allocations give the full witness bound
with only the two original population complement masses as discarded loss. -/
theorem lintegral_actualAllocation_rooted_average_witness_le_core_and_population_loss
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (aplus aminus : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
      aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
      aminus z.1 z.2 j))
    (hfp : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aplus z))
    (hfm : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aminus z))
    (Ks Kt : Set M) (hKs : MeasurableSet Ks) (hKt : MeasurableSet Kt)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (hT₀ : T₀ ⊆ {e | e.1.1 ∈ U}) (hT₁ : T₁ ⊆ {e | e.1.1 ∈ U}) :
    let avg := fun w z S ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ aplus (fun z ↦ z.1) w).restrict S) coord u N z +
        physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ aminus (fun z ↦ z.1) w).restrict S) coord u N z)
    (∫⁻ w, ∫⁻ z, min 1 (min (avg w z (H ×ˢ univ) T₀) (avg w z (H ×ˢ univ) T₁))
      ∂cavityRootMeasure volume D N ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (∫⁻ w, ∫⁻ z, min 1 (min (avg w z ((Ks ×ˢ Kt) ∩ (H ×ˢ univ)) T₀)
        (avg w z ((Ks ×ˢ Kt) ∩ (H ×ˢ univ)) T₁))
        ∂cavityRootMeasure volume D N ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) +
      volume U * (μ Ksᶜ + ν Ktᶜ) :=
  lintegral_physicalSceneRooted_average_witness_le_core_and_mass_loss
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    (physicalSceneGlobalAllocationFamily μ aplus (fun z ↦ z.1))
    (physicalSceneGlobalAllocationFamily μ aminus (fun z ↦ z.1))
    (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus
      (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst))
    (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus
      (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst))
    (Ks ×ˢ Kt) (hKs.prod hKt) H hH coord hcoord u hu N hN D U hD hU hUf
    (μ Ksᶜ + ν Ktᶜ)
    (lintegral_physicalSceneGlobalAllocationFamily_outside_product_le μ ν n aplus hplus hfp
      Ks Kt hKs hKt)
    (lintegral_physicalSceneGlobalAllocationFamily_outside_product_le μ ν n aminus hminus hfm
      Ks Kt hKs hKt) T₀ T₁ hT₀ hT₁

end OTSelector.Reconstruction
