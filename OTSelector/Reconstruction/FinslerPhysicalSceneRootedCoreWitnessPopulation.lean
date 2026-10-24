import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessLoss

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

/-- Restricting either original endpoint to its retained physical core is
measurable in the unchanged original experiment. -/
theorem measurable_physicalPlan_endpointRestriction
    (Γ : Ω → Measure (M × M)) (hΓ : Measurable Γ)
    (E : Set (M × M)) (hE : MeasurableSet E) :
    Measurable (fun w ↦ (Γ w).restrict E) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  simp only [Measure.restrict_apply hT]
  exact (Measure.measurable_coe (hT.inter hE)).comp hΓ

/-- The original source identity and actual mean random target columns bound
all discarded endpoint mass in the same global allocation. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_outside_product_le
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
      a z.1 z.2 j))
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (a z))
    (Ks Kt : Set M) (hKs : MeasurableSet Ks) (hKt : MeasurableSet Kt) :
    (∫⁻ w, physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) w (Ks ×ˢ Kt)ᶜ
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ μ Ksᶜ + ν Ktᶜ := by
  let Γ := physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1)
  have hΓ : Measurable Γ := measurable_physicalSceneGlobalAllocationFamily μ a ha
    (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  have hcover : (Ks ×ˢ Kt)ᶜ ⊆ (Ksᶜ ×ˢ univ) ∪ (univ ×ˢ Ktᶜ) := by
    intro e he
    by_cases hs : e.1 ∈ Ks
    · exact Or.inr ⟨mem_univ _, fun ht ↦ he ⟨hs, ht⟩⟩
    · exact Or.inl ⟨hs, mem_univ _⟩
  calc
    _ ≤ ∫⁻ w, Γ w (Ksᶜ ×ˢ univ) + Γ w (univ ×ˢ Ktᶜ)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) :=
      lintegral_mono fun w ↦ (measure_mono hcover).trans (measure_union_le _ _)
    _ = (∫⁻ w, Γ w (Ksᶜ ×ˢ univ)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) +
        ∫⁻ w, Γ w (univ ×ˢ Ktᶜ)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) :=
      lintegral_add_left ((Measure.measurable_coe (hKs.compl.prod MeasurableSet.univ)).comp hΓ) _
    _ = _ := by
      rw [lintegral_physicalSceneGlobalAllocationFamily_sourceSet_eq μ ν n a hfeas hKs.compl,
        lintegral_physicalSceneGlobalAllocationFamily_targetSet_eq μ ν n a hfeas hKt.compl]

/-- The actual arithmetic mean of the two discarded physical pieces has the
same root-window expectation bound; neither restricted column law is changed. -/
theorem lintegral_physicalSceneRooted_average_endpoint_loss_le
    (Penv : Measure Ω) (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (E : Set (M × M)) (hE : MeasurableSet E) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤) (C : ℝ≥0∞)
    (hCp : (∫⁻ w, Γp w Eᶜ ∂Penv) ≤ C)
    (hCm : (∫⁻ w, Γm w Eᶜ ∂Penv) ≤ C) :
    (∫⁻ w, ∫⁻ z, ((2 : ℝ≥0∞)⁻¹ •
        (physicalSceneRootedPlan ((Γp w).restrict (Eᶜ ∩ (H ×ˢ univ))) coord u N z +
          physicalSceneRootedPlan ((Γm w).restrict (Eᶜ ∩ (H ×ˢ univ))) coord u N z))
          {e | e.1.1 ∈ U} ∂cavityRootMeasure volume D N ∂Penv) ≤ volume U * C := by
  have := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  let Q := Eᶜ ∩ (H ×ˢ univ)
  let W : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) := {e | e.1.1 ∈ U}
  have hQ : MeasurableSet Q := hE.compl.inter (hH.prod MeasurableSet.univ)
  have hW : MeasurableSet W := hU.preimage measurable_fst.fst
  let p := fun w z ↦ physicalSceneRootedPlan ((Γp w).restrict Q) coord u N z W
  let m := fun w z ↦ physicalSceneRootedPlan ((Γm w).restrict Q) coord u N z W
  have hpm : Measurable (fun v : Ω × (ι → ℝ) ↦ p v.1 v.2) :=
    (Measure.measurable_coe hW).comp (measurable_joint_physicalSceneRootedPlan
      (fun w ↦ (Γp w).restrict Q) (measurable_physicalPlan_endpointRestriction Γp hp Q hQ)
      coord hcoord u hu N)
  have hmm : Measurable (fun v : Ω × (ι → ℝ) ↦ m v.1 v.2) :=
    (Measure.measurable_coe hW).comp (measurable_joint_physicalSceneRootedPlan
      (fun w ↦ (Γm w).restrict Q) (measurable_physicalPlan_endpointRestriction Γm hm Q hQ)
      coord hcoord u hu N)
  have hbp := lintegral_event_restricted_rooted_sourceWindow_expected_le_of_mass
    Penv Γp coord hcoord u hu N hN D U hU hUf Eᶜ H C hCp
  have hbm := lintegral_event_restricted_rooted_sourceWindow_expected_le_of_mass
    Penv Γm coord hcoord u hu N hN D U hU hUf Eᶜ H C hCm
  change (∫⁻ w, ∫⁻ z, (2 : ℝ≥0∞)⁻¹ * (p w z + m w z)
    ∂cavityRootMeasure volume D N ∂Penv) ≤ volume U * C
  calc
    _ = (2 : ℝ≥0∞)⁻¹ * ((∫⁻ w, ∫⁻ z, p w z ∂cavityRootMeasure volume D N ∂Penv) +
        ∫⁻ w, ∫⁻ z, m w z ∂cavityRootMeasure volume D N ∂Penv) := by
      simp_rw [lintegral_const_mul' _ _ (show (2 : ℝ≥0∞)⁻¹ ≠ ⊤ by norm_num)]
      congr 1
      calc
        _ = ∫⁻ w, (∫⁻ z, p w z ∂cavityRootMeasure volume D N) +
            ∫⁻ z, m w z ∂cavityRootMeasure volume D N ∂Penv := by
          apply lintegral_congr
          intro w
          exact lintegral_add_left (hpm.comp (measurable_const.prodMk measurable_id)) _
        _ = _ := lintegral_add_left hpm.lintegral_prod_right' _
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (volume U * C + volume U * C) :=
      mul_le_mul_right (add_le_add hbp hbm) _
    _ = _ := by
      rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end OTSelector.Reconstruction
