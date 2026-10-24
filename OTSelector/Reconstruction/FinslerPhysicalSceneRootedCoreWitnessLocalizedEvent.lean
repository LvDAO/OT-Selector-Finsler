import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessScreenedDefect

/-!
# Localizing a full-scene cycle witness using retained actual edge events

Only observed edges inside the requested root window must enter the selected
physical endpoint core. The exceptional mass is the complement of an actual
retained edge event, allowing the original near-event energy bound to pay it
without paying the population complement of one coefficient core.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

/-- Only original edges whose actual observation belongs to the test window
need satisfy the deterministic retained-core inclusion. -/
theorem physicalSceneRootedPlan_restrict_le_of_observed_event_inclusion
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (E F : Set (M × M))
    (T : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (hT : MeasurableSet T)
    (hinc : ∀ e ∈ E, physicalSceneRootedObservation coord u z e ∈ T → e ∈ F) :
    physicalSceneRootedPlan (Γ.restrict E) coord u N z T ≤
      physicalSceneRootedPlan (Γ.restrict F) coord u N z T := by
  have hf := measurable_physicalSceneRootedObservation coord hcoord u hu z
  change ENNReal.ofReal N * ((Γ.restrict E).map _) T ≤
    ENNReal.ofReal N * ((Γ.restrict F).map _) T
  rw [Measure.map_apply hf hT, Measure.map_apply hf hT,
    Measure.restrict_apply (hT.preimage hf), Measure.restrict_apply (hT.preimage hf)]
  have hsub : physicalSceneRootedObservation coord u z ⁻¹' T ∩ E ⊆
      physicalSceneRootedObservation coord u z ⁻¹' T ∩ F :=
    fun e he ↦ ⟨he.1, hinc e he.2 he.1⟩
  exact mul_le_mul_right (measure_mono hsub) _

/-- The complete arithmetic-average witness pays only discarded actual-event
mass once its retained observed edges enter the selected endpoint product. -/
theorem physicalSceneRootedPlan_average_witness_le_local_core_and_event_loss
    (Γp Γm : Measure (M × M)) (H : Set M) (E F : Set (M × M))
    (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (T₀ T₁ W : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (hT₀ : MeasurableSet T₀) (hT₁ : MeasurableSet T₁)
    (hT₀W : T₀ ⊆ W) (hT₁W : T₁ ⊆ W)
    (hinc : ∀ e ∈ E ∩ (H ×ˢ univ),
      physicalSceneRootedObservation coord u z e ∈ T₀ ∪ T₁ → e ∈ F) :
    let avg := fun S ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan (Γp.restrict S) coord u N z +
       physicalSceneRootedPlan (Γm.restrict S) coord u N z)
    min 1 (min (avg (H ×ˢ univ) T₀) (avg (H ×ˢ univ) T₁)) ≤
      min 1 (min (avg (F ∩ (H ×ˢ univ)) T₀) (avg (F ∩ (H ×ˢ univ)) T₁)) +
        avg (Eᶜ ∩ (H ×ˢ univ)) W := by
  let avg := fun S ↦ (2 : ℝ≥0∞)⁻¹ •
    (physicalSceneRootedPlan (Γp.restrict S) coord u N z +
     physicalSceneRootedPlan (Γm.restrict S) coord u N z)
  have hbound (T : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      (hT : MeasurableSet T) (hsub : T ⊆ T₀ ∪ T₁) :
      avg (E ∩ (H ×ˢ univ)) T ≤ avg (F ∩ (H ×ˢ univ)) T := by
    have hinc' : ∀ e ∈ E ∩ (H ×ˢ univ),
        physicalSceneRootedObservation coord u z e ∈ T → e ∈ F ∩ (H ×ˢ univ) :=
      fun e he ht ↦ ⟨hinc e he (hsub ht), he.2⟩
    change (2 : ℝ≥0∞)⁻¹ * (_ + _) ≤ (2 : ℝ≥0∞)⁻¹ * (_ + _)
    exact mul_le_mul_right (add_le_add
      (physicalSceneRootedPlan_restrict_le_of_observed_event_inclusion Γp coord hcoord u hu
        N z _ _ T hT hinc')
      (physicalSceneRootedPlan_restrict_le_of_observed_event_inclusion Γm coord hcoord u hu
        N z _ _ T hT hinc')) _
  have hb := physicalSceneRootedPlan_average_witness_le_core_and_loss Γp Γm H E hE
    coord hcoord u hu N z T₀ T₁ W hT₀W hT₁W
  exact hb.trans (add_le_add
    (min_le_min_left 1 (min_le_min
      (hbound T₀ hT₀ subset_union_left) (hbound T₁ hT₁ subset_union_right))) le_rfl)

/-- A root-local deterministic inclusion lets the same original non-near mass
bound control the full witness. The selected core's population complement is
not charged. -/
theorem lintegral_physicalSceneRooted_average_screened_witness_le_local_core_and_event_loss
    (Penv : Measure Ω) (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (E F : Set (M × M)) (hE : MeasurableSet E)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤) (C : ℝ≥0∞)
    (hCp : (∫⁻ w, Γp w Eᶜ ∂Penv) ≤ C)
    (hCm : (∫⁻ w, Γm w Eᶜ ∂Penv) ≤ C)
    (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (hT₀ : MeasurableSet T₀) (hT₁ : MeasurableSet T₁)
    (hT₀U : T₀ ⊆ {e | e.1.1 ∈ U}) (hT₁U : T₁ ⊆ {e | e.1.1 ∈ U})
    (Eroot : Set (ι → ℝ))
    (hinc : ∀ z ∈ Eroot, ∀ e ∈ E ∩ (H ×ˢ univ),
      physicalSceneRootedObservation coord u z e ∈ T₀ ∪ T₁ → e ∈ F) :
    let avg := fun w z S ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan ((Γp w).restrict S) coord u N z +
       physicalSceneRootedPlan ((Γm w).restrict S) coord u N z)
    (∫⁻ w, ∫⁻ z, Eroot.indicator (fun z ↦ min 1 (min (avg w z (H ×ˢ univ) T₀)
        (avg w z (H ×ˢ univ) T₁))) z ∂cavityRootMeasure volume D N ∂Penv) ≤
      (∫⁻ w, ∫⁻ z, Eroot.indicator (fun z ↦ min 1
        (min (avg w z (F ∩ (H ×ˢ univ)) T₀) (avg w z (F ∩ (H ×ˢ univ)) T₁))) z
        ∂cavityRootMeasure volume D N ∂Penv) + volume U * C := by
  have := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have hb := lintegral_physicalSceneRooted_average_screened_witness_le_core_and_mass_loss
    Penv Γp Γm hp hm E hE H hH coord hcoord u hu N hN D U hD hU hUf C hCp hCm
    T₀ T₁ hT₀U hT₁U Eroot
  dsimp only at hb ⊢
  apply hb.trans
  apply add_le_add_left
  apply lintegral_mono
  intro w
  apply lintegral_mono
  intro z
  by_cases hz : z ∈ Eroot
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    have hbound (T : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        (hT : MeasurableSet T) (hsub : T ⊆ T₀ ∪ T₁) :
        ((2 : ℝ≥0∞)⁻¹ •
          (physicalSceneRootedPlan ((Γp w).restrict (E ∩ (H ×ˢ univ))) coord u N z +
           physicalSceneRootedPlan ((Γm w).restrict (E ∩ (H ×ˢ univ))) coord u N z)) T ≤
        ((2 : ℝ≥0∞)⁻¹ •
          (physicalSceneRootedPlan ((Γp w).restrict (F ∩ (H ×ˢ univ))) coord u N z +
           physicalSceneRootedPlan ((Γm w).restrict (F ∩ (H ×ˢ univ))) coord u N z)) T := by
      change (2 : ℝ≥0∞)⁻¹ * (_ + _) ≤ (2 : ℝ≥0∞)⁻¹ * (_ + _)
      apply mul_le_mul_right
      apply add_le_add
      · exact physicalSceneRootedPlan_restrict_le_of_observed_event_inclusion _ coord hcoord u hu
          N z _ _ T hT (fun e he ht ↦ ⟨hinc z hz e he (hsub ht), he.2⟩)
      · exact physicalSceneRootedPlan_restrict_le_of_observed_event_inclusion _ coord hcoord u hu
          N z _ _ T hT (fun e he ht ↦ ⟨hinc z hz e he (hsub ht), he.2⟩)
    exact min_le_min_left 1 (min_le_min
      (hbound T₀ hT₀ subset_union_left) (hbound T₁ hT₁ subset_union_right))
  · simp only [Set.indicator_of_notMem hz]
    exact le_rfl

end OTSelector.Reconstruction
