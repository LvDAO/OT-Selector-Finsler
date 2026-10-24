import OTSelector.Reconstruction.FinslerPhysicalSceneRootedFullDisplacement

/-!
# Finite actual physical event covers under rooting

A finite cover of one original physical restriction remains a sum bound after
the same actual rooted observation and after the original environment and root
integrals.  An explicit remainder may be read on a larger rooted window.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open OTSelector.Probability
open scoped Topology ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι X J : Type*} [Fintype ι] [Fintype J] [MeasurableSpace X]

/-- Restricting the same original physical source keeps every near piece and
the complete non-near remainder in one explicit physical cover. -/
theorem physicalScene_source_restriction_near_cover
    (A B H : Set X) (Snear : J → Set (X × X)) :
    (A ×ˢ B) ∩ (H ×ˢ univ) ⊆
      (⋃ j, Snear j ∩ (H ×ˢ univ)) ∪
        (((A ×ˢ B) \ ⋃ j, Snear j) ∩ (H ×ˢ univ)) := by
  classical
  intro p hp
  by_cases hn : p ∈ ⋃ j, Snear j
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    exact Or.inl (mem_iUnion.mpr ⟨j, hj, hp.2⟩)
  · exact Or.inr ⟨⟨hp.1, hn⟩, hp.2⟩

/-- A finite actual physical event cover bounds the same rooted plan by the
sum of its original restricted pieces and its explicit remainder. -/
theorem physicalSceneRootedPlan_finite_event_cover_le
    (Γ : Measure (X × X)) (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock) (N : ℝ) (z : ι → ℝ)
    {S Q : Set (X × X)} {Snear : J → Set (X × X)}
    (hcover : S ⊆ (⋃ j, Snear j) ∪ Q)
    {T Tbad : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hT : MeasurableSet T) (hTbad : MeasurableSet Tbad) (hsub : T ⊆ Tbad) :
    physicalSceneRootedPlan (Γ.restrict S) coord clock N z T ≤
      (∑ j, physicalSceneRootedPlan (Γ.restrict (Snear j)) coord clock N z T) +
      physicalSceneRootedPlan (Γ.restrict Q) coord clock N z Tbad := by
  classical
  let f := physicalSceneRootedObservation coord clock z
  have hf : Measurable f := measurable_physicalSceneRootedObservation coord hcoord clock hclock z
  have hμ : Γ.restrict S ≤ (∑ j, Γ.restrict (Snear j)) + Γ.restrict Q := by
    apply (Measure.restrict_mono hcover le_rfl).trans
    apply (Measure.restrict_union_le _ _).trans
    apply add_le_add _ le_rfl
    simpa only [Measure.sum_fintype] using
      (Measure.restrict_iUnion_le (μ := Γ) (s := Snear))
  have hm : (Γ.restrict S) (f ⁻¹' T) ≤
      (∑ j, (Γ.restrict (Snear j)) (f ⁻¹' T)) + (Γ.restrict Q) (f ⁻¹' Tbad) := by
    have h := hμ (f ⁻¹' T)
    simp only [Measure.add_apply, Measure.finsetSum_apply] at h
    exact h.trans (add_le_add le_rfl (measure_mono (preimage_mono hsub)))
  change ENNReal.ofReal N * ((Γ.restrict S).map f) T ≤
    (∑ j, ENNReal.ofReal N * ((Γ.restrict (Snear j)).map f) T) +
      ENNReal.ofReal N * ((Γ.restrict Q).map f) Tbad
  simp_rw [Measure.map_apply hf hT]
  rw [Measure.map_apply hf hTbad]
  simpa only [mul_add, Finset.mul_sum] using mul_le_mul_right hm (ENNReal.ofReal N)

/-- The finite actual cover remains the corresponding sum after both original
integrals.  Joint measurability follows from the same original finite family. -/
theorem lintegral_physicalSceneRootedPlan_finite_event_cover_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Penv : Measure Ω) (Γ : Ω → Measure (X × X)) [∀ w, IsFiniteMeasure (Γ w)]
    (hΓ : Measurable Γ)
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock) (N : ℝ) (hN : 0 < N)
    (rootDomain : Set (ι → ℝ)) (hD : volume rootDomain = ENNReal.ofReal N)
    {S Q : Set (X × X)} {Snear : J → Set (X × X)}
    (hcover : S ⊆ (⋃ j, Snear j) ∪ Q) (hSnear : ∀ j, MeasurableSet (Snear j))
    {T Tbad : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hT : MeasurableSet T) (hTbad : MeasurableSet Tbad) (hsub : T ⊆ Tbad) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict S) coord clock N z T
      ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
      (∑ j, ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (Snear j)) coord clock N z T
        ∂cavityRootMeasure volume rootDomain N ∂Penv) +
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict Q) coord clock N z Tbad
        ∂cavityRootMeasure volume rootDomain N ∂Penv := by
  classical
  have : IsProbabilityMeasure (cavityRootMeasure volume rootDomain N) :=
    isProbabilityMeasure_cavityRootMeasure volume rootDomain N hN hD
  have hΓnear (j : J) : Measurable (fun w ↦ (Γ w).restrict (Snear j)) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simp only [Measure.restrict_apply hV]
    exact (Measure.measurable_coe (hV.inter (hSnear j))).comp hΓ
  have hm (j : J) : Measurable (fun v : Ω × (ι → ℝ) ↦
      physicalSceneRootedPlan ((Γ v.1).restrict (Snear j)) coord clock N v.2 T) :=
    (Measure.measurable_coe hT).comp
      (measurable_joint_physicalSceneRootedPlan _ (hΓnear j) coord hcoord clock hclock N)
  have hsum : Measurable (fun v : Ω × (ι → ℝ) ↦
      ∑ j, physicalSceneRootedPlan ((Γ v.1).restrict (Snear j)) coord clock N v.2 T) :=
    Finset.measurable_sum _ (fun j _ ↦ hm j)
  calc
    _ ≤ ∫⁻ w, ∫⁻ z,
        (∑ j, physicalSceneRootedPlan ((Γ w).restrict (Snear j)) coord clock N z T) +
        physicalSceneRootedPlan ((Γ w).restrict Q) coord clock N z Tbad
        ∂cavityRootMeasure volume rootDomain N ∂Penv :=
      lintegral_mono fun w ↦ lintegral_mono fun z ↦
        physicalSceneRootedPlan_finite_event_cover_le (Γ w) coord hcoord clock hclock
          N z hcover hT hTbad hsub
    _ = ∫⁻ w,
        (∫⁻ z, ∑ j, physicalSceneRootedPlan ((Γ w).restrict (Snear j)) coord clock N z T
          ∂cavityRootMeasure volume rootDomain N) +
        (∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict Q) coord clock N z Tbad
          ∂cavityRootMeasure volume rootDomain N) ∂Penv := by
      apply lintegral_congr
      intro w
      exact lintegral_add_left (hsum.comp
        (show Measurable (fun z : ι → ℝ ↦ (w, z)) from measurable_const.prodMk measurable_id)) _
    _ = (∫⁻ w, ∫⁻ z, ∑ j, physicalSceneRootedPlan ((Γ w).restrict (Snear j)) coord clock N z T
          ∂cavityRootMeasure volume rootDomain N ∂Penv) +
        ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict Q) coord clock N z Tbad
          ∂cavityRootMeasure volume rootDomain N ∂Penv :=
      lintegral_add_left hsum.lintegral_prod_right' _
    _ = _ := by
      congr 1
      calc
        _ = ∫⁻ w, ∑ j, ∫⁻ z,
            physicalSceneRootedPlan ((Γ w).restrict (Snear j)) coord clock N z T
              ∂cavityRootMeasure volume rootDomain N ∂Penv := by
          apply lintegral_congr
          intro w
          exact lintegral_finsetSum _ (fun j _ ↦ (hm j).comp
            (show Measurable (fun z : ι → ℝ ↦ (w, z)) from measurable_const.prodMk measurable_id))
        _ = _ := lintegral_finsetSum _ (fun j _ ↦ (hm j).lintegral_prod_right')

end OTSelector.Reconstruction
