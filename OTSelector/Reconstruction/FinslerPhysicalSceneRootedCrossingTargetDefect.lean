import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMarginals
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonNearMass
import OTSelector.Geometry.FinslerDistanceLocalizationCore

/-!
# Actual target defects at full physical cores

Source restriction and target restriction differ only on edges crossing the
same physical source set.  Any actual physical event covering those crossings
on the original carriers pays the defect.  The full original target marginal,
restricted physically to that same set, is common to the two allocations; their
random source-restricted columns remain unchanged throughout the estimate.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Both directions of crossing the same original physical source set. -/
def physicalSceneCoreCrossing {X : Type*} (H : Set X) : Set (X × X) :=
  (H ×ˢ Hᶜ) ∪ (Hᶜ ×ˢ H)

theorem measurableSet_physicalSceneCoreCrossing {X : Type*} [MeasurableSpace X]
    {H : Set X} (hH : MeasurableSet H) : MeasurableSet (physicalSceneCoreCrossing H) :=
  (hH.prod hH.compl).union (hH.compl.prod hH)


section Restriction
variable {X : Type*} [MeasurableSpace X]

/-- The signed difference between source and target restriction is supported
only on the physical crossing event and the actual observable window. -/
theorem ofReal_abs_source_restrict_sub_target_restrict_le_crossing
    (Γ : Measure (X × X)) [IsFiniteMeasure Γ] (H : Set X) (hH : MeasurableSet H)
    (F : X × X → ℝ) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ p, ‖F p‖ ≤ B) (W : Set (X × X))
    (hzero : ∀ p, p ∉ W → F p = 0) :
    ENNReal.ofReal |(∫ p, F p ∂Γ.restrict (H ×ˢ univ)) -
      ∫ p, F p ∂Γ.restrict (univ ×ˢ H)| ≤
      ENNReal.ofReal B * Γ (physicalSceneCoreCrossing H ∩ W) := by
  classical
  let S := H ×ˢ (univ : Set X)
  let T := (univ : Set X) ×ˢ H
  let G := fun p ↦ S.indicator F p - T.indicator F p
  let Q := physicalSceneCoreCrossing H ∩ W
  have hS : MeasurableSet S := hH.prod MeasurableSet.univ
  have hT : MeasurableSet T := MeasurableSet.univ.prod hH
  have hint : Integrable F Γ :=
    Integrable.of_bound hF.aestronglyMeasurable B (Eventually.of_forall hbound)
  have hzeroG : ∀ p, p ∉ Q → G p = 0 := by
    intro p hp
    by_cases hw : p ∈ W
    · have hc : p ∉ physicalSceneCoreCrossing H := fun hc ↦ hp ⟨hc, hw⟩
      by_cases hx : p.1 ∈ H <;> by_cases hy : p.2 ∈ H <;>
        simp [G, S, T, physicalSceneCoreCrossing, hx, hy] at *
    · simp only [G, indicator_apply, hzero p hw]
      split_ifs <;> simp
  have hboundG : ∀ p, ‖G p‖ ≤ B := by
    intro p
    by_cases hx : p.1 ∈ H <;> by_cases hy : p.2 ∈ H <;>
      simp [G, S, T, hx, hy]
    all_goals first | exact hB | simpa only [Real.norm_eq_abs] using hbound p
  have hreal : |(∫ p, F p ∂Γ.restrict (H ×ˢ univ)) -
      ∫ p, F p ∂Γ.restrict (univ ×ˢ H)| ≤ B * Γ.real Q := by
    rw [← integral_indicator hS, ← integral_indicator hT,
      ← integral_sub (hint.indicator hS) (hint.indicator hT)]
    change |∫ p, G p ∂Γ| ≤ _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzeroG]
    simpa only [Real.norm_eq_abs] using norm_setIntegral_le_of_norm_le_const_ae
      (μ := Γ) (s := Q) (f := G) (measure_lt_top _ _)
      (Eventually.of_forall hboundG)
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul hB, ofReal_measureReal] at h
  exact h

/-- The common original global target remains common after restricting that
target physically to the same set. -/
theorem snd_actual_target_restriction (Γ : Measure (X × X)) (H : Set X)
    (hH : MeasurableSet H) :
    (Γ.restrict (univ ×ˢ H)).snd = Γ.snd.restrict H := by
  unfold Measure.snd
  rw [Measure.restrict_map measurable_snd hH]
  congr 1
  congr 1
  ext p
  simp

end Restriction

section RootedCrossing
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

/-- Rooting preserves the same physical crossing estimate for a compact target
test, paying only crossing-plan mass in the actual rooted target window. -/
theorem ofReal_abs_rooted_source_restrict_sub_target_restrict_le_crossing
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ] (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N) (z : ι → ℝ)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hfU : ∀ y ∈ tsupport f, y.1 ∈ U) :
    ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γ.restrict (univ ×ˢ H)) coord u N z| ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        physicalSceneRootedPlan (Γ.restrict (physicalSceneCoreCrossing H)) coord u N z
          {e | e.2.1 ∈ U} := by
  let F := fun p : M × M ↦ f (coord p.2 - z, u p.2)
  let W := {p : M × M | coord p.2 - z ∈ U}
  have hF : Measurable F := f.continuous.measurable.comp
    (((hcoord.comp measurable_snd).sub measurable_const).prodMk (hu.comp measurable_snd))
  have hzero : ∀ p, p ∉ W → F p = 0 := by
    intro p hp
    by_contra hn
    exact hp (hfU _ (subset_tsupport f hn))
  have hphysical := ofReal_abs_source_restrict_sub_target_restrict_le_crossing
    Γ H hH F hF ‖f.toBoundedContinuousFunction‖ (norm_nonneg _)
    (fun p ↦ f.toBoundedContinuousFunction.norm_coe_le_norm _) W hzero
  have hobs := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have hread (Q : Set (M × M)) :
      (∫ e, f e.2 ∂physicalSceneRootedPlan (Γ.restrict Q) coord u N z) =
        N * ∫ p, F p ∂Γ.restrict Q := by
    unfold physicalSceneRootedPlan
    rw [integral_smul_measure, integral_map (f := fun e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦ f e.2)
      hobs.aemeasurable (f.continuous.comp continuous_snd).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hN.le, smul_eq_mul]
    rfl
  have hW : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U} :=
    hU.preimage measurable_snd.fst
  have hmass : physicalSceneRootedPlan (Γ.restrict (physicalSceneCoreCrossing H))
      coord u N z {e | e.2.1 ∈ U} =
        ENNReal.ofReal N * Γ (physicalSceneCoreCrossing H ∩ W) := by
    unfold physicalSceneRootedPlan
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hobs hW,
      Measure.restrict_apply (hW.preimage hobs)]
    congr 1
    rw [inter_comm]
    rfl
  calc
    _ = ENNReal.ofReal N * ENNReal.ofReal
        |(∫ p, F p ∂Γ.restrict (H ×ˢ univ)) -
          ∫ p, F p ∂Γ.restrict (univ ×ˢ H)| := by
      rw [hread, hread, ← mul_sub, abs_mul, abs_of_pos hN, ENNReal.ofReal_mul hN.le]
    _ ≤ ENNReal.ofReal N * (ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        Γ (physicalSceneCoreCrossing H ∩ W)) := mul_le_mul_right hphysical _
    _ = _ := by rw [hmass]; ac_rfl


/-- Equal original global targets cancel after restriction of the target
physically to the same set.  Only the two actual crossing plans remain. -/
theorem ofReal_abs_rooted_source_restricted_target_tests_le_crossing
    (Γplus Γminus : Measure (M × M)) [IsFiniteMeasure Γplus] [IsFiniteMeasure Γminus]
    (htarget : Γplus.snd = Γminus.snd) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N) (z : ι → ℝ)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hfU : ∀ y ∈ tsupport f, y.1 ∈ U) :
    ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan (Γplus.restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γminus.restrict (H ×ˢ univ)) coord u N z| ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (physicalSceneRootedPlan (Γplus.restrict (physicalSceneCoreCrossing H)) coord u N z
          {e | e.2.1 ∈ U} +
        physicalSceneRootedPlan (Γminus.restrict (physicalSceneCoreCrossing H)) coord u N z
          {e | e.2.1 ∈ U}) := by
  have hrestricted : (Γplus.restrict (univ ×ˢ H)).snd =
      (Γminus.restrict (univ ×ˢ H)).snd := by
    rw [snd_actual_target_restriction Γplus H hH,
      snd_actual_target_restriction Γminus H hH, htarget]
  have hroot : (physicalSceneRootedPlan (Γplus.restrict (univ ×ˢ H)) coord u N z).snd =
      (physicalSceneRootedPlan (Γminus.restrict (univ ×ˢ H)) coord u N z).snd := by
    rw [(physicalSceneRootedPlan_marginals _ coord hcoord u hu N z).2,
      (physicalSceneRootedPlan_marginals _ coord hcoord u hu N z).2, hrestricted]
  have htest :
      (∫ e, f e.2 ∂physicalSceneRootedPlan (Γplus.restrict (univ ×ˢ H)) coord u N z) =
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γminus.restrict (univ ×ˢ H)) coord u N z := by
    have hp := integral_map (μ := physicalSceneRootedPlan (Γplus.restrict (univ ×ˢ H)) coord u N z)
      (f := fun y ↦ f y) measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    have hm := integral_map (μ := physicalSceneRootedPlan (Γminus.restrict (univ ×ˢ H)) coord u N z)
      (f := fun y ↦ f y) measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    exact hp.symm.trans ((congrArg (fun ν : Measure ((ι → ℝ) × ℝ) ↦ ∫ y, f y ∂ν) hroot).trans hm)
  have htri := abs_sub_le
    (∫ e, f e.2 ∂physicalSceneRootedPlan (Γplus.restrict (H ×ˢ univ)) coord u N z)
    (∫ e, f e.2 ∂physicalSceneRootedPlan (Γplus.restrict (univ ×ˢ H)) coord u N z)
    (∫ e, f e.2 ∂physicalSceneRootedPlan (Γminus.restrict (H ×ˢ univ)) coord u N z)
  have hsecond :
      |(∫ e, f e.2 ∂physicalSceneRootedPlan (Γplus.restrict (univ ×ˢ H)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γminus.restrict (H ×ˢ univ)) coord u N z| =
      |(∫ e, f e.2 ∂physicalSceneRootedPlan (Γminus.restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γminus.restrict (univ ×ˢ H)) coord u N z| := by
    rw [htest, abs_sub_comm]
  rw [hsecond] at htri
  have h := ENNReal.ofReal_le_ofReal htri
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at h
  apply h.trans
  rw [mul_add]
  exact add_le_add
    (ofReal_abs_rooted_source_restrict_sub_target_restrict_le_crossing
      Γplus H hH coord hcoord u hu N hN z f U hU hfU)
    (ofReal_abs_rooted_source_restrict_sub_target_restrict_le_crossing
      Γminus H hH coord hcoord u hu N hN z f U hU hfU)

/-- Haar averaging pays the actual source-restricted target-test difference
only by the original crossing masses. -/
theorem lintegral_rooted_source_restricted_target_tests_le_crossing
    (Γplus Γminus : Measure (M × M)) [IsFiniteMeasure Γplus] [IsFiniteMeasure Γminus]
    (htarget : Γplus.snd = Γminus.snd) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (hfU : ∀ y ∈ tsupport f, y.1 ∈ U) :
    (∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan (Γplus.restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γminus.restrict (H ×ˢ univ)) coord u N z|
      ∂cavityRootMeasure volume D N) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U *
        (Γplus (physicalSceneCoreCrossing H) + Γminus (physicalSceneCoreCrossing H)) := by
  let W : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) := {e | e.2.1 ∈ U}
  have hW : MeasurableSet W := hU.preimage measurable_snd.fst
  have hm (Γ : Measure (M × M)) [IsFiniteMeasure Γ] :
      Measurable (fun z : ι → ℝ ↦ physicalSceneRootedPlan Γ coord u N z W) := by
    exact (Measure.measurable_coe hW).comp
      ((measurable_joint_physicalSceneRootedPlan (fun _ : Unit ↦ Γ)
        measurable_const coord hcoord u hu N).comp
        (show Measurable (fun z : ι → ℝ ↦ ((), z)) from measurable_const.prodMk measurable_id))
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (physicalSceneRootedPlan (Γplus.restrict (physicalSceneCoreCrossing H)) coord u N z W +
          physicalSceneRootedPlan (Γminus.restrict (physicalSceneCoreCrossing H)) coord u N z W)
      ∂cavityRootMeasure volume D N := lintegral_mono fun z ↦
        ofReal_abs_rooted_source_restricted_target_tests_le_crossing
          Γplus Γminus htarget H hH coord hcoord u hu N hN z f U hU hfU
    _ = ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((∫⁻ z, physicalSceneRootedPlan (Γplus.restrict (physicalSceneCoreCrossing H)) coord u N z W
          ∂cavityRootMeasure volume D N) +
        ∫⁻ z, physicalSceneRootedPlan (Γminus.restrict (physicalSceneCoreCrossing H)) coord u N z W
          ∂cavityRootMeasure volume D N) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (hm (Γplus.restrict (physicalSceneCoreCrossing H))) _]
    _ ≤ ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (volume U * Γplus (physicalSceneCoreCrossing H) +
          volume U * Γminus (physicalSceneCoreCrossing H)) := by
      apply mul_le_mul_right
      apply add_le_add
      · simpa only [Measure.restrict_apply_univ] using
          lintegral_physicalSceneRootedPlan_targetWindow_le
            (Γplus.restrict (physicalSceneCoreCrossing H)) coord hcoord u hu N hN D U hU
      · simpa only [Measure.restrict_apply_univ] using
          lintegral_physicalSceneRootedPlan_targetWindow_le
            (Γminus.restrict (physicalSceneCoreCrossing H)) coord hcoord u hu N hN D U hU
    _ = _ := by ring


/-- The expected target-test defect is charged to the expected actual crossing
mass of the two measurable original plan families. -/
theorem lintegral_rooted_source_restricted_target_tests_le_expected_crossing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (htarget : ∀ᵐ w ∂P, (Γplus w).snd = (Γminus w).snd)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (hfU : ∀ y ∈ tsupport f, y.1 ∈ U)
    (Ccross : ℝ≥0∞)
    (hmass : (∫⁻ w, Γplus w (physicalSceneCoreCrossing H) +
        Γminus w (physicalSceneCoreCrossing H) ∂P) ≤ Ccross) :
    (∫⁻ w, ∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan ((Γplus w).restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan ((Γminus w).restrict (H ×ˢ univ)) coord u N z|
      ∂cavityRootMeasure volume D N ∂P) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U * Ccross := by
  have hcross := measurableSet_physicalSceneCoreCrossing hH
  have hsum : Measurable (fun w ↦ Γplus w (physicalSceneCoreCrossing H) +
      Γminus w (physicalSceneCoreCrossing H)) :=
    ((Measure.measurable_coe hcross).comp hplus).add
      ((Measure.measurable_coe hcross).comp hminus)
  calc
    _ ≤ ∫⁻ w, (ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U) *
        (Γplus w (physicalSceneCoreCrossing H) + Γminus w (physicalSceneCoreCrossing H)) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [htarget] with w hw
      exact lintegral_rooted_source_restricted_target_tests_le_crossing
        (Γplus w) (Γminus w) hw H hH coord hcoord u hu N hN D U hU f hfU
    _ = (ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U) *
        ∫⁻ w, Γplus w (physicalSceneCoreCrossing H) + Γminus w (physicalSceneCoreCrossing H) ∂P :=
      lintegral_const_mul _ hsum
    _ ≤ _ := mul_le_mul_right hmass _

/-- Original feasibility gives the common global target internally.  An actual
physical event covering crossings on the original carriers then pays the full
source-restricted target-test defect, with no target-column replacement. -/
theorem lintegral_actualAllocation_rooted_target_tests_le_covering_event
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aplus w))
    (hfm : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aminus w))
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hYB : ∀ᵐ w ∂P, ∀ j, Y w j ∈ B)
    (H : Set M) (hH : MeasurableSet H) (Q : Set (M × M))
    (hcover : (A ×ˢ B) ∩ physicalSceneCoreCrossing H ⊆ Q)
    (C : ℝ≥0∞)
    (hmassplus : (∫⁻ w, physicalSceneGlobalAllocationFamily μ aplus Y w Q ∂P) ≤ C)
    (hmassminus : (∫⁻ w, physicalSceneGlobalAllocationFamily μ aminus Y w Q ∂P) ≤ C)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (hfU : ∀ y ∈ tsupport f, y.1 ∈ U) :
    (∫⁻ w, ∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ)) coord u N z|
      ∂cavityRootMeasure volume D N ∂P) ≤
      2 * ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U * C := by
  let Γplus := physicalSceneGlobalAllocationFamily μ aplus Y
  let Γminus := physicalSceneGlobalAllocationFamily μ aminus Y
  have hp : Measurable Γplus := measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY
  have hm : Measurable Γminus := measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY
  have htarget : ∀ᵐ w ∂P, (Γplus w).snd = (Γminus w).snd := by
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ aplus Y p hfp,
      physicalSceneGlobalAllocationFamily_ae_eq P μ aminus Y p hfm, hfp, hfm]
      with w hwp hwm hpa hma
    change Γplus w = _ at hwp
    change Γminus w = _ at hwm
    rw [hwp, hwm, physicalSceneAllocationPlan_snd hpa, physicalSceneAllocationPlan_snd hma]
  have hcarriedplus := ae_physicalSceneGlobalAllocationFamily_carried P μ aplus Y p
    hfp hA hB hμA hYB
  have hcarriedminus := ae_physicalSceneGlobalAllocationFamily_carried P μ aminus Y p
    hfm hA hB hμA hYB
  have hcp : (∫⁻ w, Γplus w (physicalSceneCoreCrossing H) ∂P) ≤ C := by
    apply le_trans (lintegral_mono_ae ?_) hmassplus
    filter_upwards [hcarriedplus] with w hw
    exact measure_mono_ae (hw.mono fun e he hc ↦ hcover ⟨he, hc⟩)
  have hcm : (∫⁻ w, Γminus w (physicalSceneCoreCrossing H) ∂P) ≤ C := by
    apply le_trans (lintegral_mono_ae ?_) hmassminus
    filter_upwards [hcarriedminus] with w hw
    exact measure_mono_ae (hw.mono fun e he hc ↦ hcover ⟨he, hc⟩)
  have hmass : (∫⁻ w, Γplus w (physicalSceneCoreCrossing H) +
      Γminus w (physicalSceneCoreCrossing H) ∂P) ≤ C + C := by
    rw [lintegral_add_left (f := fun w ↦ Γplus w (physicalSceneCoreCrossing H))
      ((Measure.measurable_coe (measurableSet_physicalSceneCoreCrossing hH)).comp hp) _]
    exact add_le_add hcp hcm
  exact (lintegral_rooted_source_restricted_target_tests_le_expected_crossing
    P Γplus Γminus hp hm htarget H hH coord hcoord u hu N hN D U hU f hfU (C + C) hmass).trans_eq
      (by ring)

end RootedCrossing
end OTSelector.Reconstruction
