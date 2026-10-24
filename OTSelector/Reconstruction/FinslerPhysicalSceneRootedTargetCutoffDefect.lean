import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceCutoffDefect

/-!
# Target compact product tests retain their actual finite defect

A compact source cutoff approximates a target test. Its two actual escape
masses pay the cutoff error, while the original untruncated target-test defect
remains explicit. The same inequality is read directly under the actual pair
scene law, without assuming common restricted target columns.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Deterministic
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- Cutting off the source in a target test loses only the actual source
escape mass over that target test's compact support. -/
theorem abs_integral_target_sub_product_le_finite_tail
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (g : C_c(X, ℝ)) (f : C_c(Y, ℝ)) (hg : ∀ x, g x ∈ Icc 0 1)
    (K : Set X) (hgK : EqOn g 1 K) :
    |(∫ e, f e.2 ∂π) - ∫ e, cavityProductTest g f e ∂π| ≤
      ‖f.toBoundedContinuousFunction‖ * π.real (Kᶜ ×ˢ tsupport f) := by
  have hf : Integrable (fun e : X × Y ↦ f e.2) π :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (Eventually.of_forall fun e ↦
        f.toBoundedContinuousFunction.norm_coe_le_norm e.2)
  have hprod : Integrable (fun e ↦ cavityProductTest g f e) π := by
    change Integrable (fun e : X × Y ↦ g e.1 * f e.2) π
    exact hf.bdd_mul (g.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun e ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg e.1).1]
        exact (hg e.1).2)
  rw [← integral_sub hf hprod]
  have hz : ∀ e : X × Y, e ∉ Kᶜ ×ˢ tsupport f → f e.2 - cavityProductTest g f e = 0 := by
    intro e he
    by_cases hy : e.2 ∈ tsupport f
    · have hx : e.1 ∈ K := by
        by_contra hn
        exact he ⟨hn, hy⟩
      change f e.2 - g e.1 * f e.2 = 0
      rw [hgK hx]
      simp
    · change f e.2 - g e.1 * f e.2 = 0
      rw [image_eq_zero_of_notMem_tsupport hy]
      simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  simpa only [Real.norm_eq_abs] using norm_setIntegral_le_of_norm_le_const_ae
    (μ := π) (s := Kᶜ ×ˢ tsupport f) (f := fun e ↦ f e.2 - cavityProductTest g f e)
    (measure_lt_top _ _) (Eventually.of_forall fun e ↦ by
      change ‖f e.2 - g e.1 * f e.2‖ ≤ ‖f.toBoundedContinuousFunction‖
      have heq : f e.2 - g e.1 * f e.2 = (1 - g e.1) * f e.2 := by ring
      rw [heq, norm_mul]
      have hfactor : ‖1 - g e.1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hg e.1).2)]
        linarith [(hg e.1).1]
      exact (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans
        (by simpa using f.toBoundedContinuousFunction.norm_coe_le_norm e.2))

/-- The actual untruncated target-test defect and the two actual source escape
masses bound the compact product-test defect. -/
theorem ofReal_abs_product_tests_sub_le_target_defect_and_tails
    (πplus πminus : Measure (X × Y)) [IsFiniteMeasure πplus] [IsFiniteMeasure πminus]
    (g : C_c(X, ℝ)) (f : C_c(Y, ℝ)) (hg : ∀ x, g x ∈ Icc 0 1)
    (K : Set X) (hgK : EqOn g 1 K) :
    ENNReal.ofReal |(∫ e, cavityProductTest g f e ∂πplus) -
      ∫ e, cavityProductTest g f e ∂πminus| ≤
      ENNReal.ofReal |(∫ e, f e.2 ∂πplus) - ∫ e, f e.2 ∂πminus| +
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (πplus (Kᶜ ×ˢ tsupport f) + πminus (Kᶜ ×ˢ tsupport f)) := by
  have hp := abs_integral_target_sub_product_le_finite_tail πplus g f hg K hgK
  have hm := abs_integral_target_sub_product_le_finite_tail πminus g f hg K hgK
  let Fp := ∫ e : X × Y, f e.2 ∂πplus
  let Fm := ∫ e : X × Y, f e.2 ∂πminus
  let Tp := ∫ e, cavityProductTest g f e ∂πplus
  let Tm := ∫ e, cavityProductTest g f e ∂πminus
  have hreal : |Tp - Tm| ≤ |Fp - Fm| + ‖f.toBoundedContinuousFunction‖ *
      (πplus.real (Kᶜ ×ˢ tsupport f) + πminus.real (Kᶜ ×ˢ tsupport f)) := by
    have htri := (abs_sub_le Tp Fp Tm).trans
      (add_le_add le_rfl (abs_sub_le Fp Fm Tm))
    rw [abs_sub_comm Tp Fp] at htri
    rw [mul_add]
    linarith
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg (norm_nonneg _) (add_nonneg
      measureReal_nonneg measureReal_nonneg)), ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
    ofReal_measureReal, ofReal_measureReal] at h
  exact h

end Deterministic

/-- A measurable pair of escape observables may be split off even when the
first nonnegative defect is not assumed measurable. -/
theorem lintegral_lintegral_defect_add_escape
    {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (P : Measure W) (Q : Measure Z) [SFinite Q]
    (F ep em : W → Z → ℝ≥0∞)
    (hp : Measurable (fun v : W × Z ↦ ep v.1 v.2))
    (hm : Measurable (fun v : W × Z ↦ em v.1 v.2))
    (c : ℝ≥0∞) (hc : c ≠ ∞) :
    (∫⁻ w, ∫⁻ z, F w z + c * (ep w z + em w z) ∂Q ∂P) =
      (∫⁻ w, ∫⁻ z, F w z ∂Q ∂P) +
        c * ((∫⁻ w, ∫⁻ z, ep w z ∂Q ∂P) + ∫⁻ w, ∫⁻ z, em w z ∂Q ∂P) := by
  have hs : Measurable (fun v : W × Z ↦ c * (ep v.1 v.2 + em v.1 v.2)) :=
    (hp.add hm).const_mul c
  calc
    _ = ∫⁻ w, (∫⁻ z, F w z ∂Q) + ∫⁻ z, c * (ep w z + em w z) ∂Q ∂P := by
      apply lintegral_congr
      intro w
      exact lintegral_add_right (F w) (hs.comp (measurable_const.prodMk measurable_id))
    _ = (∫⁻ w, ∫⁻ z, F w z ∂Q ∂P) + ∫⁻ w, ∫⁻ z, c * (ep w z + em w z) ∂Q ∂P :=
      lintegral_add_right _ hs.lintegral_prod_right'
    _ = _ := by
      congr 1
      simp_rw [lintegral_const_mul' _ _ hc]
      congr 1
      calc
        _ = ∫⁻ w, (∫⁻ z, ep w z ∂Q) + ∫⁻ z, em w z ∂Q ∂P := by
          apply lintegral_congr
          intro w
          exact lintegral_add_left (hp.comp (measurable_const.prodMk measurable_id)) _
        _ = _ := lintegral_add_right _ hm.lintegral_prod_right'

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω] {n : ℕ}

set_option maxHeartbeats 400000 in
/-- The original finite families give the expected target compact product-test
bound. No equality of their actual source-restricted target columns is assumed. -/
theorem lintegral_actualAllocation_rooted_target_cutoff_defect_le_target_defect_escape
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (g f : C_c((ι → ℝ) × ℝ, ℝ)) (hg : ∀ x, g x ∈ Icc 0 1)
    (K : Set ((ι → ℝ) × ℝ)) (hK : MeasurableSet K) (hgK : EqOn g 1 K) :
    let πplus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ)) coord u N z
    let πminus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ)) coord u N z
    (∫⁻ w, ∫⁻ z, ENNReal.ofReal |(∫ e, cavityProductTest g f e ∂πplus w z) -
        ∫ e, cavityProductTest g f e ∂πminus w z| ∂cavityRootMeasure volume D N ∂P) ≤
      (∫⁻ w, ∫⁻ z, ENNReal.ofReal |(∫ e, f e.2 ∂πplus w z) -
        ∫ e, f e.2 ∂πminus w z| ∂cavityRootMeasure volume D N ∂P) +
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((∫⁻ w, ∫⁻ z, πplus w z (Kᶜ ×ˢ tsupport f) ∂cavityRootMeasure volume D N ∂P) +
          ∫⁻ w, ∫⁻ z, πminus w z (Kᶜ ×ˢ tsupport f) ∂cavityRootMeasure volume D N ∂P) := by
  let Γp := physicalSceneGlobalAllocationFamily μ aplus Y
  let Γm := physicalSceneGlobalAllocationFamily μ aminus Y
  let πplus := fun w z ↦ physicalSceneRootedPlan ((Γp w).restrict (H ×ˢ univ)) coord u N z
  let πminus := fun w z ↦ physicalSceneRootedPlan ((Γm w).restrict (H ×ˢ univ)) coord u N z
  let T := Kᶜ ×ˢ tsupport f
  have hT : MeasurableSet T := hK.compl.prod (isClosed_tsupport f).measurableSet
  have : IsProbabilityMeasure (cavityRootMeasure volume D N) :=
    isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have hmeasp : Measurable (fun v : Ω × (ι → ℝ) ↦ πplus v.1 v.2 T) :=
    (Measure.measurable_coe hT).comp
      (measurable_joint_physicalSceneRootedPlan (fun w ↦ (Γp w).restrict (H ×ˢ univ))
        (measurable_physicalPlan_sourceRestriction Γp
          (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY) H hH)
        coord hcoord u hu N)
  have hmeasm : Measurable (fun v : Ω × (ι → ℝ) ↦ πminus v.1 v.2 T) :=
    (Measure.measurable_coe hT).comp
      (measurable_joint_physicalSceneRootedPlan (fun w ↦ (Γm w).restrict (H ×ˢ univ))
        (measurable_physicalPlan_sourceRestriction Γm
          (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY) H hH)
        coord hcoord u hu N)
  have hb (w : Ω) (z : ι → ℝ) := by
    have := isFiniteMeasure_physicalSceneRootedPlan ((Γp w).restrict (H ×ˢ univ)) coord u N z
    have := isFiniteMeasure_physicalSceneRootedPlan ((Γm w).restrict (H ×ˢ univ)) coord u N z
    exact ofReal_abs_product_tests_sub_le_target_defect_and_tails
      (πplus w z) (πminus w z) g f hg K hgK
  calc
    _ ≤ ∫⁻ w, ∫⁻ z,
        ENNReal.ofReal |(∫ e, f e.2 ∂πplus w z) - ∫ e, f e.2 ∂πminus w z| +
        ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * (πplus w z T + πminus w z T)
        ∂cavityRootMeasure volume D N ∂P := lintegral_mono fun w ↦ lintegral_mono fun z ↦ hb w z
    _ = _ := lintegral_lintegral_defect_add_escape P (cavityRootMeasure volume D N)
      (fun w z ↦ ENNReal.ofReal |(∫ e, f e.2 ∂πplus w z) - ∫ e, f e.2 ∂πminus w z|)
      (fun w z ↦ πplus w z T) (fun w z ↦ πminus w z T) hmeasp hmeasm
      (ENNReal.ofReal ‖f.toBoundedContinuousFunction‖) ENNReal.ofReal_ne_top



local instance targetProductCutoffDefectPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

set_option maxHeartbeats 400000 in
/-- The target compact product-test estimate under the actual pair scene law.
The actual original untruncated target defect is preserved on the right. -/
theorem lintegral_actualAllocationRootedSceneLaw_target_cutoff_defect_le_target_defect_escape
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (g f : C_c((ι → ℝ) × ℝ, ℝ)) (hg : ∀ x, g x ∈ Icc 0 1)
    (K : Set ((ι → ℝ) × ℝ)) (hK : MeasurableSet K) (hgK : EqOn g 1 K) :
    let πplus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ)) coord u N z
    let πminus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ)) coord u N z
    (∫⁻ scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ),
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1 (cavityProductTest g f) -
        LocalFiniteMeasure.testIntegral scene.2 (cavityProductTest g f)|
      ∂(actualAllocationRootedSceneLaw P μ aplus aminus hplus hminus Y hY H hH
        coord hcoord u hu N hN D hD :
          Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤
      (∫⁻ w, ∫⁻ z, ENNReal.ofReal |(∫ e, f e.2 ∂πplus w z) -
        ∫ e, f e.2 ∂πminus w z| ∂cavityRootMeasure volume D N ∂P) +
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((∫⁻ w, ∫⁻ z, πplus w z (Kᶜ ×ˢ tsupport f) ∂cavityRootMeasure volume D N ∂P) +
          ∫⁻ w, ∫⁻ z, πminus w z (Kᶜ ×ˢ tsupport f) ∂cavityRootMeasure volume D N ∂P) := by
  let Γp := fun w ↦ (physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ)
  let Γm := fun w ↦ (physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ)
  have hp := measurable_physicalPlan_sourceRestriction
    (physicalSceneGlobalAllocationFamily μ aplus Y)
    (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY) H hH
  have hm := measurable_physicalPlan_sourceRestriction
    (physicalSceneGlobalAllocationFamily μ aminus Y)
    (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY) H hH
  have hread := lintegral_physicalSceneRootedLocalSceneLaw P Γp Γm hp hm
    coord hcoord u hu N hN D hD
    (fun scene ↦ ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1 (cavityProductTest g f) -
      LocalFiniteMeasure.testIntegral scene.2 (cavityProductTest g f)|)
    ((((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)).abs.measurable.ennreal_ofReal)
  exact hread.trans_le
    (lintegral_actualAllocation_rooted_target_cutoff_defect_le_target_defect_escape
      P μ aplus aminus hplus hminus Y hY H hH coord hcoord u hu N hN D hD g f hg K hK hgK)

end OTSelector.Reconstruction
