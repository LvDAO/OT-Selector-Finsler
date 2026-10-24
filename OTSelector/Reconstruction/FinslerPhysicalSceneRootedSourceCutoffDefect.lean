import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMarginals
import OTSelector.MeasureTheory.CompactProductMarginalTests

/-!
# Actual source-cutoff defects from original feasible allocations

A genuine compact target cutoff loses only actual target escape mass.  The two
original allocations give their common full source marginal internally, after
the same physical source restriction and actual rooted observation.
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

/-- The finite-plan cutoff defect in extended nonnegative reals is paid by the
two actual escape masses from the retained target set. -/
theorem ofReal_abs_product_tests_sub_le_common_source_tails
    (πplus πminus : Measure (X × Y)) [IsFiniteMeasure πplus] [IsFiniteMeasure πminus]
    (hsource : πplus.fst = πminus.fst) (f : C_c(X, ℝ)) (g : C_c(Y, ℝ))
    (hg : ∀ y, g y ∈ Icc 0 1) (K : Set Y) (hgK : EqOn g 1 K) :
    ENNReal.ofReal |(∫ e, cavityProductTest f g e ∂πplus) -
      ∫ e, cavityProductTest f g e ∂πminus| ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (πplus (tsupport f ×ˢ Kᶜ) + πminus (tsupport f ×ˢ Kᶜ)) := by
  have hint (π : Measure (X × Y)) [IsFiniteMeasure π] :
      Integrable (fun e : X × Y ↦ f e.1) π :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (Eventually.of_forall fun e ↦
        f.toBoundedContinuousFunction.norm_coe_le_norm e.1)
  have hb := abs_product_tests_sub_le_common_source_tails πplus πminus f g hsource
    (hint πplus) (hint πminus) hg K hgK (measure_lt_top _ _) (measure_lt_top _ _)
  have h := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
    ofReal_measureReal, ofReal_measureReal] at h
  exact h

end Deterministic

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω] {n : ℕ}

/-- The same original feasible allocations produce the rooted compact-test
bound, with the common source marginal derived internally and their actual
random restricted columns and escape masses retained exactly. -/
theorem lintegral_actualAllocation_rooted_source_cutoff_defect_le_escape
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aplus w))
    (hfm : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aminus w))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (f g : C_c((ι → ℝ) × ℝ, ℝ)) (hg : ∀ y, g y ∈ Icc 0 1)
    (K : Set ((ι → ℝ) × ℝ)) (hK : MeasurableSet K) (hgK : EqOn g 1 K) :
    let πplus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ)) coord u N z
    let πminus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ)) coord u N z
    (∫⁻ w, ∫⁻ z, ENNReal.ofReal |(∫ e, cavityProductTest f g e ∂πplus w z) -
        ∫ e, cavityProductTest f g e ∂πminus w z|
      ∂cavityRootMeasure volume D N ∂P) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((∫⁻ w, ∫⁻ z, πplus w z (tsupport f ×ˢ Kᶜ) ∂cavityRootMeasure volume D N ∂P) +
          ∫⁻ w, ∫⁻ z, πminus w z (tsupport f ×ˢ Kᶜ) ∂cavityRootMeasure volume D N ∂P) := by
  let Γp := physicalSceneGlobalAllocationFamily μ aplus Y
  let Γm := physicalSceneGlobalAllocationFamily μ aminus Y
  let πplus := fun w z ↦ physicalSceneRootedPlan ((Γp w).restrict (H ×ˢ univ)) coord u N z
  let πminus := fun w z ↦ physicalSceneRootedPlan ((Γm w).restrict (H ×ˢ univ)) coord u N z
  let T := tsupport f ×ˢ Kᶜ
  have hT : MeasurableSet T := (isClosed_tsupport f).measurableSet.prod hK.compl
  have : IsProbabilityMeasure (cavityRootMeasure volume D N) :=
    isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have hmeasp : Measurable (fun v : Ω × (ι → ℝ) ↦ πplus v.1 v.2 T) :=
    (Measure.measurable_coe hT).comp
      (measurable_joint_physicalSceneRootedPlan
        (fun w ↦ (Γp w).restrict (H ×ˢ univ))
        (measurable_physicalPlan_sourceRestriction Γp
          (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY) H hH)
        coord hcoord u hu N)
  have hmeasm : Measurable (fun v : Ω × (ι → ℝ) ↦ πminus v.1 v.2 T) :=
    (Measure.measurable_coe hT).comp
      (measurable_joint_physicalSceneRootedPlan
        (fun w ↦ (Γm w).restrict (H ×ˢ univ))
        (measurable_physicalPlan_sourceRestriction Γm
          (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY) H hH)
        coord hcoord u hu N)
  have hsrc : ∀ᵐ w ∂P, ∀ z,
      (πplus w z).fst = (πminus w z).fst := by
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ aplus Y p hfp,
      physicalSceneGlobalAllocationFamily_ae_eq P μ aminus Y p hfm, hfp, hfm]
      with w hwp hwm hpa hma z
    change Γp w = _ at hwp
    change Γm w = _ at hwm
    change (physicalSceneRootedPlan ((Γp w).restrict (H ×ˢ univ)) coord u N z).fst =
      (physicalSceneRootedPlan ((Γm w).restrict (H ×ˢ univ)) coord u N z).fst
    rw [hwp, hwm, ← physicalSceneAllocationPlan_restrict μ (aplus w) (Y w) hH,
      ← physicalSceneAllocationPlan_restrict μ (aminus w) (Y w) hH]
    exact (physicalSceneRootedPlan_source_restrict_marginals hpa (Y w)
      H coord hcoord u hu N z).1.trans
      (physicalSceneRootedPlan_source_restrict_marginals hma (Y w)
        H coord hcoord u hu N z).1.symm
  have hb : ∀ᵐ w ∂P, ∀ z,
      ENNReal.ofReal |(∫ e, cavityProductTest f g e ∂πplus w z) -
        ∫ e, cavityProductTest f g e ∂πminus w z| ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (πplus w z T + πminus w z T) := by
    filter_upwards [hsrc] with w hw z
    have := isFiniteMeasure_physicalSceneRootedPlan ((Γp w).restrict (H ×ˢ univ)) coord u N z
    have := isFiniteMeasure_physicalSceneRootedPlan ((Γm w).restrict (H ×ˢ univ)) coord u N z
    exact ofReal_abs_product_tests_sub_le_common_source_tails
      (πplus w z) (πminus w z) (hw z) f g hg K hgK
  calc
    _ ≤ ∫⁻ w, ∫⁻ z, ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (πplus w z T + πminus w z T) ∂cavityRootMeasure volume D N ∂P :=
      lintegral_mono_ae (hb.mono fun w hw ↦ lintegral_mono hw)
    _ = ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ∫⁻ w, ∫⁻ z, πplus w z T + πminus w z T ∂cavityRootMeasure volume D N ∂P := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
      congr 1
      calc
        _ = ∫⁻ w, (∫⁻ z, πplus w z T ∂cavityRootMeasure volume D N) +
            ∫⁻ z, πminus w z T ∂cavityRootMeasure volume D N ∂P := by
          apply lintegral_congr
          intro w
          exact lintegral_add_left (hmeasp.comp
            (show Measurable (fun z : ι → ℝ ↦ (w, z)) from
              measurable_const.prodMk measurable_id)) _
        _ = _ := lintegral_add_right _ hmeasm.lintegral_prod_right'


local instance sourceCutoffDefectPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The same producer written directly under the actual pair scene law,
ready for the compact-test weak-limit bounds. -/
theorem lintegral_actualAllocationRootedSceneLaw_source_cutoff_defect_le_escape
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aplus w))
    (hfm : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aminus w))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (f g : C_c((ι → ℝ) × ℝ, ℝ)) (hg : ∀ y, g y ∈ Icc 0 1)
    (K : Set ((ι → ℝ) × ℝ)) (hK : MeasurableSet K) (hgK : EqOn g 1 K) :
    let πplus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ)) coord u N z
    let πminus := fun w z ↦ physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ)) coord u N z
    (∫⁻ scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ),
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1 (cavityProductTest f g) -
        LocalFiniteMeasure.testIntegral scene.2 (cavityProductTest f g)|
      ∂(actualAllocationRootedSceneLaw P μ aplus aminus hplus hminus Y hY H hH
        coord hcoord u hu N hN D hD :
          Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((∫⁻ w, ∫⁻ z, πplus w z (tsupport f ×ˢ Kᶜ) ∂cavityRootMeasure volume D N ∂P) +
          ∫⁻ w, ∫⁻ z, πminus w z (tsupport f ×ˢ Kᶜ) ∂cavityRootMeasure volume D N ∂P) := by
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
    (fun scene ↦ ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1 (cavityProductTest f g) -
      LocalFiniteMeasure.testIntegral scene.2 (cavityProductTest f g)|)
    ((((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)).abs.measurable.ennreal_ofReal)
  exact hread.trans_le
    (lintegral_actualAllocation_rooted_source_cutoff_defect_le_escape
      P μ aplus aminus hplus hminus Y hY p hfp hfm H hH coord hcoord u hu
      N hN D hD f g hg K hK hgK)

end OTSelector.Reconstruction
