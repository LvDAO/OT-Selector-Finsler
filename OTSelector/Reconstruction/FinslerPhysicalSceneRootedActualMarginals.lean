import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCountable
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMarginals
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetMass

/-!
# Actual common source marginals and target restriction defects

The same original feasible allocations produce exact common full source
marginals at finite rooted scenes. Their realized restricted target columns
have a quantitative defect controlled by the original discarded source mass.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
  OTSelector.Probability
open scoped Topology ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section FiniteProjection

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
  [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace X] [SigmaCompactSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

local instance actualFiniteSourcePlanPolish : PolishSpace (LocalFiniteMeasure (X × Y)) :=
  LocalFiniteMeasure.instPolishSpace
local instance actualFiniteSourceMarginalPolish : PolishSpace (LocalFiniteMeasure X) :=
  LocalFiniteMeasure.instPolishSpace

/-- The full source projection on the finite-plan event, with zero completion
only outside that event. -/
def finitePlanSourceProjection (π : LocalFiniteMeasure (X × Y)) : LocalFiniteMeasure X := by
  by_cases h : (π : Measure (X × Y)) univ < ⊤
  · have : IsFiniteMeasure (π : Measure (X × Y)) := ⟨h⟩
    exact ⟨(π : Measure (X × Y)).fst, inferInstance⟩
  · exact ⟨0, inferInstance⟩

theorem coe_finitePlanSourceProjection (π : LocalFiniteMeasure (X × Y)) :
    (finitePlanSourceProjection π : Measure X) =
      if (π : Measure (X × Y)) univ < ⊤ then (π : Measure (X × Y)).fst else 0 := by
  by_cases h : (π : Measure (X × Y)) univ < ⊤ <;>
    simp [finitePlanSourceProjection, h]

theorem measurable_finitePlanSourceProjection :
    Measurable (finitePlanSourceProjection : LocalFiniteMeasure (X × Y) → LocalFiniteMeasure X) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  have hmass : Measurable (fun π : LocalFiniteMeasure (X × Y) ↦
      (π : Measure (X × Y)) univ) :=
    (LocalFiniteMeasure.lowerSemicontinuous_measure_open isOpen_univ).measurable
  have hopen (U : Set X) (hU : IsOpen U) : Measurable (fun π : LocalFiniteMeasure (X × Y) ↦
      (finitePlanSourceProjection π : Measure X) U) := by
    simp only [coe_finitePlanSourceProjection]
    have heval : Measurable (fun π : LocalFiniteMeasure (X × Y) ↦
        (π : Measure (X × Y)) (U ×ˢ univ)) :=
      (LocalFiniteMeasure.lowerSemicontinuous_measure_open (hU.prod isOpen_univ)).measurable
    have heq : (fun π : LocalFiniteMeasure (X × Y) ↦
        (if (π : Measure (X × Y)) univ < ⊤ then (π : Measure (X × Y)).fst else 0) U) =
        (fun π : LocalFiniteMeasure (X × Y) ↦ if (π : Measure (X × Y)) univ < ⊤ then
          (π : Measure (X × Y)) (U ×ˢ univ) else 0) := by
      funext π
      split_ifs <;> simp [Measure.fst_apply hU.measurableSet,
        show Prod.fst ⁻¹' U = U ×ˢ (univ : Set Y) by ext e; simp]
    rw [heq]
    exact Measurable.ite (measurableSet_lt hmass measurable_const) heval measurable_const
  have : ∀ π : LocalFiniteMeasure (X × Y),
      IsFiniteMeasure (finitePlanSourceProjection π : Measure X) := by
    intro π
    by_cases h : (π : Measure (X × Y)) univ < ⊤
    · have : IsFiniteMeasure (π : Measure (X × Y)) := ⟨h⟩
      rw [coe_finitePlanSourceProjection, ite_eq_left h]
      infer_instance
    · rw [coe_finitePlanSourceProjection, ite_eq_right h]
      infer_instance
  exact Measurable.measure_of_isPiSystem
    (S := {U : Set X | IsOpen U}) BorelSpace.measurable_eq isPiSystem_isOpen
    hopen (hopen univ isOpen_univ)

theorem finitePlanSourceProjection_eq_of_fst_eq
    (π₀ π₁ : LocalFiniteMeasure (X × Y))
    (h₀ : (π₀ : Measure (X × Y)) univ < ⊤)
    (h₁ : (π₁ : Measure (X × Y)) univ < ⊤)
    (heq : (π₀ : Measure (X × Y)).fst = (π₁ : Measure (X × Y)).fst) :
    finitePlanSourceProjection π₀ = finitePlanSourceProjection π₁ := by
  apply Subtype.ext
  rw [coe_finitePlanSourceProjection, coe_finitePlanSourceProjection,
    ite_eq_left h₀, ite_eq_left h₁]
  exact heq

end FiniteProjection

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω] {n : ℕ}

local instance actualFiniteSourcePolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance actualFiniteSourceProjectedPolish : PolishSpace
    (LocalFiniteMeasure ((ι → ℝ) × ℝ)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Same original feasible allocations, restricted in the same physical source,
give exact full source marginal equality under their actual rooted pair law. -/
theorem ae_actualAllocationRootedSceneLaw_equal_full_source
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
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N) :
    ∀ᵐ scene ∂(actualAllocationRootedSceneLaw P μ aplus aminus hplus hminus Y hY
      H hH coord hcoord u hu N hN D hD :
        Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst =
        (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst := by
  let Γp := physicalSceneGlobalAllocationFamily μ aplus Y
  let Γm := physicalSceneGlobalAllocationFamily μ aminus Y
  let observation := physicalSceneRootedLocalScene
    (fun w ↦ (Γp w).restrict (H ×ˢ univ))
    (fun w ↦ (Γm w).restrict (H ×ˢ univ)) coord u N
  have hm := measurable_physicalSceneRootedLocalScene
    (fun w ↦ (Γp w).restrict (H ×ˢ univ))
    (fun w ↦ (Γm w).restrict (H ×ˢ univ))
    (measurable_physicalPlan_sourceRestriction Γp
      (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY) H hH)
    (measurable_physicalPlan_sourceRestriction Γm
      (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY) H hH)
    coord hcoord u hu N
  let good : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) → Prop := fun scene ↦
    (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) univ < ⊤ ∧
    (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) univ < ⊤ ∧
    finitePlanSourceProjection scene.1 = finitePlanSourceProjection scene.2
  have hg : MeasurableSet {scene | good scene} := by
    have hmass := (LocalFiniteMeasure.lowerSemicontinuous_measure_open
      (X := (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) isOpen_univ).measurable
    exact (measurableSet_lt (hmass.comp measurable_fst) measurable_const).inter
      ((measurableSet_lt (hmass.comp measurable_snd) measurable_const).inter
        (measurableSet_eq_fun
          (measurable_finitePlanSourceProjection.comp measurable_fst)
          (measurable_finitePlanSourceProjection.comp measurable_snd)))
  have hroot : IsProbabilityMeasure (cavityRootMeasure volume D N) :=
    isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have henv : ∀ᵐ v : Ω × (ι → ℝ) ∂P.prod (cavityRootMeasure volume D N),
      Γp v.1 = physicalSceneAllocationPlan μ (aplus v.1) (Y v.1) ∧
      Γm v.1 = physicalSceneAllocationPlan μ (aminus v.1) (Y v.1) ∧
      IsSemidiscreteAllocation μ (p v.1) (aplus v.1) ∧
      IsSemidiscreteAllocation μ (p v.1) (aminus v.1) :=
    measurePreserving_fst.quasiMeasurePreserving.ae
      ((physicalSceneGlobalAllocationFamily_ae_eq P μ aplus Y p hfp).and
        ((physicalSceneGlobalAllocationFamily_ae_eq P μ aminus Y p hfm).and (hfp.and hfm)))
  have hgood : ∀ᵐ scene ∂(P.prod (cavityRootMeasure volume D N)).map observation,
      good scene := by
    apply (ae_map_iff hm.aemeasurable hg).mpr
    filter_upwards [henv] with v hv
    have hpfinite := isFiniteMeasure_physicalSceneRootedPlan
      ((Γp v.1).restrict (H ×ˢ univ)) coord u N v.2
    have hmfinite := isFiniteMeasure_physicalSceneRootedPlan
      ((Γm v.1).restrict (H ×ˢ univ)) coord u N v.2
    have hsrc : ((observation v).1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst =
        ((observation v).2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst := by
      change (physicalSceneRootedPlan ((Γp v.1).restrict (H ×ˢ univ)) coord u N v.2).fst =
        (physicalSceneRootedPlan ((Γm v.1).restrict (H ×ˢ univ)) coord u N v.2).fst
      rw [hv.1, hv.2.1, ← physicalSceneAllocationPlan_restrict μ (aplus v.1) (Y v.1) hH,
        ← physicalSceneAllocationPlan_restrict μ (aminus v.1) (Y v.1) hH]
      exact (physicalSceneRootedPlan_source_restrict_marginals hv.2.2.1 (Y v.1)
        H coord hcoord u hu N v.2).1.trans
        (physicalSceneRootedPlan_source_restrict_marginals hv.2.2.2 (Y v.1)
          H coord hcoord u hu N v.2).1.symm
    have hp : ((observation v).1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) univ < ⊤ := by
      change (physicalSceneRootedPlan ((Γp v.1).restrict (H ×ˢ univ)) coord u N v.2) univ < ⊤
      exact measure_lt_top _ _
    have hmf : ((observation v).2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) univ < ⊤ := by
      change (physicalSceneRootedPlan ((Γm v.1).restrict (H ×ˢ univ)) coord u N v.2) univ < ⊤
      exact measure_lt_top _ _
    refine ⟨hp, hmf, ?_⟩
    exact finitePlanSourceProjection_eq_of_fst_eq _ _ hp hmf hsrc
  change ∀ᵐ scene ∂(P.prod (cavityRootMeasure volume D N)).map observation, _
  filter_upwards [hgood] with scene hs
  have heq := congrArg (fun μ : LocalFiniteMeasure ((ι → ℝ) × ℝ) ↦
    (μ : Measure ((ι → ℝ) × ℝ))) hs.2.2
  simpa only [coe_finitePlanSourceProjection, ite_eq_left hs.1, ite_eq_left hs.2.1] using heq

open PointProcess PointProcess.LocalConfiguration

variable (base : (ι → ℝ) × ℝ)
local instance actualFiniteSourceCountableStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance actualFiniteSourceCountableTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance actualFiniteSourceCountableBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance actualFiniteSourceCountablePolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace

/-- The same exact finite-stage full source equality holds in the actual law
that also retains the original integer target cloud. -/
theorem ae_actualAllocationRootedCountableSceneLaw_equal_full_source
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
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ∀ᵐ s ∂(actualAllocationRootedCountableSceneLaw base P μ aplus aminus hplus hminus
      Y hY H hH coord hcoord u hu D hD :
        Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      (s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst =
        (s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst := by
  have hp := ae_actualAllocationRootedSceneLaw_equal_full_source P μ aplus aminus hplus hminus
    Y hY p hfp hfm H hH coord hcoord u hu ((n : ℝ) + 1) (by positivity) D hD
  have hmap := map_actualAllocationRootedCountableSceneLaw_pair base P μ aplus aminus
    hplus hminus Y hY H hH coord hcoord u hu D hD
  have heq := congrArg (fun Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) ↦
      (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) hmap
  change (actualAllocationRootedCountableSceneLaw base P μ aplus aminus hplus hminus
    Y hY H hH coord hcoord u hu D hD :
      Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)).map
        Prod.fst = _ at heq
  rw [← heq] at hp
  exact ae_of_ae_map measurable_fst.aemeasurable hp

omit base in
/-- Physical source restriction splits the same actual rooted plan exactly. -/
theorem physicalSceneRootedPlan_source_split
    (Γ : Measure (M × M)) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ) :
    physicalSceneRootedPlan Γ coord u N z =
      physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z +
      physicalSceneRootedPlan (Γ.restrict (Hᶜ ×ˢ univ)) coord u N z := by
  have hcomp : (H ×ˢ (univ : Set M))ᶜ = Hᶜ ×ˢ univ := by ext e; simp
  have heq := Measure.restrict_add_restrict_compl (μ := Γ) (hH.prod MeasurableSet.univ)
  rw [hcomp] at heq
  unfold physicalSceneRootedPlan
  calc
    _ = ENNReal.ofReal N • Measure.map (physicalSceneRootedObservation coord u z)
        (Γ.restrict (H ×ˢ univ) + Γ.restrict (Hᶜ ×ˢ univ)) := by rw [heq]
    _ = _ := by
      rw [Measure.map_add _ _
        (measurable_physicalSceneRootedObservation coord hcoord u hu z), smul_add]

omit base in
/-- Discarded rooted target-window mass pays the actual target-test defect of
two retained subplans of globally equal-target plans. -/
theorem ofReal_abs_target_tests_of_split_common_target_le
    (F₀ F₁ R₀ R₁ D₀ D₁ : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure F₀] [IsFiniteMeasure F₁] [IsFiniteMeasure R₀] [IsFiniteMeasure R₁]
    [IsFiniteMeasure D₀] [IsFiniteMeasure D₁]
    (hsplit₀ : F₀ = R₀ + D₀) (hsplit₁ : F₁ = R₁ + D₁) (htarget : F₀.snd = F₁.snd)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (U : Set (ι → ℝ))
    (hU : ∀ y ∈ tsupport f, y.1 ∈ U) :
    ENNReal.ofReal |(∫ e, f e.2 ∂R₀) - ∫ e, f e.2 ∂R₁| ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (D₀ {e | e.2.1 ∈ U} + D₁ {e | e.2.1 ∈ U}) := by
  let W := {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U}
  have hint (Γ : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) [IsFiniteMeasure Γ] :
      Integrable (fun e ↦ f e.2) Γ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (Eventually.of_forall fun e ↦
        f.toBoundedContinuousFunction.norm_coe_le_norm e.2)
  have hbound (Γ : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) [IsFiniteMeasure Γ] :
      |∫ e, f e.2 ∂Γ| ≤ ‖f.toBoundedContinuousFunction‖ * Γ.real W := by
    have hz : ∀ e, e ∉ W → f e.2 = 0 := by
      intro e he
      by_contra hn
      exact he (hU e.2 (subset_tsupport f hn))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    simpa only [Real.norm_eq_abs] using norm_setIntegral_le_of_norm_le_const_ae
      (μ := Γ) (s := W) (f := fun e ↦ f e.2) (measure_lt_top _ _)
      (Eventually.of_forall fun e ↦ f.toBoundedContinuousFunction.norm_coe_le_norm e.2)
  have hfull : (∫ e, f e.2 ∂F₀) = ∫ e, f e.2 ∂F₁ := by
    have h₀ := integral_map (μ := F₀) (f := fun y ↦ f y)
      measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    have h₁ := integral_map (μ := F₁) (f := fun y ↦ f y)
      measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    exact h₀.symm.trans ((congrArg (fun μ : Measure ((ι → ℝ) × ℝ) ↦
      ∫ y, f y ∂μ) htarget).trans h₁)
  rw [hsplit₀, hsplit₁, integral_add_measure (hint R₀) (hint D₀),
    integral_add_measure (hint R₁) (hint D₁)] at hfull
  have heq : (∫ e, f e.2 ∂R₀) - (∫ e, f e.2 ∂R₁) =
      (∫ e, f e.2 ∂D₁) - (∫ e, f e.2 ∂D₀) := by linarith [hfull]
  have hreal : |(∫ e, f e.2 ∂R₀) - (∫ e, f e.2 ∂R₁)| ≤
      ‖f.toBoundedContinuousFunction‖ * (D₀.real W + D₁.real W) := by
    rw [heq, mul_add]
    exact (abs_sub _ _).trans (by linarith [hbound D₀, hbound D₁])
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
    ofReal_measureReal, ofReal_measureReal] at h
  exact h


omit base in
/-- Haar averaging of the actual retained target-test defect.  The error is
exactly charged to discarded original physical source mass. -/
theorem lintegral_rooted_target_tests_source_restrict_le_discard
    (Γ₀ Γ₁ : Measure (M × M)) [IsFiniteMeasure Γ₀] [IsFiniteMeasure Γ₁]
    (htarget : Γ₀.snd = Γ₁.snd) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (hfU : ∀ y ∈ tsupport f, y.1 ∈ U) :
    (∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan (Γ₀.restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γ₁.restrict (H ×ˢ univ)) coord u N z|
      ∂cavityRootMeasure volume D N) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (volume U * Γ₀ (Hᶜ ×ˢ univ) + volume U * Γ₁ (Hᶜ ×ˢ univ)) := by
  let W : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) := {e | e.2.1 ∈ U}
  have hW : MeasurableSet W := hU.preimage measurable_snd.fst
  have hm (Γ : Measure (M × M)) [IsFiniteMeasure Γ] :
      Measurable (fun z : ι → ℝ ↦ physicalSceneRootedPlan Γ coord u N z W) := by
    have hΓ : Measurable (fun _ : Unit ↦ Γ) := measurable_const
    have hm := measurable_joint_physicalSceneRootedPlan (fun _ : Unit ↦ Γ)
      hΓ coord hcoord u hu N
    exact (Measure.measurable_coe hW).comp
      (hm.comp (show Measurable (fun z : ι → ℝ ↦ ((), z)) from
        measurable_const.prodMk measurable_id))
  have hb (z : ι → ℝ) : ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan (Γ₀.restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan (Γ₁.restrict (H ×ˢ univ)) coord u N z| ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (physicalSceneRootedPlan (Γ₀.restrict (Hᶜ ×ˢ univ)) coord u N z W +
          physicalSceneRootedPlan (Γ₁.restrict (Hᶜ ×ˢ univ)) coord u N z W) := by
    have := isFiniteMeasure_physicalSceneRootedPlan Γ₀ coord u N z
    have := isFiniteMeasure_physicalSceneRootedPlan Γ₁ coord u N z
    have := isFiniteMeasure_physicalSceneRootedPlan (Γ₀.restrict (H ×ˢ univ)) coord u N z
    have := isFiniteMeasure_physicalSceneRootedPlan (Γ₁.restrict (H ×ˢ univ)) coord u N z
    have := isFiniteMeasure_physicalSceneRootedPlan (Γ₀.restrict (Hᶜ ×ˢ univ)) coord u N z
    have := isFiniteMeasure_physicalSceneRootedPlan (Γ₁.restrict (Hᶜ ×ˢ univ)) coord u N z
    apply ofReal_abs_target_tests_of_split_common_target_le
      (physicalSceneRootedPlan Γ₀ coord u N z) (physicalSceneRootedPlan Γ₁ coord u N z)
      _ _ _ _
      (physicalSceneRootedPlan_source_split Γ₀ H hH coord hcoord u hu N z)
      (physicalSceneRootedPlan_source_split Γ₁ H hH coord hcoord u hu N z) _ f U hfU
    rw [(physicalSceneRootedPlan_marginals Γ₀ coord hcoord u hu N z).2,
      (physicalSceneRootedPlan_marginals Γ₁ coord hcoord u hu N z).2, htarget]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (physicalSceneRootedPlan (Γ₀.restrict (Hᶜ ×ˢ univ)) coord u N z W +
          physicalSceneRootedPlan (Γ₁.restrict (Hᶜ ×ˢ univ)) coord u N z W)
        ∂cavityRootMeasure volume D N := lintegral_mono hb
    _ = ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((∫⁻ z, physicalSceneRootedPlan (Γ₀.restrict (Hᶜ ×ˢ univ)) coord u N z W
          ∂cavityRootMeasure volume D N) +
        ∫⁻ z, physicalSceneRootedPlan (Γ₁.restrict (Hᶜ ×ˢ univ)) coord u N z W
          ∂cavityRootMeasure volume D N) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (hm (Γ₀.restrict (Hᶜ ×ˢ univ))) _]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply add_le_add
      · simpa only [Measure.restrict_apply_univ] using
          lintegral_physicalSceneRootedPlan_targetWindow_le
            (Γ₀.restrict (Hᶜ ×ˢ univ)) coord hcoord u hu N hN D U hU
      · simpa only [Measure.restrict_apply_univ] using
          lintegral_physicalSceneRootedPlan_targetWindow_le
            (Γ₁.restrict (Hᶜ ×ˢ univ)) coord hcoord u hu N hN D U hU


omit base in
/-- The original feasible allocations give the retained rooted target-test
error bound.  The actual random restricted target columns are never replaced. -/
theorem lintegral_actualAllocation_rooted_target_tests_restrict_le_discard
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (Y : Ω → Fin (n + 1) → M) (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aplus w))
    (hfm : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aminus w))
    (H : Set M) (hH : MeasurableSet H)
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
      2 * ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U * μ Hᶜ := by
  let Γp := physicalSceneGlobalAllocationFamily μ aplus Y
  let Γm := physicalSceneGlobalAllocationFamily μ aminus Y
  have heqp := physicalSceneGlobalAllocationFamily_ae_eq P μ aplus Y p hfp
  have heqm := physicalSceneGlobalAllocationFamily_ae_eq P μ aminus Y p hfm
  have hpre : Prod.fst ⁻¹' Hᶜ = Hᶜ ×ˢ (univ : Set M) := by ext e; simp
  have hb : ∀ᵐ w ∂P,
      (∫⁻ z, ENNReal.ofReal
        |(∫ e, f e.2 ∂physicalSceneRootedPlan ((Γp w).restrict (H ×ˢ univ)) coord u N z) -
          ∫ e, f e.2 ∂physicalSceneRootedPlan ((Γm w).restrict (H ×ˢ univ)) coord u N z|
        ∂cavityRootMeasure volume D N) ≤
          ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
            (volume U * μ Hᶜ + volume U * μ Hᶜ) := by
    filter_upwards [heqp, heqm, hfp, hfm] with w hwp hwm hpa hma
    change Γp w = _ at hwp
    change Γm w = _ at hwm
    have htarget : (Γp w).snd = (Γm w).snd := by
      rw [hwp, hwm, physicalSceneAllocationPlan_snd hpa, physicalSceneAllocationPlan_snd hma]
    have hmassp : Γp w (Hᶜ ×ˢ univ) = μ Hᶜ := by
      have heq := congrArg (fun ν : Measure M ↦ ν Hᶜ) (physicalSceneAllocationPlan_fst hpa (Y w))
      rw [hwp]
      simpa only [Measure.fst_apply hH.compl, hpre] using heq
    have hmassm : Γm w (Hᶜ ×ˢ univ) = μ Hᶜ := by
      have heq := congrArg (fun ν : Measure M ↦ ν Hᶜ) (physicalSceneAllocationPlan_fst hma (Y w))
      rw [hwm]
      simpa only [Measure.fst_apply hH.compl, hpre] using heq
    simpa only [hmassp, hmassm] using
      lintegral_rooted_target_tests_source_restrict_le_discard
        (Γp w) (Γm w) htarget H hH coord hcoord u hu N hN D U hU f hfU
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
          (volume U * μ Hᶜ + volume U * μ Hᶜ) ∂P := lintegral_mono_ae hb
    _ = _ := by simp only [lintegral_const, measure_univ, mul_one]; ring

end OTSelector.Reconstruction
