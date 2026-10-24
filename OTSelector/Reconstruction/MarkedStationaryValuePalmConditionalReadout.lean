import OTSelector.Reconstruction.MarkedStationaryValuePalmScene
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Original tagged conditional paired-edge Palm readouts

Disintegration retains the original macroscopic tag, both original clocks, and
the complete transverse displacement. Every nonnegative conditional Palm
readout integrates to the same original source-unit-window edge readout.
Neither stationarity nor a finite-moment premise is needed for this identity.
Finite absolute original readout also gives exact signed disintegration, and
bounded original probes require only the original finite source-unit moment.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T]

local instance markedStationaryValuePalmConditionalReadoutLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

local instance markedStationaryValuePalmConditionalReadoutLocalNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩

/-- The same actual original source-unit-window edge readout is jointly
measurable in its original tag and its actual diffuse physical scene. -/
theorem measurable_tagged_physicalScene_sourceUnit_readout
    {F : T × PhysicalPairPalmMark ι → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι},
        F (p.1, (physicalPairAnchor e).2)
          ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))) := by
  let κ : Kernel (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))
      (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
    localFiniteMeasureKernel.comap (fun p ↦ p.2.1) (measurable_fst.comp measurable_snd)
  have hκ : IsSFiniteKernel κ := by dsimp [κ]; infer_instance
  have hread : Measurable (Function.uncurry
      (fun (p : T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))
        (e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ↦
        F (p.1, (physicalPairAnchor e).2))) :=
    hF.comp (measurable_fst.fst.prodMk
      ((measurable_snd.comp measurable_physicalPairAnchor).comp measurable_snd))
  exact hread.setLIntegral_kernel_prod_right (κ := κ)
    ((measurableSet_palmUnitCube ι).preimage measurable_fst.fst)

/-- The conditional full-displacement paired-edge Palm readout is measurable
in the original tag; this is derived from the original actual plan kernel. -/
theorem measurable_conditional_cubePalm_physicalScenePairCampbell
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ]
    {F : T × PhysicalPairPalmMark ι → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun w ↦ ∫⁻ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w))) := by
  have hm := (measurable_tagged_physicalScene_sourceUnit_readout hF).lintegral_kernel_prod_right'
    (κ := ρ.condKernel)
  convert hm using 1
  funext w
  exact lintegral_cubePalm_physicalScenePairCampbell (ρ.condKernel w)
    (hF.comp (measurable_const.prodMk measurable_id))

/-- Exact tagged conditional Palm disintegration for every nonnegative
observable of the same original clocks and full transverse displacement. -/
theorem lintegral_conditional_cubePalm_physicalScenePairCampbell
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ]
    {F : T × PhysicalPairPalmMark ι → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w, ∫⁻ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w)) ∂ρ.fst) =
      ∫⁻ p, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
          e.1.1 ∈ palmUnitCube ι}, F (p.1, (physicalPairAnchor e).2)
        ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂ρ := by
  calc
    _ = ∫⁻ w, ∫⁻ scene, ∫⁻ e in
        {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι},
        F (w, (physicalPairAnchor e).2)
          ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          ∂ρ.condKernel w ∂ρ.fst := by
      apply lintegral_congr_ae
      exact .of_forall (fun w ↦ lintegral_cubePalm_physicalScenePairCampbell
        (ρ.condKernel w) (hF.comp (measurable_const.prodMk measurable_id)))
    _ = _ := Measure.lintegral_condKernel (measurable_tagged_physicalScene_sourceUnit_readout hF)

/-- Finite energy in the actual original tagged source-window readout gives
finite energy for almost every conditional paired-edge Palm law. -/
theorem ae_conditional_cubePalm_physicalScenePairCampbell_lintegral_lt_top
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ]
    {F : T × PhysicalPairPalmMark ι → ℝ≥0∞} (hF : Measurable F)
    (hfinite : (∫⁻ p, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
        e.1.1 ∈ palmUnitCube ι}, F (p.1, (physicalPairAnchor e).2)
      ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂ρ) < ∞) :
    ∀ᵐ w ∂ρ.fst, (∫⁻ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w))) < ∞ := by
  apply ae_lt_top (measurable_conditional_cubePalm_physicalScenePairCampbell ρ hF)
  rw [lintegral_conditional_cubePalm_physicalScenePairCampbell ρ hF]
  exact ne_of_lt hfinite

/-- The original source-unit-window edge measure, retaining the original
macroscopic tag as its environment. -/
def taggedPhysicalSceneUnitEdgeKernel :
    Kernel (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))
      (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  (localFiniteMeasureKernel.comap (fun p ↦ p.2.1)
    (measurable_fst.comp measurable_snd)).restrict
      ((measurableSet_palmUnitCube ι).preimage measurable_fst.fst)

instance taggedPhysicalSceneUnitEdgeKernelIsSFinite :
    IsSFiniteKernel (taggedPhysicalSceneUnitEdgeKernel (ι := ι) (T := T)) := by
  unfold taggedPhysicalSceneUnitEdgeKernel
  infer_instance

@[simp]
theorem taggedPhysicalSceneUnitEdgeKernel_apply
    (p : T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :
    taggedPhysicalSceneUnitEdgeKernel p =
      (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).restrict
        {e | e.1.1 ∈ palmUnitCube ι} := rfl

/-- A canonical measurable kernel of the actual conditional paired-edge Palm
measures, constructed from the original scene conditional kernel. -/
def conditionalPhysicalScenePairPalmKernel
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ] : Kernel T (PhysicalPairPalmMark ι) :=
  ((physicalScenePairKernel ∘ₖ ρ.condKernel).restrict
    ((measurableSet_palmUnitCube ι).prod MeasurableSet.univ)).map Prod.snd

instance conditionalPhysicalScenePairPalmKernelIsSFinite
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ] : IsSFiniteKernel (conditionalPhysicalScenePairPalmKernel ρ) := by
  unfold conditionalPhysicalScenePairPalmKernel
  infer_instance

@[simp]
theorem conditionalPhysicalScenePairPalmKernel_apply
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ] (w : T) :
    conditionalPhysicalScenePairPalmKernel ρ w =
      cubePalm ι (physicalScenePairCampbell (ρ.condKernel w)) := by
  rw [conditionalPhysicalScenePairPalmKernel, Kernel.map_apply _ measurable_snd,
    Kernel.restrict_apply, Kernel.comp_apply]
  rfl

private theorem palmReadout_lintegral_compProd
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ]
    {F : T × PhysicalPairPalmMark ι → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂(ρ.fst ⊗ₘ conditionalPhysicalScenePairPalmKernel ρ)) =
      ∫⁻ pe, F (pe.1.1, (physicalPairAnchor pe.2).2)
        ∂(ρ ⊗ₘ taggedPhysicalSceneUnitEdgeKernel) := by
  rw [Measure.lintegral_compProd hF]
  simp_rw [conditionalPhysicalScenePairPalmKernel_apply]
  rw [lintegral_conditional_cubePalm_physicalScenePairCampbell ρ hF]
  have hactual : Measurable (fun pe :
      (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) ×
        (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦
      F (pe.1.1, (physicalPairAnchor pe.2).2)) :=
    hF.comp (measurable_fst.fst.prodMk
      ((measurable_snd.comp measurable_physicalPairAnchor).comp measurable_snd))
  rw [Measure.lintegral_compProd hactual]
  rfl

private theorem palmReadout_integrable_integral_compProd
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    {f : A × B → ℝ} (hf : Measurable f) (hint : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun a ↦ ∫ b, f (a, b) ∂κ a) μ := by
  have hnorm := ((Measure.integrable_compProd_iff hint.1).mp hint).2
  apply hnorm.mono
    (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).aestronglyMeasurable
  exact .of_forall (fun a ↦ by
    exact (norm_integral_le_integral_norm _).trans_eq
      (Real.norm_of_nonneg (integral_nonneg (fun b ↦ norm_nonneg (f (a, b))))).symm)

/-- Finite absolute original edge readout supplies inner and outer signed
integrability and exact signed conditional Palm disintegration. -/
theorem integrable_and_integral_conditional_cubePalm_physicalScenePairCampbell
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ]
    {F : T × PhysicalPairPalmMark ι → ℝ} (hF : Measurable F)
    (habs : (∫⁻ p, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
        e.1.1 ∈ palmUnitCube ι}, ENNReal.ofReal |F (p.1, (physicalPairAnchor e).2)|
      ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂ρ) < ∞) :
    (∀ᵐ w ∂ρ.fst, Integrable (fun m ↦ F (w, m))
      (cubePalm ι (physicalScenePairCampbell (ρ.condKernel w)))) ∧
    Integrable (fun w ↦ ∫ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w))) ρ.fst ∧
    (∀ᵐ p ∂ρ, IntegrableOn (fun e ↦ F (p.1, (physicalPairAnchor e).2))
      {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι}
      (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))) ∧
    Integrable (fun p ↦ ∫ e in
      {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι},
        F (p.1, (physicalPairAnchor e).2)
          ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))) ρ ∧
    (∫ w, ∫ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w)) ∂ρ.fst) =
      ∫ p, ∫ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
          e.1.1 ∈ palmUnitCube ι}, F (p.1, (physicalPairAnchor e).2)
        ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂ρ := by
  let actual :
      (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) ×
        (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) → ℝ :=
    fun pe ↦ F (pe.1.1, (physicalPairAnchor pe.2).2)
  have hactual : Measurable actual := hF.comp (measurable_fst.fst.prodMk
    ((measurable_snd.comp measurable_physicalPairAnchor).comp measurable_snd))
  have hFa : Integrable actual (ρ ⊗ₘ taggedPhysicalSceneUnitEdgeKernel) := by
    refine ⟨hactual.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm, Measure.lintegral_compProd
      (f := fun a ↦ ENNReal.ofReal ‖actual a‖)
      (ENNReal.measurable_ofReal.comp hactual.norm)]
    simpa only [taggedPhysicalSceneUnitEdgeKernel_apply, Real.norm_eq_abs, actual] using habs
  have hFp : Integrable F (ρ.fst ⊗ₘ conditionalPhysicalScenePairPalmKernel ρ) := by
    refine ⟨hF.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm,
      palmReadout_lintegral_compProd ρ (F := fun a ↦ ENNReal.ofReal ‖F a‖)
        (ENNReal.measurable_ofReal.comp hF.norm)]
    exact (hasFiniteIntegral_iff_norm actual).mp hFa.2
  have ha := ((Measure.integrable_compProd_iff hFa.1).mp hFa).1
  have hp := ((Measure.integrable_compProd_iff hFp.1).mp hFp).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [conditionalPhysicalScenePairPalmKernel_apply] using hp
  · simpa only [conditionalPhysicalScenePairPalmKernel_apply] using
      palmReadout_integrable_integral_compProd ρ.fst
        (conditionalPhysicalScenePairPalmKernel ρ) hF hFp
  · simpa only [taggedPhysicalSceneUnitEdgeKernel_apply, actual, IntegrableOn] using ha
  · simpa only [taggedPhysicalSceneUnitEdgeKernel_apply, actual] using
      palmReadout_integrable_integral_compProd ρ
        taggedPhysicalSceneUnitEdgeKernel hactual hFa
  · have heq : (∫ p, F p ∂(ρ.fst ⊗ₘ conditionalPhysicalScenePairPalmKernel ρ)) =
        ∫ pe, actual pe ∂(ρ ⊗ₘ taggedPhysicalSceneUnitEdgeKernel) := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hFp,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hFa,
        palmReadout_lintegral_compProd ρ (F := fun a ↦ ENNReal.ofReal (F a))
          (ENNReal.measurable_ofReal.comp hF),
        palmReadout_lintegral_compProd ρ (F := fun a ↦ ENNReal.ofReal (-F a))
          (ENNReal.measurable_ofReal.comp hF.neg)]
    rw [Measure.integral_compProd hFp, Measure.integral_compProd hFa] at heq
    simpa only [conditionalPhysicalScenePairPalmKernel_apply,
      taggedPhysicalSceneUnitEdgeKernel_apply, actual] using heq

omit [Fintype ι] in
/-- A bounded jointly measurable signed original paired-mark probe is
absolutely integrable whenever the original joint source-unit moment is finite. -/
theorem lintegral_abs_tagged_sourceUnit_lt_top_of_bounded
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {F : T × PhysicalPairPalmMark ι → ℝ} {G : ℝ}
    (hbound : ∀ p, |F p| ≤ G)
    (hunit : (∫⁻ p, (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂ρ) < ∞) :
    (∫⁻ p, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
        e.1.1 ∈ palmUnitCube ι}, ENNReal.ofReal |F (p.1, (physicalPairAnchor e).2)|
      ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂ρ) < ∞ := by
  calc
    _ ≤ ∫⁻ p, ∫⁻ _e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
        e.1.1 ∈ palmUnitCube ι}, ENNReal.ofReal G
          ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂ρ :=
      lintegral_mono (fun p ↦ lintegral_mono (fun e ↦
        ENNReal.ofReal_le_ofReal (hbound (p.1, (physicalPairAnchor e).2))))
    _ = ENNReal.ofReal G * ∫⁻ p,
        (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          {e | e.1.1 ∈ palmUnitCube ι} ∂ρ := by
      simp_rw [lintegral_const, Measure.restrict_apply_univ]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hunit

/-- The actual finite original unit-window moment and a jointly measurable
bounded signed probe supply conditional Palm integrability and exact signed
readout, with the original macro tag and complete displacement retained. -/
theorem integrable_and_integral_bounded_conditional_cubePalm_physicalScenePairCampbell
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsFiniteMeasure ρ]
    {F : T × PhysicalPairPalmMark ι → ℝ} (hF : Measurable F) {G : ℝ}
    (hbound : ∀ p, |F p| ≤ G)
    (hunit : (∫⁻ p, (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂ρ) < ∞) :
    (∀ᵐ w ∂ρ.fst, Integrable (fun m ↦ F (w, m))
      (cubePalm ι (physicalScenePairCampbell (ρ.condKernel w)))) ∧
    Integrable (fun w ↦ ∫ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w))) ρ.fst ∧
    (∫ w, ∫ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w)) ∂ρ.fst) =
      ∫ p, ∫ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
          e.1.1 ∈ palmUnitCube ι}, F (p.1, (physicalPairAnchor e).2)
        ∂(p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂ρ := by
  have h := integrable_and_integral_conditional_cubePalm_physicalScenePairCampbell ρ hF
    (lintegral_abs_tagged_sourceUnit_lt_top_of_bounded ρ hbound hunit)
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

end OTSelector.Reconstruction
