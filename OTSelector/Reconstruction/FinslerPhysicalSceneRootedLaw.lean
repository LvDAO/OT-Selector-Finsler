import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClock
import OTSelector.MeasureTheory.PairWeakCycleSupport
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Actual physical rooted plan laws in the vague scene carrier

A measurable environment of finite physical plans remains jointly measurable
after the actual spatial observation and root translation.  Both original plans
then define one law on the locally finite vague carrier, using the same original
environment and root.  Their physical marginals, including random restricted
target column masses, are retained by the actual plan observations.
-/

open Set MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option linter.unusedSectionVars false

section FiniteMap

variable {V S X : Type*} [MeasurableSpace V] [MeasurableSpace S] [MeasurableSpace X]

/-- A Giry-measurable finite measure and a jointly measurable observation have
a measurable observed measure, with no fixed spatial or marginal law. -/
theorem measurable_parameterized_finite_measure_map
    (Γ : V → Measure S) [∀ v, IsFiniteMeasure (Γ v)] (hΓ : Measurable Γ)
    (f : V × S → X) (hf : Measurable f) :
    Measurable (fun v ↦ (Γ v).map (fun s ↦ f (v, s))) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  let K : Kernel V S := ⟨Γ, hΓ⟩
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := K) (hU.preimage hf) (fun _ ↦ inferInstance)
  have heq : (fun v ↦ ((Γ v).map (fun s ↦ f (v, s))) U) =
      (fun v ↦ K v (Prod.mk v ⁻¹' (f ⁻¹' U))) := by
    funext v
    rw [Measure.map_apply (f := fun s : S ↦ f (v, s))
      (hf.comp (measurable_const.prodMk measurable_id)) hU]
    rfl
  rw [heq]
  exact hm

end FiniteMap

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

local instance physicalSceneRootedLawLocalInst : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The actual finite physical plan depends measurably on the original
environment and its independently chosen spatial root. -/
theorem measurable_joint_physicalSceneRootedPlan
    (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)] (hΓ : Measurable Γ)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) :
    Measurable (fun v : Ω × (ι → ℝ) ↦ physicalSceneRootedPlan (Γ v.1) coord u N v.2) := by
  let f : (Ω × (ι → ℝ)) × (M × M) → (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
    fun v ↦ physicalSceneRootedObservation coord u v.1.2 v.2
  have hf : Measurable f :=
    ((((hcoord.comp measurable_snd.fst).sub measurable_fst.snd).prodMk
      (hu.comp measurable_snd.fst)).prodMk
      (((hcoord.comp measurable_snd.snd).sub measurable_fst.snd).prodMk
        (hu.comp measurable_snd.snd)))
  have hm := measurable_parameterized_finite_measure_map
    (fun v : Ω × (ι → ℝ) ↦ Γ v.1) (hΓ.comp measurable_fst) f hf
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [physicalSceneRootedPlan, Measure.smul_apply, smul_eq_mul]
  exact ((Measure.measurable_coe hU).comp hm).const_mul (ENNReal.ofReal N)

/-- Finite original physical mass remains finite under actual observation and
the finite original total-mass scaling. -/
theorem isFiniteMeasure_physicalSceneRootedPlan
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → (ι → ℝ)) (u : M → ℝ) (N : ℝ) (z : ι → ℝ) :
    IsFiniteMeasure (physicalSceneRootedPlan Γ coord u N z) := by
  constructor
  simp only [physicalSceneRootedPlan, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- One actual rooted physical plan as a locally finite vague measure. -/
def physicalSceneRootedLocalPlan
    (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)]
    (coord : M → (ι → ℝ)) (u : M → ℝ) (N : ℝ) (v : Ω × (ι → ℝ)) :
    LocalFiniteMeasure ((((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := by
  have := isFiniteMeasure_physicalSceneRootedPlan (Γ v.1) coord u N v.2
  exact ⟨physicalSceneRootedPlan (Γ v.1) coord u N v.2, inferInstance⟩

/-- The vague carrier contains exactly the actual observed physical plan. -/
@[simp]
theorem coe_physicalSceneRootedLocalPlan
    (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)]
    (coord : M → (ι → ℝ)) (u : M → ℝ) (N : ℝ) (v : Ω × (ι → ℝ)) :
    (physicalSceneRootedLocalPlan Γ coord u N v :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) =
      physicalSceneRootedPlan (Γ v.1) coord u N v.2 := rfl

/-- The actual observed finite plan is jointly measurable for the proved vague
Borel structure, including its actual random physical marginals. -/
theorem measurable_physicalSceneRootedLocalPlan
    (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)] (hΓ : Measurable Γ)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) :
    Measurable (physicalSceneRootedLocalPlan Γ coord u N) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  exact measurable_joint_physicalSceneRootedPlan Γ hΓ coord hcoord u hu N

/-- Both actual finite physical plans use one original environment and spatial
root in the locally finite scene carrier. -/
def physicalSceneRootedLocalScene
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ env, IsFiniteMeasure (Γplus env)] [∀ env, IsFiniteMeasure (Γminus env)]
    (coord : M → (ι → ℝ)) (u : M → ℝ) (N : ℝ) (v : Ω × (ι → ℝ)) :
    CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) :=
  (physicalSceneRootedLocalPlan Γplus coord u N v,
    physicalSceneRootedLocalPlan Γminus coord u N v)

/-- The actual two-plan physical scene is jointly measurable in its common
environment and root, without prescribed target column masses. -/
theorem measurable_physicalSceneRootedLocalScene
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ env, IsFiniteMeasure (Γplus env)] [∀ env, IsFiniteMeasure (Γminus env)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) :
    Measurable (physicalSceneRootedLocalScene Γplus Γminus coord u N) :=
  (measurable_physicalSceneRootedLocalPlan Γplus hplus coord hcoord u hu N).prodMk
    (measurable_physicalSceneRootedLocalPlan Γminus hminus coord hcoord u hu N)

/-- The actual environment and actual normalized Haar root produce a common
probability law for both physical plans in the diffuse vague scene space. -/
def physicalSceneRootedLocalSceneLaw
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ env, IsFiniteMeasure (Γplus env)] [∀ env, IsFiniteMeasure (Γminus env)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N) :
    ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) := by
  have := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  exact ⟨(Penv.prod (cavityRootMeasure volume D N)).map
    (physicalSceneRootedLocalScene Γplus Γminus coord u N),
    Measure.isProbabilityMeasure_map
      (measurable_physicalSceneRootedLocalScene Γplus Γminus hplus hminus
        coord hcoord u hu N).aemeasurable⟩

section Evaluation

variable (Penv : Measure Ω) [IsProbabilityMeasure Penv]
  (Γplus Γminus : Ω → Measure (M × M))
  [∀ env, IsFiniteMeasure (Γplus env)] [∀ env, IsFiniteMeasure (Γminus env)]
  (hplus : Measurable Γplus) (hminus : Measurable Γminus)
  (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
  (u : M → ℝ) (hu : Measurable u)
  (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)

/-- Every measurable scene readout under the actual physical scene law is
exactly its original environment and Haar-root integral, in iterated form. -/
theorem lintegral_physicalSceneRootedLocalSceneLaw
    (f : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ scene, f scene
      ∂(physicalSceneRootedLocalSceneLaw Penv Γplus Γminus hplus hminus
        coord hcoord u hu N hN D hD :
          Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) =
      ∫⁻ env, ∫⁻ z, f (physicalSceneRootedLocalScene Γplus Γminus coord u N (env, z))
        ∂cavityRootMeasure volume D N ∂Penv := by
  have hscene := measurable_physicalSceneRootedLocalScene Γplus Γminus hplus hminus
    coord hcoord u hu N
  have : SFinite (cavityRootMeasure volume D N) := by
    unfold cavityRootMeasure
    infer_instance
  change (∫⁻ scene, f scene ∂(Penv.prod (cavityRootMeasure volume D N)).map
    (physicalSceneRootedLocalScene Γplus Γminus coord u N)) = _
  rw [lintegral_map hf hscene]
  exact lintegral_prod _ (hf.comp hscene).aemeasurable

/-- Open-event mass of each actual physical plan under the scene law is its
original environment-root averaged mass, with the same plan in both integrals. -/
theorem lintegral_physicalSceneRootedLocalSceneLaw_open
    {E : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))} (hE : IsOpen E) :
    ((∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) E
      ∂(physicalSceneRootedLocalSceneLaw Penv Γplus Γminus hplus hminus
        coord hcoord u hu N hN D hD :
          Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) =
      ∫⁻ env, ∫⁻ z, physicalSceneRootedPlan (Γplus env) coord u N z E
        ∂cavityRootMeasure volume D N ∂Penv) ∧
    ((∫⁻ scene, (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) E
      ∂(physicalSceneRootedLocalSceneLaw Penv Γplus Γminus hplus hminus
        coord hcoord u hu N hN D hD :
          Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) =
      ∫⁻ env, ∫⁻ z, physicalSceneRootedPlan (Γminus env) coord u N z E
        ∂cavityRootMeasure volume D N ∂Penv) := by
  constructor
  · exact lintegral_physicalSceneRootedLocalSceneLaw Penv Γplus Γminus hplus hminus
      coord hcoord u hu N hN D hD _
      (((LocalFiniteMeasure.lowerSemicontinuous_measure_open hE).comp continuous_fst).measurable)
  · exact lintegral_physicalSceneRootedLocalSceneLaw Penv Γplus Γminus hplus hminus
      coord hcoord u hu N hN D hD _
      (((LocalFiniteMeasure.lowerSemicontinuous_measure_open hE).comp continuous_snd).measurable)

end Evaluation

end OTSelector.Reconstruction
