import OTSelector.Reconstruction.MarkedStationaryValuePalmScene
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootConditionalPhysical
import OTSelector.MeasureTheory.CompactProductMarginalTests
import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Original weak scene bounds produce the actual conditional Palm unit moment

Continuous source bumps times actual compact edge cutoffs preserve the original
window bound under weak convergence. Fatou on the constructed original mean
plan removes the cutoffs. The actual conditional kernels inherit finite unit
moments by disintegration, rather than by a conditional-moment premise.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι]
local instance markedStationaryValuePalmUnitMomentLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValuePalmUnitMomentLocalNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩

/-- The same original first plan, before spatial anchoring. -/
def physicalScenePlanKernel : Kernel
    (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))
    (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  localFiniteMeasureKernel.comap Prod.fst measurable_fst

instance physicalScenePlanKernelIsSFinite : IsSFiniteKernel (physicalScenePlanKernel (ι := ι)) := by
  unfold physicalScenePlanKernel
  infer_instance

/-- The original expected physical plan, including all original target positions. -/
def physicalSceneMeanPlan
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) := P.bind physicalScenePlanKernel

/-- Compact nonnegative tests have exactly their original scene expectation. -/
theorem lintegral_meanPlan_ofReal_compactTest
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (f : C_c((((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)), ℝ)) (hf : ∀ e, 0 ≤ f e) :
    (∫⁻ e, ENNReal.ofReal (f e) ∂physicalSceneMeanPlan P) =
      ∫⁻ scene, ENNReal.ofReal (LocalFiniteMeasure.testIntegral scene.1 f) ∂P := by
  have hm : Measurable (fun e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦
      ENNReal.ofReal (f e)) := ENNReal.measurable_ofReal.comp f.continuous.measurable
  rw [physicalSceneMeanPlan, Measure.lintegral_bind (Kernel.measurable _).aemeasurable
    hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with scene
  change (∫⁻ x, ENNReal.ofReal (f x) ∂(scene.1 : Measure _)) = _
  exact (ofReal_integral_eq_lintegral_ofReal f.integrable (.of_forall hf)).symm

/-- The actual unit spatial edge mass is a measurable scene readout. -/
theorem measurable_physicalScene_sourceUnitMass : Measurable
    (fun scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι}) :=
  (Measure.measurable_coe ((measurableSet_palmUnitCube ι).preimage measurable_fst.fst)).comp
    (measurable_localFiniteMeasure_coe.comp measurable_fst)

/-- Original uniform source-window bounds survive an actual weak scene limit,
including all original targets. The compact-test and Fatou inputs are produced
internally from the original source bump and edge exhaustion. -/
theorem lintegral_sourceUnitMass_le_of_weak_sourceWindow_bound
    (P : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hweak : Tendsto P atTop (𝓝 Q))
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hsub : palmUnitCube ι ⊆ U)
    (C : ℝ≥0∞)
    (hbound : ∀ n, (∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ U} ∂(P n : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C) :
    (∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C := by
  obtain ⟨bump, hbump, _, hsupp, hb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (show IsCompact (palmUnitCube ι) from isCompact_Icc) hU hsub
  let K := CompactExhaustion.choice (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
  let g : C((((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)), ℝ) :=
    ⟨fun e ↦ bump e.1.1, bump.continuous.comp continuous_fst.fst⟩
  let test (n : ℕ) := LocalFiniteMeasure.weightedContinuousTest
    (LocalFiniteMeasure.exhaustionCutoff K n) g
  have htest (n) (e) : test n e ∈ Icc (0 : ℝ) 1 := by
    have hcut := LocalFiniteMeasure.exhaustionCutoff_bounds K n e
    have hb' := hb e.1.1
    exact ⟨mul_nonneg hcut.1 hb'.1, mul_le_one₀ hcut.2 hb'.1 hb'.2⟩
  have hzero (n) (e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (he : e.1.1 ∉ U) : test n e = 0 := by
    have hb0 : bump e.1.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ he (hsupp h))
    change LocalFiniteMeasure.exhaustionCutoff K n e * bump e.1.1 = 0
    rw [hb0, mul_zero]
  have hnonneg (n) (scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :
      0 ≤ LocalFiniteMeasure.testIntegral scene.1 (test n) := integral_nonneg (fun e ↦ (htest n e).1)
  have hQtest (n) : (∫⁻ scene, ENNReal.ofReal
      (LocalFiniteMeasure.testIntegral scene.1 (test n)) ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C := by
    have hi := lintegral_abs_le_of_weak_uniform_bound Q P hweak
      (fun scene ↦ LocalFiniteMeasure.testIntegral scene.1 (test n))
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst) C ?_
    · simpa only [abs_of_nonneg (hnonneg n _)] using hi
    · intro k
      apply (lintegral_mono (fun scene ↦ ?_)).trans (hbound k)
      rw [abs_of_nonneg (hnonneg n scene)]
      exact integral_le_measure (fun e _ ↦ (htest n e).2) (fun e he ↦ (hzero n e he).le)
  have hpoint (e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :
      Tendsto (fun n ↦ ENNReal.ofReal (test n e)) atTop (𝓝 (ENNReal.ofReal (bump e.1.1))) := by
    obtain ⟨m, hm⟩ := K.exists_mem e
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop m] with n hn
    change ENNReal.ofReal (bump e.1.1) = ENNReal.ofReal (LocalFiniteMeasure.exhaustionCutoff K n e * bump e.1.1)
    rw [LocalFiniteMeasure.exhaustionCutoff_eq_one K n (K.subset hn hm), Pi.one_apply, one_mul]
  have hFatou := lintegral_liminf_le (u := (atTop : Filter ℕ)) (μ := physicalSceneMeanPlan (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))
    (fun n ↦ (show Measurable (fun e ↦ ENNReal.ofReal (test n e)) from
      ENNReal.measurable_ofReal.comp (test n).continuous.measurable))
  have hlim : (fun e ↦ atTop.liminf (fun n ↦ ENNReal.ofReal (test n e))) =
      (fun e ↦ ENNReal.ofReal (bump e.1.1)) := funext (fun e ↦ (hpoint e).liminf_eq)
  rw [hlim] at hFatou
  have hlimBound : atTop.liminf (fun n ↦ ∫⁻ e, ENNReal.ofReal (test n e)
      ∂physicalSceneMeanPlan (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C := by
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    exact .of_forall (fun n ↦ by
      rw [lintegral_meanPlan_ofReal_compactTest _ (test n) (fun e ↦ (htest n e).1)]
      exact hQtest n)
  have hmass : physicalSceneMeanPlan (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) {e | e.1.1 ∈ palmUnitCube ι} ≤ C := by
    apply le_trans _ (hFatou.trans hlimBound)
    apply meas_le_lintegral₀
    · exact (ENNReal.continuous_ofReal.comp (bump.continuous.comp continuous_fst.fst)).measurable.aemeasurable
    · intro e he
      rw [hbump he]
      simp
  change ((Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).bind
    (fun scene ↦ (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))))
      {e | e.1.1 ∈ palmUnitCube ι} ≤ C at hmass
  have hkernel : Measurable (fun scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))) :=
    measurable_localFiniteMeasure_coe.comp measurable_fst
  have hset : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
      e.1.1 ∈ palmUnitCube ι} :=
    (measurableSet_palmUnitCube ι).preimage measurable_fst.fst
  rwa [Measure.bind_apply hset hkernel.aemeasurable] at hmass

/-- A finite original joint unit-window moment supplies conditional finiteness
at almost every retained original macroscopic root. -/
theorem ae_condKernel_sourceUnitMass_lt_top
    {T : Type*} [MeasurableSpace T]
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) [IsFiniteMeasure ρ]
    (hfinite : (∫⁻ p, (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂ρ) < ∞) :
    ∀ᵐ w ∂ρ.fst, (∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂ρ.condKernel w) < ∞ := by
  have hW := measurable_physicalScene_sourceUnitMass (ι := ι)
  apply ae_lt_top (hW.lintegral_kernel (κ := ρ.condKernel))
  have hWjoint : Measurable (fun p : T ×
      CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι}) := hW.comp measurable_snd
  have heq := Measure.lintegral_condKernel (ρ := ρ) hWjoint
  simpa only [heq] using ne_of_lt hfinite

/-- Joint original-root stationarity and one original finite moment produce
actual qdim Campbell/Palm factorizations at almost every original root. -/
theorem ae_condKernel_physicalScenePairCampbell_eq_volume_prod_cubePalm
    {T : Type*} [MeasurableSpace T]
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) [IsFiniteMeasure ρ]
    (hjoint : ∀ v : ι → ℝ, MeasurePreserving (Prod.map id (physicalSceneReroot v)) ρ ρ)
    (hfinite : (∫⁻ p, (p.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂ρ) < ∞) :
    ∀ᵐ w ∂ρ.fst, physicalScenePairCampbell (ρ.condKernel w) =
      (volume : Measure (ι → ℝ)).prod (cubePalm ι (physicalScenePairCampbell (ρ.condKernel w))) := by
  filter_upwards [ae_forall_measurePreserving_physicalSceneReroot_condKernel ρ hjoint,
    ae_condKernel_sourceUnitMass_lt_top ρ hfinite] with w hw hm
  exact physicalScenePairCampbell_eq_volume_prod_cubePalm (ρ.condKernel w) hw hm

end OTSelector.Reconstruction
