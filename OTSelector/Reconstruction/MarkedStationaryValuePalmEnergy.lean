import OTSelector.Reconstruction.MarkedStationaryValuePalmUnitMoment

/-!
# Actual original paired-mark energy survives weak physical scene limits

A continuous nonnegative observable uses both original scalar clocks and the
full original transverse displacement. Compact edge cutoffs and a source bump
transfer its original source-window expectation through weak convergence; Fatou
removes every edge cutoff. The resulting bound is on the constructed actual
qdim pair Palm readout.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι]
local instance markedStationaryValuePalmEnergyLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

omit [Fintype ι] in
/-- The same original physical edge has continuously varying source location,
original clocks and full displacement vector. -/
theorem continuous_physicalPairAnchor : Continuous (physicalPairAnchor (ι := ι)) :=
  continuous_fst.fst.prodMk ((continuous_fst.snd.prodMk continuous_snd.snd).prodMk
    (continuous_snd.fst.sub continuous_fst.fst))

/-- The actual mean plan retains every measurable nonnegative original edge
readout with its exact original scene expectation. -/
theorem lintegral_physicalSceneMeanPlan
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {f : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ e, f e ∂physicalSceneMeanPlan P) =
      ∫⁻ scene, ∫⁻ e, f e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂P := by
  rw [physicalSceneMeanPlan, Measure.lintegral_bind (Kernel.measurable _).aemeasurable
    hf.aemeasurable]
  rfl

/-- Source-window restriction commutes with the actual original plan
expectation, without restricting or resampling the realized targets. -/
theorem setLIntegral_physicalSceneMeanPlan
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {f : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) → ℝ≥0∞} (hf : Measurable f)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) :
    (∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
      f e ∂physicalSceneMeanPlan P) =
      ∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
        f e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ∂P := by
  have hW : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} :=
    hU.preimage measurable_fst.fst
  simp_rw [← lintegral_indicator hW]
  exact lintegral_physicalSceneMeanPlan P (hf.indicator hW)

/-- A genuine uniform original source-window energy bound gives the same bound
for the actual pair Palm energy of a weak scene limit. All compact-test and
cutoff inputs are produced from the original observable. -/
theorem lintegral_cubePalm_le_of_weak_sourceWindow_energy_bound
    (P : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hweak : Tendsto P atTop (𝓝 Q))
    (f : PhysicalPairPalmMark ι → ℝ) (hf : Continuous f) (hf0 : ∀ m, 0 ≤ f m)
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hsub : palmUnitCube ι ⊆ U)
    (C : ℝ≥0∞)
    (hbound : ∀ n, (∫⁻ scene, ∫⁻ e in
      {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
      ENNReal.ofReal (f (physicalPairAnchor e).2)
      ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      ∂(P n : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C) :
    (∫⁻ m, ENNReal.ofReal (f m) ∂cubePalm ι
      (physicalScenePairCampbell (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))) ≤ C := by
  obtain ⟨bump, hbump, _, hsupp, hb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (show IsCompact (palmUnitCube ι) from isCompact_Icc) hU hsub
  let K := CompactExhaustion.choice (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
  let F : C((((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)), ℝ) :=
    ⟨fun e ↦ f (physicalPairAnchor e).2, hf.comp continuous_physicalPairAnchor.snd⟩
  let g : C((((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)), ℝ) :=
    ⟨fun e ↦ bump e.1.1 * F e,
      (bump.continuous.comp continuous_fst.fst).mul F.continuous⟩
  let test (n : ℕ) := LocalFiniteMeasure.weightedContinuousTest
    (LocalFiniteMeasure.exhaustionCutoff K n) g
  have hF0 (e) : 0 ≤ F e := hf0 _
  have htest0 (n) (e) : 0 ≤ test n e :=
    mul_nonneg (LocalFiniteMeasure.exhaustionCutoff_bounds K n e).1
      (mul_nonneg (hb e.1.1).1 (hF0 e))
  have htest_le (n) (e) : test n e ≤ F e := by
    exact (mul_le_of_le_one_left (mul_nonneg (hb e.1.1).1 (hF0 e))
      (LocalFiniteMeasure.exhaustionCutoff_bounds K n e).2).trans
        (mul_le_of_le_one_left (hF0 e) (hb e.1.1).2)
  have hzero (n) (e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (he : e.1.1 ∉ U) : test n e = 0 := by
    have hb0 : bump e.1.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ he (hsupp h))
    change LocalFiniteMeasure.exhaustionCutoff K n e * (bump e.1.1 * F e) = 0
    rw [hb0, zero_mul, mul_zero]
  have hUedge : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} :=
    hU.measurableSet.preimage measurable_fst.fst
  have hnonneg (n) (scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :
      0 ≤ LocalFiniteMeasure.testIntegral scene.1 (test n) := integral_nonneg (htest0 n)
  have hQtest (n) : (∫⁻ scene, ENNReal.ofReal
      (LocalFiniteMeasure.testIntegral scene.1 (test n))
      ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C := by
    have hi := lintegral_abs_le_of_weak_uniform_bound Q P hweak
      (fun scene ↦ LocalFiniteMeasure.testIntegral scene.1 (test n))
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst) C ?_
    · simpa only [abs_of_nonneg (hnonneg n _)] using hi
    · intro k
      apply (lintegral_mono (fun scene ↦ ?_)).trans (hbound k)
      rw [abs_of_nonneg (hnonneg n scene)]
      change ENNReal.ofReal (∫ e, test n e ∂(scene.1 : Measure _)) ≤ _
      rw [ofReal_integral_eq_lintegral_ofReal (test n).integrable (.of_forall (htest0 n)),
        ← lintegral_indicator hUedge]
      apply lintegral_mono
      intro e
      by_cases he : e.1.1 ∈ U
      · have hem : e ∈ {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} := he
        rw [indicator_of_mem hem]
        exact ENNReal.ofReal_le_ofReal (htest_le n e)
      · have hem : e ∉ {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} := he
        rw [indicator_of_notMem hem]
        change ENNReal.ofReal (test n e) ≤ 0
        rw [hzero n e he, ENNReal.ofReal_zero]
  have hpoint (e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :
      Tendsto (fun n ↦ ENNReal.ofReal (test n e)) atTop
        (𝓝 (ENNReal.ofReal (bump e.1.1 * F e))) := by
    obtain ⟨m, hm⟩ := K.exists_mem e
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop m] with n hn
    change ENNReal.ofReal (bump e.1.1 * F e) =
      ENNReal.ofReal (LocalFiniteMeasure.exhaustionCutoff K n e * (bump e.1.1 * F e))
    rw [LocalFiniteMeasure.exhaustionCutoff_eq_one K n (K.subset hn hm), Pi.one_apply, one_mul]
  have hFatou := lintegral_liminf_le (u := (atTop : Filter ℕ))
    (μ := physicalSceneMeanPlan (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))
    (fun n ↦ (show Measurable (fun e ↦ ENNReal.ofReal (test n e)) from
      ENNReal.measurable_ofReal.comp (test n).continuous.measurable))
  have hlim : (fun e ↦ atTop.liminf (fun n ↦ ENNReal.ofReal (test n e))) =
      (fun e ↦ ENNReal.ofReal (bump e.1.1 * F e)) := funext (fun e ↦ (hpoint e).liminf_eq)
  rw [hlim] at hFatou
  have hlimBound : atTop.liminf (fun n ↦ ∫⁻ e, ENNReal.ofReal (test n e)
      ∂physicalSceneMeanPlan (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C := by
    apply liminf_le_of_frequently_le'
    exact Filter.Eventually.frequently (.of_forall (fun n ↦ by
      rw [lintegral_meanPlan_ofReal_compactTest _ (test n) (htest0 n)]
      exact hQtest n))
  have hmass : (∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι},
      ENNReal.ofReal (F e) ∂physicalSceneMeanPlan
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ C := by
    apply le_trans _ (hFatou.trans hlimBound)
    have hunitEdge : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
        e.1.1 ∈ palmUnitCube ι} := (measurableSet_palmUnitCube ι).preimage measurable_fst.fst
    rw [← lintegral_indicator hunitEdge]
    apply lintegral_mono
    intro e
    by_cases he : e.1.1 ∈ palmUnitCube ι
    · have hem : e ∈ {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι} := he
      rw [indicator_of_mem hem]
      change ENNReal.ofReal (F e) ≤ ENNReal.ofReal (bump e.1.1 * F e)
      rw [hbump he, Pi.one_apply, one_mul]
    · have hem : e ∉ {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι} := he
      rw [indicator_of_notMem hem]
      exact bot_le
  rw [setLIntegral_physicalSceneMeanPlan _
    (show Measurable (fun e ↦ ENNReal.ofReal (F e)) from ENNReal.measurable_ofReal.comp F.continuous.measurable)
    (measurableSet_palmUnitCube ι)] at hmass
  have hfnn : Measurable (fun m : PhysicalPairPalmMark ι ↦ ENNReal.ofReal (f m)) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  rw [lintegral_cubePalm_physicalScenePairCampbell _ hfnn]
  exact hmass

end OTSelector.Reconstruction
