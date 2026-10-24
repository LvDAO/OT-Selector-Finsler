import OTSelector.Reconstruction.OriginalIIDActualConditionalMatching
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplaceMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMoment
import OTSelector.Reconstruction.MarkedStationaryValuePalmMarginals
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilationPalm
import OTSelector.MeasureTheory.CompactTestDetermination

/-!
# Actual conditional input means and unnormalized original Palm measures

The original compact Poisson profile retains its physical intensity theta.
No source-anchored Palm is assumed to have unit mass before spatial dilation.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000

local instance originalConditionalCandidatePointStandardBorel (q : ℕ) :
    StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance originalConditionalCandidateInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance originalConditionalCandidatePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The actual finite reference has its original theta-scaled first moment. -/
theorem lintegral_originalFinitePoissonInputLaw_test
    (q : ℕ) {S : ℝ} (hS : 0 < S) (θ : ℝ)
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (F : C_c((Fin q → ℝ) × ℝ, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (hzero : ∀ x, x.1 ∉ haarRootCube (Fin q) S → F x = 0) :
    (∫⁻ μ, ENNReal.ofReal (LocalFiniteMeasure.testIntegral μ F)
      ∂originalFinitePoissonInputLaw q hS θ α) =
      ENNReal.ofReal θ * ∫⁻ x, ENNReal.ofReal (F x)
        ∂(volume : Measure (Fin q → ℝ)).prod α := by
  let U := haarRootCube (Fin q) S
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have hν : IsProbabilityMeasure ν := isProbabilityMeasure_originalFinitePoissonWindowPointLaw q hS
  have hU : MeasurableSet U := measurableSet_Icc
  have hfin : volume U ≠ ⊤ := isCompact_Icc.measure_ne_top
  have hpos : volume U ≠ 0 := by
    dsimp only [U]
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  unfold originalFinitePoissonInputLaw
  rw [lintegral_map (LocalFiniteMeasure.continuous_testIntegral F).measurable.ennreal_ofReal
    (measurable_originalFinitePoissonBlockLocal (0 : (Fin q → ℝ) × ℝ))]
  simp_rw [testIntegral_originalFinitePoissonBlockLocal]
  rw [lintegral_legalInputBlockTest_ofReal (ν.prod α)
    (θ.toNNReal * (volume U).toNNReal) F F.continuous.measurable hF
    (fun x ↦ F.toBoundedContinuousFunction.norm_coe_le_norm x)]
  have hmass : ((θ.toNNReal * (volume U).toNNReal : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal θ * volume U := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hfin]
    congr 1
  have hscale : volume U * (∫⁻ x, ENNReal.ofReal (F x) ∂ν.prod α) =
      ∫⁻ x, ENNReal.ofReal (F x) ∂((volume : Measure (Fin q → ℝ)).restrict U).prod α := by
    change volume U • (∫⁻ x, ENNReal.ofReal (F x) ∂ν.prod α) = _
    rw [← lintegral_smul_measure,physicalIntensity_smul_normalized_window q hfin hpos α]
  rw [hmass,mul_assoc,hscale]
  congr 1
  rw [Measure.restrict_prod_eq_prod_univ,
    ← lintegral_indicator (hU.prod MeasurableSet.univ)]
  apply lintegral_congr
  intro x
  by_cases hx : x.1 ∈ U
  · rw [indicator_of_mem (show x ∈ U ×ˢ univ from ⟨hx, mem_univ _⟩)]
  · rw [indicator_of_notMem (show x ∉ U ×ˢ univ from fun h ↦ hx h.1),
      hzero x hx, ENNReal.ofReal_zero]

/-- A genuine compact Poisson profile identifies the extended first moment,
without a supplied moment bound or a new random input experiment. -/
theorem lintegral_testIntegral_of_original_compact_poisson_profile
    (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (Q : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ))) [IsProbabilityMeasure Q]
    (hLaplace : ∀ F : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
      (∫ μ, legalInputMeasureLaplace F μ ∂Q) =
        Real.exp (-(θ * ∫ x, 1 - Real.exp (-F.1 x) ∂volume.prod α)))
    (F : C_c((Fin q → ℝ) × ℝ, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫⁻ μ, ENNReal.ofReal (LocalFiniteMeasure.testIntegral μ F) ∂Q) =
      ENNReal.ofReal θ * ∫⁻ x, ENNReal.ofReal (F x) ∂volume.prod α := by
  obtain ⟨S,hS,hzero⟩ := exists_originalInput_spatial_cube_support q F
  let R := originalFinitePoissonInputLaw q hS θ α
  have hR : IsProbabilityMeasure R := isProbabilityMeasure_originalFinitePoissonInputLaw q hS θ α
  let X := fun μ : LocalFiniteMeasure ((Fin q → ℝ) × ℝ) ↦ LocalFiniteMeasure.testIntegral μ F
  have hX : Measurable X := (LocalFiniteMeasure.continuous_testIntegral F).measurable
  have hXn : ∀ μ, 0 ≤ X μ := fun μ ↦ integral_nonneg hF
  have heq := lintegral_ofReal_eq_of_nonnegative_laplace_eq Q R X X hX hX hXn hXn (by
    intro a ha
    let aF : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ) :=
      ⟨a • F, fun x ↦ mul_nonneg ha.le (hF x)⟩
    have hzeroa : ∀ x, x.1 ∉ haarRootCube (Fin q) S → aF.1 x = 0 := by
      intro x hx
      change a * F x = 0
      rw [hzero x hx,mul_zero]
    have hl := (hLaplace aF).trans
      (integral_originalFinitePoissonInputLaw_laplace_eq q hS θ hθ α aF hzeroa).symm
    have hh (μ : LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) :
        legalInputMeasureLaplace aF μ = Real.exp (-a * X μ) := by
      change Real.exp (-(∫ x, a * F x ∂(μ : Measure _))) = _
      rw [integral_const_mul,neg_mul]
      rfl
    simpa only [hh] using hl)
  exact heq.trans (lintegral_originalFinitePoissonInputLaw_test q hS θ α F hF hzero)

/-- The complete physical mean of the same original input, with its true
intensity theta retained, follows from the proven compact Poisson profile. -/
theorem original_input_mean_eq_of_compact_poisson_profile
    (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (Q : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ))) [IsProbabilityMeasure Q]
    (hLaplace : ∀ F : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
      (∫ μ, legalInputMeasureLaplace F μ ∂Q) =
        Real.exp (-(θ * ∫ x, 1 - Real.exp (-F.1 x) ∂volume.prod α))) :
    Q.bind localFiniteMeasureKernel =
      ENNReal.ofReal θ • (volume : Measure (Fin q → ℝ)).prod α := by
  have hfiniteMean : IsFiniteMeasureOnCompacts
      (ENNReal.ofReal θ • (volume : Measure (Fin q → ℝ)).prod α) := ⟨by
    intro K hK
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
  apply measure_eq_of_nonnegative_compact_lintegrals
  intro F hF
  have hfm : Measurable (fun x : (Fin q → ℝ) × ℝ ↦ ENNReal.ofReal (F x)) :=
    F.continuous.measurable.ennreal_ofReal
  rw [Measure.lintegral_bind (μ := localFiniteMeasureKernel) (m := Q)
    (f := fun x ↦ ENNReal.ofReal (F x)) (Kernel.measurable _).aemeasurable hfm.aemeasurable,
    lintegral_smul_measure]
  have hpoint (μ : LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) :
      (∫⁻ x, ENNReal.ofReal (F x) ∂localFiniteMeasureKernel μ) =
        ENNReal.ofReal (LocalFiniteMeasure.testIntegral μ F) := by
    change (∫⁻ x, ENNReal.ofReal (F x) ∂(μ : Measure ((Fin q → ℝ) × ℝ))) = _
    exact (ofReal_integral_eq_lintegral_ofReal F.integrable (.of_forall hF)).symm
  simp_rw [hpoint]
  exact lintegral_testIntegral_of_original_compact_poisson_profile q θ hθ α Q hLaplace F hF

/-- Complete original endpoint marginals and the actual compact input
profile produce the two physical mean intensities, including their theta mass. -/
theorem original_scene_intensities_eq_of_compact_poisson_profile
    (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))) [IsProbabilityMeasure Q]
    (hmarg : ∀ᵐ s ∂Q,
      (s.1.1 : Measure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))).fst =
          (s.2.1 : Measure ((Fin q → ℝ) × ℝ)) ∧
        (s.1.1 : Measure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))).snd =
          (s.2.2 : Measure ((Fin q → ℝ) × ℝ)))
    (hLaplace : ∀ H G : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
      (∫ z, legalInputMeasureLaplacePair H G z ∂Q.map Prod.snd) =
        Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂volume.prod α) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂volume.prod β)))) :
    physicalSceneSourceIntensity (Q.map Prod.fst) =
        ENNReal.ofReal θ • (volume : Measure (Fin q → ℝ)).prod α ∧
      physicalSceneTargetIntensity (Q.map Prod.fst) =
        ENNReal.ofReal θ • (volume : Measure (Fin q → ℝ)).prod β := by
  let X := (Fin q → ℝ) × ℝ
  let Scene := OriginalIIDMaskedMacroInputScene (Fin q)
  let P := Q.map (Prod.snd : Scene → LocalFiniteMeasure X × LocalFiniteMeasure X)
  have hP : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hS : IsProbabilityMeasure (P.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hT : IsProbabilityMeasure (P.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  obtain ⟨hSLap,hTLap⟩ := originalInput_marginal_laplace_of_pair_profile P θ
    (volume.prod α) (volume.prod β) hLaplace
  have hs := original_input_mean_eq_of_compact_poisson_profile q θ hθ α (P.map Prod.fst) hSLap
  have ht := original_input_mean_eq_of_compact_poisson_profile q θ hθ β (P.map Prod.snd) hTLap
  have hsmap : P.map Prod.fst = Q.map (fun s : Scene ↦ s.2.1) := by
    rw [Measure.map_map measurable_fst measurable_snd]
    rfl
  have htmap : P.map Prod.snd = Q.map (fun s : Scene ↦ s.2.2) := by
    rw [Measure.map_map measurable_snd measurable_snd]
    rfl
  rw [hsmap] at hs
  rw [htmap] at ht
  constructor
  · refine Eq.trans ?_ hs
    ext B hB
    rw [physicalSceneSourceIntensity,
      Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
      Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
      lintegral_map (Kernel.measurable_coe _ hB) measurable_fst,
      lintegral_map (Kernel.measurable_coe _ hB) measurable_snd.fst]
    apply lintegral_congr_ae
    filter_upwards [hmarg] with s h
    have hk : physicalSceneSourceKernel s.1 =
        (s.1.1 : Measure (X × X)).map Prod.fst :=
      Kernel.map_apply _ measurable_fst s.1
    rw [hk]
    exact congrArg (fun μ : Measure X ↦ μ B) h.1
  · refine Eq.trans ?_ ht
    ext B hB
    rw [physicalSceneTargetIntensity,
      Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
      Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
      lintegral_map (Kernel.measurable_coe _ hB) measurable_fst,
      lintegral_map (Kernel.measurable_coe _ hB) measurable_snd.snd]
    apply lintegral_congr_ae
    filter_upwards [hmarg] with s h
    have hk : physicalSceneTargetKernel s.1 =
        (s.1.1 : Measure (X × X)).map Prod.snd :=
      Kernel.map_apply _ measurable_snd s.1
    rw [hk]
    exact congrArg (fun μ : Measure X ↦ μ B) h.2

/-- The same raw actual matching has its genuine Campbell product and Palm
mass theta. Its clock marginals are theta times the original probability laws. -/
theorem original_raw_campbell_of_stationary_full_input_profile
    (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))) [IsProbabilityMeasure Q]
    (hstat : ∀ v, MeasurePreserving (originalIIDMaskedMacroInputSceneReroot v) Q Q)
    (hfull : ∀ᵐ s ∂Q, IsFullOriginalBipartiteMatching
      (0 : (Fin q → ℝ) × ℝ) (0 : (Fin q → ℝ) × ℝ) s.1.1 s.2.1 s.2.2)
    (hLaplace : ∀ H G : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
      (∫ z, legalInputMeasureLaplacePair H G z ∂Q.map Prod.snd) =
        Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂volume.prod α) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂volume.prod β)))) :
    let P := Q.map Prod.fst
    let palm := cubePalm (Fin q) (physicalScenePairCampbell P)
    (∀ v, MeasurePreserving (physicalSceneReroot v) P P) ∧
      physicalScenePairCampbell P = (volume : Measure (Fin q → ℝ)).prod palm ∧
      palm univ = ENNReal.ofReal θ ∧
      palm.map (fun m ↦ m.1.1) = ENNReal.ofReal θ • α ∧
      palm.map (fun m ↦ m.1.2) = ENNReal.ofReal θ • β := by
  intro P palm
  obtain ⟨hsource,htarget⟩ := original_scene_intensities_eq_of_compact_poisson_profile
    q θ hθ α β Q (hfull.mono fun s hs ↦ ⟨hs.source_marginal,hs.target_marginal⟩) hLaplace
  have hPstat (v : Fin q → ℝ) : MeasurePreserving (physicalSceneReroot v) P P := by
    refine ⟨(continuous_physicalSceneReroot v).measurable, ?_⟩
    change (Q.map Prod.fst).map (physicalSceneReroot v) = Q.map Prod.fst
    rw [Measure.map_map (continuous_physicalSceneReroot v).measurable measurable_fst]
    have heq : physicalSceneReroot v ∘ Prod.fst =
        Prod.fst ∘ originalIIDMaskedMacroInputSceneReroot (ι := Fin q) v := rfl
    rw [heq, ← Measure.map_map measurable_fst
      (continuous_originalIIDMaskedMacroInputSceneReroot v).measurable, (hstat v).map_eq]
  have hunitEq : (∫⁻ scene, (scene.1 : Measure
      (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂P) = ENNReal.ofReal θ := by
    rw [← physicalSceneSourceIntensity_unitCube, hsource,
      Measure.smul_apply,smul_eq_mul,Measure.prod_prod,volume_palmUnitCube,
      measure_univ,mul_one,mul_one]
  have hunit : (∫⁻ scene, (scene.1 : Measure
      (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂P) < ∞ := by
    rw [hunitEq]
    exact ENNReal.ofReal_lt_top
  have hmass : palm univ = ENNReal.ofReal θ := by
    rw [cubePalm_apply (Fin q) _ MeasurableSet.univ,physicalScenePairCampbell_unitCube]
    exact hunitEq
  have hs : physicalSceneSourceIntensity P =
      (volume : Measure (Fin q → ℝ)).prod (ENNReal.ofReal θ • α) := by
    rw [Measure.prod_smul_right]
    exact hsource
  have ht : physicalSceneTargetIntensity P =
      (volume : Measure (Fin q → ℝ)).prod (ENNReal.ofReal θ • β) := by
    rw [Measure.prod_smul_right]
    exact htarget
  obtain ⟨hclockS,hclockT⟩ := cubePalm_physicalScenePairCampbell_clock_marginals
    P hPstat hunit (ENNReal.ofReal θ • α) (ENNReal.ofReal θ • β) hs ht
  exact ⟨hPstat,physicalScenePairCampbell_eq_volume_prod_cubePalm P hPstat hunit,
    hmass,hclockS,hclockT⟩

/-- Both actual original plan copies undergo the same physical dilation. -/
def originalPairSceneDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (s : CavityLocalScene ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ)) :=
  (localFiniteMapHomeomorph (legalMarkedEdgeDilation q c hc) s.1,
    localFiniteMapHomeomorph (legalMarkedEdgeDilation q c hc) s.2)

theorem continuous_originalPairSceneDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0) :
    Continuous (originalPairSceneDilation q c hc) :=
  ((continuous_localFiniteMapHomeomorph _).comp continuous_fst).prodMk
    ((continuous_localFiniteMapHomeomorph _).comp continuous_snd)

/-- Dilation pushes the actual Campbell measure of the same raw plan law. -/
theorem original_pair_campbell_dilation (q : ℕ)
    (P : Measure (CavityLocalScene ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ)))
    (c : ℝ) (hc : c ≠ 0) :
    physicalScenePairCampbell (P.map (originalPairSceneDilation q c hc)) =
      (physicalScenePairCampbell P).map (legalPairAnchorDilation q c) := by
  ext B hB
  have hpre : MeasurableSet (legalPairAnchorDilation q c ⁻¹' B) :=
    hB.preimage (measurable_legalPairAnchorDilation q c)
  rw [Measure.map_apply (measurable_legalPairAnchorDilation q c) hB]
  simp only [physicalScenePairCampbell,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hpre (Kernel.measurable _).aemeasurable]
  rw [lintegral_map (Kernel.measurable_coe _ hB)
    (continuous_originalPairSceneDilation q c hc).measurable]
  apply lintegral_congr
  intro s
  rw [physicalScenePairKernel_apply, physicalScenePairKernel_apply]
  change (((s.1 : Measure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))).map
      (legalMarkedEdgeDilation q c hc)).map physicalPairAnchor) B =
    ((s.1 : Measure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))).map physicalPairAnchor)
      (legalPairAnchorDilation q c ⁻¹' B)
  rw [Measure.map_map measurable_physicalPairAnchor
      (legalMarkedEdgeDilation q c hc).continuous.measurable,
    Measure.map_apply measurable_physicalPairAnchor hpre,
    Measure.map_apply (measurable_physicalPairAnchor.comp
      (legalMarkedEdgeDilation q c hc).continuous.measurable) hB]
  congr 1
  ext e
  simp only [mem_preimage,Function.comp_def,physicalPairAnchor_legalMarkedEdgeDilation]

/-- The raw Palm has its exact physical Jacobian under dilation. Finite
Campbell mass suffices; the raw Palm is not assumed to be a probability. -/
theorem original_raw_palm_dilation (q : ℕ)
    (P : Measure (CavityLocalScene ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P)
    (hunit : (∫⁻ scene, (scene.1 : Measure
      (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂P) < ∞)
    (c : ℝ) (hc : c ≠ 0) :
    cubePalm (Fin q) (physicalScenePairCampbell (P.map (originalPairSceneDilation q c hc))) =
      ENNReal.ofReal |(c ^ q)⁻¹| •
        (cubePalm (Fin q) (physicalScenePairCampbell P)).map (legalPairMarkDilation q c) := by
  let η := cubePalm (Fin q) (physicalScenePairCampbell P)
  have hη : IsFiniteMeasure η := ⟨by
    change cubePalm (Fin q) (physicalScenePairCampbell P) univ < ∞
    rw [cubePalm_apply (Fin q) _ MeasurableSet.univ,physicalScenePairCampbell_unitCube]
    exact hunit⟩
  have hcamp : physicalScenePairCampbell P = (volume : Measure (Fin q → ℝ)).prod η :=
    physicalScenePairCampbell_eq_volume_prod_cubePalm P hstat hunit
  have hvol : (volume : Measure (Fin q → ℝ)).map (fun x ↦ c • x) =
      ENNReal.ofReal |(c ^ q)⁻¹| • (volume : Measure (Fin q → ℝ)) := by
    simpa using Measure.map_addHaar_smul (volume : Measure (Fin q → ℝ)) hc
  have hnew : physicalScenePairCampbell (P.map (originalPairSceneDilation q c hc)) =
      ENNReal.ofReal |(c ^ q)⁻¹| •
        ((volume : Measure (Fin q → ℝ)).prod (η.map (legalPairMarkDilation q c))) := by
    rw [original_pair_campbell_dilation,hcamp]
    change ((volume : Measure (Fin q → ℝ)).prod η).map
      (Prod.map (fun x ↦ c • x) (legalPairMarkDilation q c)) = _
    calc
      _ = ((volume : Measure (Fin q → ℝ)).map (fun x ↦ c • x)).prod
          (η.map (legalPairMarkDilation q c)) :=
        (Measure.map_prod_map _ _ (measurable_id.const_smul c)
          (measurable_legalPairMarkDilation q c)).symm
      _ = _ := by rw [hvol,Measure.prod_smul_left]
  ext B hB
  rw [cubePalm_apply (Fin q) _ hB,hnew,Measure.smul_apply,Measure.prod_prod,
    volume_palmUnitCube,one_mul,Measure.smul_apply]

/-- Spatial normalization of a genuine raw intensity theta Palm is performed
by the actual point-process dilation, retaining both original clock marginals. -/
theorem original_unit_palm_of_raw_dilation
    (q : ℕ) (P : Measure (CavityLocalScene ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P)
    (θ : ℝ) (hθ : 0 < θ)
    (α β : Measure ℝ)
    (hmass : cubePalm (Fin q) (physicalScenePairCampbell P) univ = ENNReal.ofReal θ)
    (hsource : (cubePalm (Fin q) (physicalScenePairCampbell P)).map (fun m ↦ m.1.1) = ENNReal.ofReal θ • α)
    (htarget : (cubePalm (Fin q) (physicalScenePairCampbell P)).map (fun m ↦ m.1.2) = ENNReal.ofReal θ • β)
    (c : ℝ) (hc : c ≠ 0) (hjac : |(c ^ q)⁻¹| = θ⁻¹) :
    let palm := cubePalm (Fin q) (physicalScenePairCampbell
      (P.map (originalPairSceneDilation q c hc)))
    IsProbabilityMeasure palm ∧ palm.map (fun m ↦ m.1.1) = α ∧
      palm.map (fun m ↦ m.1.2) = β := by
  intro palm
  have hunit : (∫⁻ scene, (scene.1 : Measure
      (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂P) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube,← cubePalm_apply (Fin q) _ MeasurableSet.univ,hmass]
    exact ENNReal.ofReal_lt_top
  have hd := original_raw_palm_dilation q P hstat hunit c hc
  rw [hjac] at hd
  have hcancel : ENNReal.ofReal θ⁻¹ * ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hθ.le),inv_mul_cancel₀ hθ.ne',ENNReal.ofReal_one]
  have hp : IsProbabilityMeasure palm := ⟨by
    change cubePalm (Fin q) _ univ = 1
    rw [hd,Measure.smul_apply,smul_eq_mul,
      Measure.map_apply (measurable_legalPairMarkDilation q c) MeasurableSet.univ,
      preimage_univ,hmass,hcancel]⟩
  have hclock (f : PhysicalPairPalmMark (Fin q) → ℝ) (hf : Measurable f)
      (hinv : f ∘ legalPairMarkDilation q c = f)
      (γ : Measure ℝ)
      (hγ : (cubePalm (Fin q) (physicalScenePairCampbell P)).map f = ENNReal.ofReal θ • γ) :
      palm.map f = γ := by
    change (cubePalm (Fin q) _).map f = γ
    rw [hd,Measure.map_smul,Measure.map_map hf (measurable_legalPairMarkDilation q c),
      hinv,hγ,smul_smul,hcancel,one_smul]
  exact ⟨hp,hclock _ measurable_fst.fst rfl α hsource,
    hclock _ measurable_fst.snd rfl β htarget⟩

/-- Actual plan dilation conjugates the original physical translation. -/
theorem original_pair_reroot_dilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (v : Fin q → ℝ) (s : CavityLocalScene ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ)) :
    physicalSceneReroot v (originalPairSceneDilation q c hc s) =
      originalPairSceneDilation q c hc (physicalSceneReroot (c⁻¹ • v) s) := by
  let Z : LocalFiniteMeasure (LegalColoredInputPoint q) := ⟨0,inferInstance⟩
  exact congrArg Prod.fst (legalMarkedInputSceneReroot_dilation q c hc v (s,Z))

/-- The same actual stationary pair law stays stationary after spatial dilation. -/
theorem original_pair_dilation_stationary (q : ℕ)
    (P : Measure (CavityLocalScene ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P)
    (c : ℝ) (hc : c ≠ 0) (v : Fin q → ℝ) :
    MeasurePreserving (physicalSceneReroot v)
      (P.map (originalPairSceneDilation q c hc)) (P.map (originalPairSceneDilation q c hc)) := by
  refine ⟨(continuous_physicalSceneReroot v).measurable,?_⟩
  rw [Measure.map_map (continuous_physicalSceneReroot v).measurable
    (continuous_originalPairSceneDilation q c hc).measurable]
  have heq : physicalSceneReroot v ∘ originalPairSceneDilation q c hc =
      originalPairSceneDilation q c hc ∘ physicalSceneReroot (c⁻¹ • v) :=
    funext fun s ↦ original_pair_reroot_dilation q c hc v s
  rw [heq,← Measure.map_map (continuous_originalPairSceneDilation q c hc).measurable
    (continuous_physicalSceneReroot (c⁻¹ • v)).measurable,(hstat _).map_eq]

/-- The positive physical dilation that turns an actual theta intensity into one. -/
theorem original_unit_density_dilation_exists (q : ℕ) (hq : 0 < q)
    (θ : ℝ) (hθ : 0 < θ) : ∃ d : ℝ, 0 < d ∧ d ^ q = θ := by
  refine ⟨θ ^ (q : ℝ)⁻¹,Real.rpow_pos_of_pos hθ _,?_⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Real.rpow_natCast,← Real.rpow_mul hθ.le,inv_mul_cancel₀ hq0,Real.rpow_one]

section SupportedOriginalCampbell
open Metric Module Manifold OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ContDiff NNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

variable
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)

local instance originalConditionalCampbellCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance originalConditionalCampbellCoreConfigTopology (q : ℕ) :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance originalConditionalCampbellCoreConfigBorel (q : ℕ) :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance originalConditionalCampbellCoreConfigPolish (q : ℕ) :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance originalConditionalCampbellCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance originalConditionalCampbellCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance originalConditionalCampbellCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance originalConditionalCampbellCorePlanNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

local instance originalConditionalCampbellCoreMacroPairPolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance originalConditionalCampbellCoreSceneBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance originalConditionalCampbellCoreMacroBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance originalConditionalCampbellCoreMacroPairBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance

local instance originalConditionalCampbellCoreScenePolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance originalConditionalCampbellCoreSceneStandardBorel (q : ℕ) :
    StandardBorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance originalConditionalCampbellCoreTaggedSceneBorel (q : ℕ) :
    BorelSpace ((Fin q → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist

/-- The same actual supported iid optimizer weak limit produces its
unnormalized theta-Palm and exact Campbell product. No probability-Palm,
Campbell, intensity or prescribed-law callback is supplied. -/
theorem PopulationLocalPressureCore.original_supported_conditional_raw_campbell
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (bins : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (Ksupport : Set M) (hK : IsCompact Ksupport)
    (hμK : ∀ᵐ x ∂μ, x ∈ Ksupport) (hνK : ∀ᵐ y ∂ν, y ∈ Ksupport)
    (f : (Ksupport × Ksupport) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (hdata : D.originalSupportedWeightUnitDensityPressureData
      (μ := (⟨μ, inferInstance⟩ : ProbabilityMeasure M))
      (ν := (⟨ν, inferInstance⟩ : ProbabilityMeasure M)) γ originalGap bins U
      retentionError splitError Ksupport hK hμK hνK f g ε probeError
      (fun n ↦ canonicalLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure M)
        (⟨ν, inferInstance⟩ : ProbabilityMeasure M) n)
      (fun n ↦ canonicalX n) (fun n ↦ canonicalY n))
    (t : ℝ) (hdim : 2 ≤ finrank ℝ E) (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let V := Fin q → ℝ
    let X := V × ℝ
    let Scene := OriginalIIDMaskedMacroInputScene (Fin q)
    let Macro := OriginalIIDMaskedMacroCarrier (0 : X)
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let φ := fun x ↦ e (R (a x))
    let K := e '' (R '' C.roots)
    let scale := physicalSceneCanonicalHaarScale q
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) C.seedIndex
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let θ := fun c ↦ originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex (ref c)
    let α := fun c ↦ condDistrib u a μ (ref c)
    let β := fun c ↦ condDistrib u a ν (ref c)
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    let cost := fun n x y ↦ finslerMeanScale E n *
      ((F.lengthEDist x y).toReal - u y + u x) +
        t * finslerCarrierProbe (⟨μ,inferInstance⟩ : ProbabilityMeasure M)
          (⟨ν,inferInstance⟩ : ProbabilityMeasure M) Ksupport hK.measurableSet hμK hνK f x y
    let hcost : ∀ n, Measurable (Function.uncurry (cost n)) := fun n ↦
      measurable_originalIID_supported_tilt_cost hcomplete
      (⟨μ,inferInstance⟩ : ProbabilityMeasure M) (⟨ν,inferInstance⟩ : ProbabilityMeasure M)
      Ksupport hK.measurableSet hμK hνK u hu f (finslerMeanScale E n) t
    let hm : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
    let hφ : Measurable φ := by
      have hp := measurable_physicalSceneOriginalSeedScaledPosition
        (P := P) (a := a) hF hcomplete hu ha hinj C.seedIndex (1 : ℝ)
      change Measurable (fun x ↦ (1 : ℝ) • φ x) at hp
      simpa only [one_smul] using hp
    let huM : Measurable u := by
      let _actualConditionalMatchingMetric : MetricSpace M := F.metricSpace
      exact hu.continuous.measurable
    ∀ m : ℕ → ℕ, StrictMono m → ∀ L : ProbabilityMeasure (Macro × Macro),
      Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν
        (by simpa using original_seed_transverse_finrank_pos S hdim)
        (cost (m n)) (hcost (m n)) 1 (m n) mask hm
        (fun x ↦ scale (m n) • φ x) (hφ.const_smul (scale (m n))) u huM)
        atTop (𝓝 L) →
      let ρ := (L.map
        (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
        Measure (V × Scene))
      ∀ᵐ c ∂(η : Measure V).restrict K,
        let P := (ρ.condKernel c).map Prod.fst
        let palm := cubePalm (Fin q) (physicalScenePairCampbell P)
        (∀ w : V, MeasurePreserving (physicalSceneReroot w) P P) ∧
          physicalScenePairCampbell P = (volume : Measure V).prod palm ∧
          palm univ = ENNReal.ofReal (θ c) ∧
          palm.map (fun m ↦ m.1.1) = ENNReal.ofReal (θ c) • α c ∧
          palm.map (fun m ↦ m.1.2) = ENNReal.ofReal (θ c) • β c ∧
          (0 < θ c → ∃ (d : ℝ) (hd : 0 < d), d ^ q = θ c ∧
            let Punit := P.map (originalPairSceneDilation q d hd.ne')
            let unitPalm := cubePalm (Fin q) (physicalScenePairCampbell Punit)
            (∀ w, MeasurePreserving (physicalSceneReroot w) Punit Punit) ∧
              IsProbabilityMeasure unitPalm ∧
              unitPalm.map (fun m ↦ m.1.1) = α c ∧
              unitPalm.map (fun m ↦ m.1.2) = β c) := by
  intro C S q V X Scene Macro R e φ K scale mask ref θ α β η cost hcost hmask hφ huM
  obtain ⟨Γ,hΓ,hall⟩ := D.original_supported_conditional_full_matching
    (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
    (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
    (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
    (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
    γ originalGap bins U retentionError splitError Ksupport hK hμK hνK f g ε probeError hdata t hdim i
  intro m hm L hw ρ
  have hroot := (hall m hm L hw).2.2
  filter_upwards [hroot] with c hc
  have hθ : 0 ≤ θ c := mul_nonneg (NNReal.coe_nonneg _)
    (populationAtlasTheta_nonneg P a κ (μ.map a) C.seedIndex (ref c))
  have hraw := original_raw_campbell_of_stationary_full_input_profile q (θ c) hθ (α c) (β c)
    (ρ.condKernel c) hc.2.2.1
    (hc.2.2.2.2.2.mono fun z hz ↦ hz.2.1) hc.2.2.2.1
  refine ⟨hraw.1,hraw.2.1,hraw.2.2.1,hraw.2.2.2.1,hraw.2.2.2.2,?_⟩
  intro hpositive
  obtain ⟨d,hd,hpow⟩ := original_unit_density_dilation_exists q
    (original_seed_transverse_finrank_pos S hdim) (θ c) hpositive
  refine ⟨d,hd,hpow,original_pair_dilation_stationary q _ hraw.1 d hd.ne',?_⟩
  exact original_unit_palm_of_raw_dilation q _ hraw.1 (θ c) hpositive (α c) (β c)
    hraw.2.2.1 hraw.2.2.2.1 hraw.2.2.2.2 d hd.ne'
    (by rw [hpow,abs_of_pos (inv_pos.mpr hpositive)])

end SupportedOriginalCampbell

end OTSelector.Reconstruction
