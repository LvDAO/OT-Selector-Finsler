import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryOriginalInputIntensity
import OTSelector.Probability.RandomMeasureFullness

/-!
# Full original endpoint marginals from the same true Palm and input law

Equal complete input laws preserve their original color mean measures. The
true probability Palm and its two original clock laws produce the same source
and target mean intensities of the actual stationary matching. Original
endpoint domination and countably many finite compact input means then recover
both whole marginals almost surely.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
local instance markedStationaryValueLegalOriginalMeanMarginalFullnessInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalOriginalMeanMarginalFullnessPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The complete actual input law determines both original color mean
measures, regardless of the retained edge plan or matching fullness. -/
theorem legalMarkedInputColorIntensity_eq_of_inputLaw_eq
    {q : ℕ} (P Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hinput : (P : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) (c : Fin 2) :
    legalMarkedInputColorIntensity q (P : Measure (LegalMarkedOptimalInputScene q)) c =
      legalMarkedInputColorIntensity q (Q : Measure (LegalMarkedOptimalInputScene q)) c := by
  ext B hB
  let Z : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) := ⟨0, inferInstance⟩
  have hm : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      legalInputColorMeasure q μ c B) := by
    have h := (Kernel.measurable_coe (legalMarkedInputColorKernel q c) hB).comp
      ((measurable_const (a := Z)).prodMk (measurable_const (a := Z)) |>.prodMk measurable_id)
    simpa only [legalMarkedInputColorKernel_apply, Function.comp_def, id_eq] using h
  have heq := congrArg (fun R : Measure (LocalFiniteMeasure (LegalColoredInputPoint q)) ↦
    ∫⁻ μ, legalInputColorMeasure q μ c B ∂R) hinput
  rw [lintegral_map hm measurable_snd, lintegral_map hm measurable_snd] at heq
  rw [legalMarkedInputColorIntensity, legalMarkedInputColorIntensity,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
  simpa only [legalMarkedInputColorKernel_apply, Function.comp_def, id_eq] using heq

/-- A probability true Palm with the unchanged original clocks recovers both
whole endpoint marginals, once the same actual input law and original
endpoint domination have been retained. No proper projection is assumed. -/
theorem ae_original_marginals_eq_input_of_truePalm_clock_marginals
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M₀ : LegalWeightedStationaryPoissonMatching q α β kin g)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hinput : (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (M₀.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd)
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)))
    (hprob : IsProbabilityMeasure (legalMarkedJointPalm q Q))
    (hsource : (legalMarkedJointPalm q Q).map (fun m ↦ m.1.1) = α)
    (htarget : (legalMarkedJointPalm q Q).map (fun m ↦ m.1.2) = β)
    (hdom : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst ≤ legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd ≤ legalInputColorMeasure q s.2 1) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1 := by
  let _ := hprob
  let P := legalMarkedInputPairLaw q Q
  have hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂(P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube, ← cubePalm_apply (Fin q) _ MeasurableSet.univ]
    change legalMarkedJointPalm q Q univ < ∞
    rw [measure_univ]
    exact ENNReal.one_lt_top
  have hmeans := physicalScene_intensities_eq_volume_prod_cubePalm_clock_marginals
    (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
    (measurePreserving_legalMarkedInputPairLaw q Q hstat) hunit
  change physicalSceneSourceIntensity (P : Measure
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod ((legalMarkedJointPalm q Q).map (fun m ↦ m.1.1)) ∧
    physicalSceneTargetIntensity (P : Measure
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod ((legalMarkedJointPalm q Q).map (fun m ↦ m.1.2)) at hmeans
  rw [hsource, htarget] at hmeans
  have hin0 := (legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M₀.law hinput 0).trans
    M₀.inputColorIntensities_eq_volume_prod.1
  have hin1 := (legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M₀.law hinput 1).trans
    M₀.inputColorIntensities_eq_volume_prod.2
  let K := CompactExhaustion.choice (LegalMarkedPhysicalPoint q)
  have hsrcMean (n : ℕ) :
      (∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst (K n)
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫⁻ s, legalInputColorMeasure q s.2 0 (K n)
        ∂(Q : Measure (LegalMarkedOptimalInputScene q)) := by
    rw [lintegral_legalInputColorMeasure_eq_intensity q _ 0 (K.isCompact n).measurableSet, hin0,
      ← hmeans.1, physicalSceneSourceIntensity,
      Measure.bind_apply (K.isCompact n).measurableSet (Kernel.measurable _).aemeasurable]
    change (∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst (K n)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫⁻ scene, physicalSceneSourceKernel scene (K n)
        ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst
    rw [lintegral_map (Kernel.measurable_coe _ (K.isCompact n).measurableSet) measurable_fst]
    apply lintegral_congr
    intro s
    have hk : physicalSceneSourceKernel s.1 =
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map Prod.fst :=
      Kernel.map_apply _ measurable_fst s.1
    exact (congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ (K n)) hk).symm
  have htgtMean (n : ℕ) :
      (∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd (K n)
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫⁻ s, legalInputColorMeasure q s.2 1 (K n)
        ∂(Q : Measure (LegalMarkedOptimalInputScene q)) := by
    rw [lintegral_legalInputColorMeasure_eq_intensity q _ 1 (K.isCompact n).measurableSet, hin1,
      ← hmeans.2, physicalSceneTargetIntensity,
      Measure.bind_apply (K.isCompact n).measurableSet (Kernel.measurable _).aemeasurable]
    change (∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd (K n)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫⁻ scene, physicalSceneTargetKernel scene (K n)
        ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst
    rw [lintegral_map (Kernel.measurable_coe _ (K.isCompact n).measurableSet) measurable_fst]
    apply lintegral_congr
    intro s
    have hk : physicalSceneTargetKernel s.1 =
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map Prod.snd :=
      Kernel.map_apply _ measurable_snd s.1
    exact (congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ (K n)) hk).symm
  have hmeas (n : ℕ) (c : Fin 2) : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      legalInputColorMeasure q s.2 c (K n)) := by
    simpa only [legalMarkedInputColorKernel_apply] using
      Kernel.measurable_coe (legalMarkedInputColorKernel q c) (K.isCompact n).measurableSet
  have hfinite0 (n : ℕ) : (∫⁻ s, legalInputColorMeasure q s.2 0 (K n)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) < ∞ := by
    rw [lintegral_legalInputColorMeasure_eq_intensity q _ 0 (K.isCompact n).measurableSet, hin0]
    exact (K.isCompact n).measure_lt_top
  have hfinite1 (n : ℕ) : (∫⁻ s, legalInputColorMeasure q s.2 1 (K n)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) < ∞ := by
    rw [lintegral_legalInputColorMeasure_eq_intensity q _ 1 (K.isCompact n).measurableSet, hin1]
    exact (K.isCompact n).measure_lt_top
  exact (ae_randomMeasure_eq_of_le_of_local_mean_eq (Q : Measure (LegalMarkedOptimalInputScene q))
    (fun s ↦ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst) (fun s ↦ legalInputColorMeasure q s.2 0)
    K K.iUnion_eq (hdom.mono (fun _ hs ↦ hs.1)) (fun n ↦ (hmeas n 0).aemeasurable)
    hfinite0 hsrcMean).and
    (ae_randomMeasure_eq_of_le_of_local_mean_eq (Q : Measure (LegalMarkedOptimalInputScene q))
      (fun s ↦ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd) (fun s ↦ legalInputColorMeasure q s.2 1)
      K K.iUnion_eq (hdom.mono (fun _ hs ↦ hs.2)) (fun n ↦ (hmeas n 1).aemeasurable)
      hfinite1 htgtMean)

end OTSelector.Reconstruction
