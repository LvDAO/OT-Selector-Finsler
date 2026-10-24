import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCutScene
import OTSelector.MeasureTheory.LocalFiniteMeasureMarginalTightness

/-! # Actual input intensities of every genuine prescribed stationary matching -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
local instance stationaryOriginalInputIntensityInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance stationaryOriginalInputIntensityPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual first matching's source intensity equals its complete original
source input intensity, with no finite-optimum provenance assumption. -/
theorem LegalWeightedStationaryPoissonMatching.sourceIntensity_eq_inputColorIntensity
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    physicalSceneSourceIntensity (legalMarkedInputPairLaw q M.law :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      legalMarkedInputColorIntensity q (M.law : Measure (LegalMarkedOptimalInputScene q)) 0 := by
  ext B hB
  rw [physicalSceneSourceIntensity, legalMarkedInputColorIntensity,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
  change (∫⁻ scene, physicalSceneSourceKernel scene B
    ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst) = _
  rw [lintegral_map (Kernel.measurable_coe _ hB) measurable_fst]
  apply lintegral_congr_ae
  filter_upwards [M.full_matching] with s hs
  rw [legalMarkedInputColorKernel_apply]
  have hk : physicalSceneSourceKernel s.1 =
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map Prod.fst :=
    Kernel.map_apply _ measurable_fst s.1
  rw [hk]
  exact congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ B) hs.source_marginal

/-- The actual target intensity equality likewise retains every original
input atom and every matching/input correlation. -/
theorem LegalWeightedStationaryPoissonMatching.targetIntensity_eq_inputColorIntensity
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    physicalSceneTargetIntensity (legalMarkedInputPairLaw q M.law :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      legalMarkedInputColorIntensity q (M.law : Measure (LegalMarkedOptimalInputScene q)) 1 := by
  ext B hB
  rw [physicalSceneTargetIntensity, legalMarkedInputColorIntensity,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
  change (∫⁻ scene, physicalSceneTargetKernel scene B
    ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst) = _
  rw [lintegral_map (Kernel.measurable_coe _ hB) measurable_fst]
  apply lintegral_congr_ae
  filter_upwards [M.full_matching] with s hs
  rw [legalMarkedInputColorKernel_apply]
  have hk : physicalSceneTargetKernel s.1 =
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map Prod.snd :=
    Kernel.map_apply _ measurable_snd s.1
  rw [hk]
  exact congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ B) hs.target_marginal

/-- Every genuine stationary matching has exact original physical input
intensities. Its own probability Palm and original clock marginals produce
the normalization; no kinetic or displacement moment bound is needed. -/
theorem LegalWeightedStationaryPoissonMatching.inputColorIntensities_eq_volume_prod
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    legalMarkedInputColorIntensity q (M.law : Measure (LegalMarkedOptimalInputScene q)) 0 =
        (volume : Measure (Fin q → ℝ)).prod α ∧
      legalMarkedInputColorIntensity q (M.law : Measure (LegalMarkedOptimalInputScene q)) 1 =
        (volume : Measure (Fin q → ℝ)).prod β := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let P := legalMarkedInputPairLaw q M.law
  have hu : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂(P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube, ← cubePalm_apply (Fin q) _ MeasurableSet.univ]
    change legalMarkedJointPalm q M.law univ < ∞
    rw [measure_univ]
    norm_num
  have hf := physicalScene_intensities_eq_volume_prod_cubePalm_clock_marginals
    (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) (measurePreserving_legalMarkedInputPairLaw q M.law M.stationary) hu
  change physicalSceneSourceIntensity (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod ((legalMarkedJointPalm q M.law).map (fun m ↦ m.1.1)) ∧
    physicalSceneTargetIntensity (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod ((legalMarkedJointPalm q M.law).map (fun m ↦ m.1.2)) at hf
  rw [M.source_clock, M.target_clock] at hf
  exact ⟨M.sourceIntensity_eq_inputColorIntensity.symm.trans hf.1,
    M.targetIntensity_eq_inputColorIntensity.symm.trans hf.2⟩

/-- The expected mass of either unchanged actual color is read directly
from its original physical intensity measure on every measurable window. -/
theorem lintegral_legalInputColorMeasure_eq_intensity (q : ℕ)
    (P : Measure (LegalMarkedOptimalInputScene q)) (c : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    (∫⁻ s, legalInputColorMeasure q s.2 c B ∂P) =
      legalMarkedInputColorIntensity q P c B := by
  rw [legalMarkedInputColorIntensity,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro s
  rw [legalMarkedInputColorKernel_apply]

/-- The complete actual colored input mass is controlled by the sum of its
two literal color restrictions, before any matching selection. -/
theorem legalInput_mass_le_sum_colorMass (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q))
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    (μ : Measure (LegalColoredInputPoint q)) (B ×ˢ univ) ≤
      legalInputColorMeasure q μ 0 B + legalInputColorMeasure q μ 1 B := by
  have he (c : Fin 2) : legalInputColorMeasure q μ c B =
      (μ : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) := by
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst hB,
      Measure.restrict_apply (hB.preimage measurable_fst)]
    congr 1
  rw [he 0, he 1]
  refine (measure_mono ?_).trans (measure_union_le _ _)
  rintro ⟨x, c⟩ hx
  fin_cases c
  · exact Or.inl ⟨hx.1, rfl⟩
  · exact Or.inr ⟨hx.1, rfl⟩

end OTSelector.Reconstruction
