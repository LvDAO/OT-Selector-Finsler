import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockMainCountMomentLaw
import OTSelector.Reconstruction.OriginalReserveOrientedWindowIntensity
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts

/-! Actual block counts retain their true physical intensity after complementary main dilation. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
local instance originalReserveDilatedBlockInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveDilatedBlockPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The dilated main count in this physical cube equals the original count in
its exact preimage cube, with every original mark and color unchanged. -/
theorem originalMainOrientedBlockCount_dilation {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c : ℝ} (hc : 0 < c) (R : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (color : Fin 2) (scene : LegalMarkedOptimalInputScene q) :
    originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S color
      (legalMarkedInputSceneDilation q c hc.ne' scene) =
    originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * (R / c))) S color scene := by
  have hpre : legalColoredInputDilation q c hc.ne' ⁻¹'
      ((originalCenteredPhysicalCubeRegion b (2 * R) ×ˢ S) ×ˢ {color}) =
      ((originalCenteredPhysicalCubeRegion b (2 * (R / c)) ×ˢ S) ×ˢ {color}) := by
    ext p
    have h := Set.ext_iff.mp (originalOrientedPhysicalCube_dilation_preimage b hc R) p.1.1
    change ((c • p.1.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R) ∧ p.1.2 ∈ S) ∧ p.2 ∈ {color}) ↔ _
    rw [show c • p.1.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R) ↔
      p.1.1 ∈ originalCenteredPhysicalCubeRegion b (2 * (R / c)) from h]
    rfl
  unfold originalMainPhysicalBlockCount
  change ⌊(((scene.2 : Measure (LegalColoredInputPoint q)).map (legalColoredInputDilation q c hc.ne'))
      ((originalCenteredPhysicalCubeRegion b (2 * R) ×ˢ S) ×ˢ {color})).toReal⌋₊ = _
  rw [Measure.map_apply (legalColoredInputDilation q c hc.ne').continuous.measurable
    (((measurableSet_originalOrientedTraffic_cube b R).prod hS).prod (measurableSet_singleton color)), hpre]
  rfl

/-- The actual dilated main has independent Poisson block counts, with the
literal preimage-window volume as rate. No new input process is sampled. -/
theorem LegalWeightedStationaryPoissonMatching.hasLaw_originalDilatedMainOrientedBlockCount_pair
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c : ℝ} (hc : 0 < c) (R : ℝ) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    HasLaw (fun scene ↦
      (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0 scene,
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1 scene))
      ((poissonMeasure ((volume (originalCenteredPhysicalCubeRegion b (2 * (R / c)))).toNNReal * (α S).toNNReal)).prod
        (poissonMeasure ((volume (originalCenteredPhysicalCubeRegion b (2 * (R / c)))).toNNReal * (β T).toNNReal)))
      (legalMarkedInputDilationLaw q c hc.ne' Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hpair := (measurable_originalMainPhysicalBlockCount
      (measurableSet_originalOrientedTraffic_cube b R) hS 0).prodMk
    (measurable_originalMainPhysicalBlockCount (measurableSet_originalOrientedTraffic_cube b R) hT 1)
  refine ⟨hpair.aemeasurable, ?_⟩
  change ((Q.law : Measure (LegalMarkedOptimalInputScene q)).map
    (legalMarkedInputSceneDilation q c hc.ne')).map _ = _
  rw [Measure.map_map hpair (continuous_legalMarkedInputSceneDilation q c hc.ne').measurable]
  have heq : (fun scene : LegalMarkedOptimalInputScene q ↦
      (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (legalMarkedInputSceneDilation q c hc.ne' scene),
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (legalMarkedInputSceneDilation q c hc.ne' scene))) =
      (fun scene ↦
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * (R / c))) S 0 scene,
          originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * (R / c))) T 1 scene)) := by
    funext scene
    rw [originalMainOrientedBlockCount_dilation b hc R hS,
      originalMainOrientedBlockCount_dilation b hc R hT]
  change (Q.law : Measure (LegalMarkedOptimalInputScene q)).map
    (fun scene ↦
      (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (legalMarkedInputSceneDilation q c hc.ne' scene),
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (legalMarkedInputSceneDilation q c hc.ne' scene))) = _
  rw [heq]
  exact (Q.hasLaw_originalMainPhysicalBlockCount_pair
    (isCompact_originalStagePhysicalCube b _) hS hT).map_eq

/-- Canonical intensity rho gives exactly rho times the same physical volume;
for the retained main this is rho = 1 - theta. -/
theorem LegalWeightedStationaryPoissonMatching.hasLaw_originalIntensityMainOrientedBlockCount_pair
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hq : 0 < q) {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    HasLaw (fun scene ↦
      (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0 scene,
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1 scene))
      ((poissonMeasure ((Real.toNNReal ρ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) *
        (α S).toNNReal)).prod
        (poissonMeasure ((Real.toNNReal ρ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) *
          (β T).toNNReal)))
      (legalMarkedInputDilationLaw q (legalIntensityDilation q ρ)
        (legalIntensityDilation_pos q hρ).ne' Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have h := Q.hasLaw_originalDilatedMainOrientedBlockCount_pair b
    (legalIntensityDilation_pos q hρ) R hS hT
  rwa [originalOrientedReserveIntensity_count_rate hq b hρ hR] at h

end OTSelector.Reconstruction
