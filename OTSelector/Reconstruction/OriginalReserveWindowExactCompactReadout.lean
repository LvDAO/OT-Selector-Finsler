import OTSelector.Reconstruction.OriginalReserveWindowCoveredReadout

/-! Literal finite arrays on the actual spatial window preserve every original compact readout. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance originalReserveWindowExactInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveWindowExactPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Restriction is a measurable operation on the unchanged measure readout. -/
theorem measurable_originalMeasureRestriction {X : Type*} [MeasurableSpace X]
    {U : Set X} (hU : MeasurableSet U) :
    Measurable (fun μ : Measure X ↦ μ.restrict U) := by
  apply Measure.measurable_of_measurable_coe
  intro V hV
  simpa only [Measure.restrict_apply hV] using Measure.measurable_coe (hV.inter hU)

/-- The actual original scene input restricted to any fixed Borel window is measurable. -/
theorem measurable_originalSceneInputRestriction (q : ℕ)
    {U : Set (LegalColoredInputPoint q)} (hU : MeasurableSet U) :
    Measurable (fun scene : LegalMarkedOptimalInputScene q ↦
      (scene.2 : Measure (LegalColoredInputPoint q)).restrict U) :=
  (measurable_originalMeasureRestriction hU).comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)

/-- Every compact marked readout of the same original input agrees with finite
Poisson arrays on the prescribed spatial window itself. A compact calibration
slice makes the containing cutoff cover the entire prescribed spatial window. -/
theorem LegalWeightedStationaryPoissonMatching.map_originalInput_compactWindow_eq_exactSpatialPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U)
    (hUK : U ⊆ (Prod.fst ∘ Prod.fst) ⁻¹' K) :
    (M.law : Measure (LegalMarkedOptimalInputScene q)).map
      (fun scene ↦ (scene.2 : Measure (LegalColoredInputPoint q)).restrict U) =
    (legalInputPoissonWindowLaw q K α β).map
      (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) := by
  let C : Set (LegalColoredInputPoint q) := (K ×ˢ ({0} : Set ℝ)) ×ˢ {0}
  have hC : IsCompact C := (hK.prod (isCompact_singleton : IsCompact ({0} : Set ℝ))).prod
    (isCompact_singleton : IsCompact ({0} : Set (Fin 2)))
  let W := U ∪ C
  have hW : IsCompact W := hU.union hC
  obtain ⟨S, hS, hcover, hlaw⟩ :=
    map_originalInputRestriction_eq_originalPoisson_with_spatial_cover M.law M.input_laplace hW
  have hKS : K ⊆ haarRootCube (Fin q) S := by
    intro x hx
    exact hcover ((x, 0), 0) (Or.inr ⟨⟨hx, rfl⟩, rfl⟩)
  have hUW : U ⊆ W := subset_union_left
  have hscene := measurable_originalSceneInputRestriction q hW.measurableSet
  have hblock : Measurable (fun b ↦ (legalInputTwoBlockMeasure q b).restrict W) :=
    (measurable_originalMeasureRestriction hW.measurableSet).comp
      (measurable_originalInputTwoBlockMeasure q)
  have hsmall := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦
    P.map (fun μ ↦ μ.restrict U)) hlaw
  rw [Measure.map_map (measurable_originalMeasureRestriction hU.measurableSet) hscene,
    Measure.map_map (measurable_originalMeasureRestriction hU.measurableSet) hblock] at hsmall
  simp only [Function.comp_def, Measure.restrict_restrict_of_subset hUW] at hsmall
  refine hsmall.trans ?_
  have hcons := map_originalPoissonWindow_spatial_restriction q hS
    hK.measurableSet hKS hKpos α β
  have h := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦
    P.map (fun μ ↦ μ.restrict U)) hcons
  rw [Measure.map_map (measurable_originalMeasureRestriction hU.measurableSet)
      (measurable_originalInputTwoBlockSpatialRestriction q hK.measurableSet),
    Measure.map_map (measurable_originalMeasureRestriction hU.measurableSet)
      (measurable_originalInputTwoBlockMeasure q)] at h
  have hp : ∀ b, ((legalInputTwoBlockMeasure q b).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K)).restrict U =
        (legalInputTwoBlockMeasure q b).restrict U :=
    fun _ ↦ Measure.restrict_restrict_of_subset hUK
  exact (Measure.map_congr (.of_forall hp)).symm.trans h

end OTSelector.Reconstruction
