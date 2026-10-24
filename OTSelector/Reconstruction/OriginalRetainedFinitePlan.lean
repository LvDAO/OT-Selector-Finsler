import OTSelector.Reconstruction.OriginalTargetPortCountExpectation
import OTSelector.MeasureTheory.ParameterizedRestriction
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCellExchangeGluing

/-! # The Borel retained core is an actual finite original integer matching -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The literal unchanged first original plan restricted by the measurable
source-inner-cube and true complete-path-length test. -/
def originalPathRetainedPlan (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  ⟨(scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict
    (physicalPairAnchor ⁻¹' originalPathLengthRetained S w R ell), inferInstance⟩

/-- The actual retained plan is a Borel function of the same original scene. -/
theorem measurable_originalPathRetainedPlan
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (R ell : ℝ) :
    Measurable (originalPathRetainedPlan S w R ell) := by
  let U : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
    {p | physicalPairAnchor p.2 ∈ originalPathLengthRetained S w R ell}
  have hU : MeasurableSet U :=
    (measurableSet_originalPathLengthRetained S hF hw R ell).preimage
      (measurable_physicalPairAnchor.comp measurable_snd)
  exact measurable_originalParameterizedRestriction (fun scene ↦ scene.1.1)
    measurable_fst.fst U hU

/-- A retained edge is still one and the same occupied unit original atom. -/
theorem IsFullOriginalInputMatching.simple_originalPathRetainedPlan
    {scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)}
    (hscene : IsFullOriginalInputMatching (finrank ℝ S.covector.ker) scene) (R ell : ℝ) :
    IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
      (originalPathRetainedPlan S w R ell scene) :=
  isLegalSimpleCountingMeasure_restrict _ scene.1.1 hscene.simple_edges _

/-- The retained plan consumes at most the exact source and target capacities
of the same original colored input, even after inspecting the full matching. -/
theorem IsFullOriginalInputMatching.originalPathRetainedPlan_capacities
    {scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)}
    (hscene : IsFullOriginalInputMatching (finrank ℝ S.covector.ker) scene) (R ell : ℝ) :
    (originalPathRetainedPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ≤
        legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 0 ∧
    (originalPathRetainedPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd ≤
        legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 1 := by
  constructor
  · rw [← hscene.source_marginal]
    exact Measure.map_mono Measure.restrict_le_self measurable_fst
  · rw [← hscene.target_marginal]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd

/-- Both endpoint projections remain injective on the actual retained support. -/
theorem IsFullOriginalInputMatching.originalPathRetainedPlan_injective
    {scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)}
    (hscene : IsFullOriginalInputMatching (finrank ℝ S.covector.ker) scene) (R ell : ℝ) :
    Set.InjOn Prod.fst (originalPathRetainedPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support ∧
    Set.InjOn Prod.snd (originalPathRetainedPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support :=
  ⟨hscene.source_injective.mono (Measure.support_mono Measure.restrict_le_self),
    hscene.target_injective.mono (Measure.support_mono Measure.restrict_le_self)⟩

/-- Total retained mass is precisely the literal original anchor-kernel count. -/
theorem originalPathRetainedPlan_mass_eq_pairKernel
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (R ell : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (originalPathRetainedPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ =
      physicalScenePairKernel scene.1 (originalPathLengthRetained S w R ell) := by
  rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
    (measurableSet_originalPathLengthRetained S hF hw R ell)]
  exact Measure.restrict_apply_univ _

/-- Actual Campbell intensity makes every retained core finite almost surely,
without a new moment or a finite-window enumeration assumption. -/
theorem ae_originalPathRetainedPlan_finite
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) (R ell : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ < (⊤ : ℝ≥0∞) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := Q.palm_probability
  have hA := measurableSet_originalPathLengthRetained S hF hw R ell
  have hmean : (∫⁻ scene, physicalScenePairKernel scene.1 (originalPathLengthRetained S w R ell)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) < (⊤ : ℝ≥0∞) := by
    rw [Q.lintegral_original_pairKernel_apply hA]
    apply lt_of_le_of_lt (measure_mono (show originalPathLengthRetained S w R ell ⊆
      haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell) ×ˢ univ from
        fun a ha ↦ ⟨ha.1, mem_univ _⟩))
    rw [Measure.prod_prod, measure_univ, mul_one]
    exact isCompact_Icc.measure_lt_top
  have hfinite := ae_lt_top ((Kernel.measurable_coe physicalScenePairKernel hA).comp measurable_fst) hmean.ne
  filter_upwards [hfinite] with scene hscene
  rwa [originalPathRetainedPlan_mass_eq_pairKernel hF hw]

end OTSelector.Reconstruction
