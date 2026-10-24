import OTSelector.Reconstruction.OriginalRetainedFinitePlan

/-! # Literal source and target port plans on the same original input -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Original unchanged edges contributing a source port in the physical cube. -/
def originalPathSourcePortPlan (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  ⟨(scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict
    (physicalPairAnchor ⁻¹' originalPathSourcePorts S w R ell), inferInstance⟩

/-- Original unchanged edges contributing a target port in the physical cube. -/
def originalPathTargetPortPlan (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  ⟨(scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict
    (physicalPairAnchor ⁻¹' originalPathTargetPorts S w R ell), inferInstance⟩

theorem measurable_originalPathSourcePortPlan
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (R ell : ℝ) :
    Measurable (originalPathSourcePortPlan S w R ell) :=
  measurable_originalParameterizedRestriction (fun scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦ scene.1.1)
    measurable_fst.fst _ ((measurableSet_originalPathSourcePorts S hF hw R ell).preimage
      (measurable_physicalPairAnchor.comp measurable_snd))

theorem measurable_originalPathTargetPortPlan
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (R ell : ℝ) :
    Measurable (originalPathTargetPortPlan S w R ell) :=
  measurable_originalParameterizedRestriction (fun scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦ scene.1.1)
    measurable_fst.fst _ ((measurableSet_originalPathTargetPorts S hF hw R ell).preimage
      (measurable_physicalPairAnchor.comp measurable_snd))

/-- The actual source and target port pieces retain the simple integer carrier;
neither a fresh point process nor a new point selection is introduced. -/
theorem IsFullOriginalInputMatching.simple_originalPathPortPlans
    {scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)}
    (hscene : IsFullOriginalInputMatching (finrank ℝ S.covector.ker) scene) (R ell : ℝ) :
    IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
      (originalPathSourcePortPlan S w R ell scene) ∧
    IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
      (originalPathTargetPortPlan S w R ell scene) :=
  ⟨isLegalSimpleCountingMeasure_restrict _ scene.1.1 hscene.simple_edges _,
    isLegalSimpleCountingMeasure_restrict _ scene.1.1 hscene.simple_edges _⟩

/-- The literal source port plan has exactly the original anchor-kernel port mass. -/
theorem originalPathSourcePortPlan_mass_eq_pairKernel
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (R ell : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (originalPathSourcePortPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ =
      physicalScenePairKernel scene.1 (originalPathSourcePorts S w R ell) := by
  rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
    (measurableSet_originalPathSourcePorts S hF hw R ell)]
  exact Measure.restrict_apply_univ _

/-- The literal target port plan has exactly the original anchor-kernel port mass. -/
theorem originalPathTargetPortPlan_mass_eq_pairKernel
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (R ell : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (originalPathTargetPortPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ =
      physicalScenePairKernel scene.1 (originalPathTargetPorts S w R ell) := by
  rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
    (measurableSet_originalPathTargetPorts S hF hw R ell)]
  exact Measure.restrict_apply_univ _

end OTSelector.Reconstruction
