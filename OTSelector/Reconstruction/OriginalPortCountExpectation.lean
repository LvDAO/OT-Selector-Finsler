import OTSelector.Reconstruction.OriginalPathPorts
import OTSelector.Reconstruction.OriginalMarkedWindowCounts

/-! # Original source ports have their own Campbell collar and long-path bound -/
open Set Function Matrix Module Manifold MeasureTheory ProbabilityTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Every source port is paid by the unchanged original source collar or its own
true-Palm long-path tail. The selected source-port cloud gets no distribution assumption. -/
theorem lintegral_original_sourcePorts_le_boundary_and_pathTail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (R ell : ℝ) :
    (∫⁻ s, physicalScenePairKernel s.1 (originalPathSourcePorts S w R ell)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R \
        haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell)) +
      volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) *
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
          {m | ell < originalSeedPairPathLength S w m} := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.palm_probability
  let W := haarRootCube (Fin (finrank ℝ S.covector.ker)) R
  let W₀ := haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell)
  let B := {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) |
    ell < originalSeedPairPathLength S w m}
  let A₀ : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
    PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) := {a | a.1 ∈ W \ W₀}
  let A₁ : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
    PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) := {a | a.1 ∈ W ∧ a.2 ∈ B}
  have hW : MeasurableSet W := measurableSet_Icc
  have hW₀ : MeasurableSet W₀ := measurableSet_Icc
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (measurable_originalSeedPairPathLength S hF hw)
  have hA₀ : MeasurableSet A₀ := (hW.diff hW₀).preimage measurable_fst
  have hmean₀ : (∫⁻ s, physicalScenePairKernel s.1 A₀
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume (W \ W₀) := by
    simpa only [add_zero, mem_univ, and_true, measure_univ, mul_one, A₀] using
      Q.lintegral_original_markedWindow_count (fun _ ↦ 0) measurable_const
        (hW.diff hW₀) MeasurableSet.univ
  have hmean₁ : (∫⁻ s, physicalScenePairKernel s.1 A₁
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume W * (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) B := by
    simpa only [add_zero, A₁] using
      Q.lintegral_original_markedWindow_count (fun _ ↦ 0) measurable_const hW hB
  calc
    _ ≤ ∫⁻ s, (physicalScenePairKernel s.1 A₀ + physicalScenePairKernel s.1 A₁)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
      apply lintegral_mono
      intro s
      exact (measure_mono (originalPathSourcePorts_subset_boundary_or_long S w R ell)).trans
        (measure_union_le _ _)
    _ = (∫⁻ s, physicalScenePairKernel s.1 A₀
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) +
        ∫⁻ s, physicalScenePairKernel s.1 A₁
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
      lintegral_add_left ((Kernel.measurable_coe physicalScenePairKernel hA₀).comp measurable_fst) _
    _ = _ := by rw [hmean₀, hmean₁]

end OTSelector.Reconstruction
