import OTSelector.Reconstruction.OriginalPortFinitePlans
import OTSelector.Reconstruction.OriginalRetainedLegalCore
import OTSelector.MeasureTheory.RetainedRestrictionDecomposition

/-! # Exact original two-color window input equals retained endpoints plus ports -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The literal source-window original input splits into its retained sources
and exactly the original source ports, without replacement or added atoms. -/
theorem IsFullOriginalInputMatching.original_sourceWindow_eq_retained_add_ports
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)}
    (hscene : IsFullOriginalInputMatching (finrank ℝ S.covector.ker) scene)
    {R ell : ℝ} (hell : 0 ≤ ell) :
    (legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 0).restrict
      {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R} =
    (originalPathRetainedPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst +
    (originalPathSourcePortPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst := by
  let π : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := scene.1.1
  let A := physicalPairAnchor ⁻¹' originalPathLengthRetained S w R ell
  let W : Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
    {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R}
  have hA : MeasurableSet A :=
    (measurableSet_originalPathLengthRetained S hF hw R ell).preimage measurable_physicalPairAnchor
  have hW : MeasurableSet W := measurableSet_Icc.preimage measurable_fst
  have hsub : ∀ᵐ e ∂π, e ∈ A → e ∈ Prod.fst ⁻¹' W := by
    apply Eventually.of_forall
    intro e he
    have hx : e.1.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell) := he.1
    constructor <;> intro i <;> have h₀ := hx.1 i <;> have h₁ := hx.2 i <;>
      dsimp at * <;> linarith
  have hdec := measure_restrict_eq_retained_add_unused_of_ae_subset π hA hsub
  have hports : physicalPairAnchor ⁻¹' originalPathSourcePorts S w R ell =
      (Prod.fst ⁻¹' W) \ A := by
    ext e
    rfl
  rw [← hscene.source_marginal]
  change (π.map Prod.fst).restrict W = _
  rw [Measure.restrict_map measurable_fst hW]
  have hmapped := congrArg (fun m : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) ↦ m.fst) hdec
  rw [Measure.fst_add] at hmapped
  change (π.restrict (Prod.fst ⁻¹' W)).fst = (π.restrict A).fst +
    (π.restrict (physicalPairAnchor ⁻¹' originalPathSourcePorts S w R ell)).fst
  rw [hports]
  exact hmapped

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Both complete original colored window inputs are exactly the retained
endpoint marginals plus the literal source and target port marginals. -/
theorem ae_original_windows_eq_retained_add_ports
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 0).restrict
        {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R} =
      (originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst +
      (originalPathSourcePortPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ∧
      (legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 1).restrict
        {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R} =
      (originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd +
      (originalPathTargetPortPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd := by
  have hA := (measurableSet_originalPathLengthRetained S hF hw R ell).preimage measurable_physicalPairAnchor
  filter_upwards [Q.full_matching, D.ae_ae_original_pairKernel_interior_forward Q]
    with scene hfull hclock
  refine ⟨hfull.original_sourceWindow_eq_retained_add_ports hF hw hell, ?_⟩
  let π : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := scene.1.1
  let A := physicalPairAnchor ⁻¹' originalPathLengthRetained S w R ell
  let W : Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
    {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R}
  have hW : MeasurableSet W := measurableSet_Icc.preimage measurable_fst
  have hclockEdge : ∀ᵐ e ∂π,
      e.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
      e.2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ e.1.2 < e.2.2 := by
    rw [physicalScenePairKernel_apply] at hclock
    exact ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hclock
  have hsub : ∀ᵐ e ∂π, e ∈ A → e ∈ Prod.snd ⁻¹' W := by
    filter_upwards [hclockEdge] with e he hret
    have ht := D.originalPathLengthRetained_target_mem_innerCube hF hw hell hR hret he.1 he.2.1 he.2.2
    have heq : e.1.1 + (e.2.1 - e.1.1) = e.2.1 := by abel
    have htarget : e.2.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) := by
      simpa only [physicalPairAnchor, heq] using ht
    constructor <;> intro i <;> have h₀ := htarget.1 i <;> have h₁ := htarget.2 i <;>
      dsimp at * <;> linarith
  have hdec := measure_restrict_eq_retained_add_unused_of_ae_subset π hA hsub
  have hports : physicalPairAnchor ⁻¹' originalPathTargetPorts S w R ell =
      (Prod.snd ⁻¹' W) \ A := by
    ext e
    have heq : e.1.1 + (e.2.1 - e.1.1) = e.2.1 := by abel
    change (e.1.1 + (e.2.1 - e.1.1) ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R ∧
      physicalPairAnchor e ∉ originalPathLengthRetained S w R ell) ↔
      (e.2.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R ∧
      physicalPairAnchor e ∉ originalPathLengthRetained S w R ell)
    rw [heq]
  rw [← hfull.target_marginal]
  change (π.map Prod.snd).restrict W = _
  rw [Measure.restrict_map measurable_snd hW]
  have hmapped := congrArg (fun m : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) ↦ m.snd) hdec
  rw [Measure.snd_add] at hmapped
  change (π.restrict (Prod.snd ⁻¹' W)).snd = (π.restrict A).snd +
    (π.restrict (physicalPairAnchor ⁻¹' originalPathTargetPorts S w R ell)).snd
  rw [hports]
  exact hmapped

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
