import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsCounts
import OTSelector.Reconstruction.OriginalStageResidualDensityWindowPorts
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocks

/-! True null clock-law blocks contain no original matching edges or actual port marginals. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {μ ν : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- Actual Palm clock null sets are avoided by the unchanged original full edge plan. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalEdges_avoid_null_clock_sets
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hμ : μ S = 0) (hν : ν T = 0) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 ∉ S ∧ e.2.2 ∉ T := by
  have hs : ∀ᵐ s ∂μ, s ∉ S := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using hμ
  have ht : ∀ᵐ t ∂ν, t ∉ T := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using hν
  have hps : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.1 ∉ S :=
    ae_of_ae_map measurable_fst.fst.aemeasurable (by rw [Q.source_clock]; exact hs)
  have hpt : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.2 ∉ T :=
    ae_of_ae_map measurable_fst.snd.aemeasurable (by rw [Q.target_clock]; exact ht)
  have hB : MeasurableSet {m : PhysicalPairPalmMark (Fin q) | m.1.1 ∉ S ∧ m.1.2 ∉ T} :=
    (hS.preimage measurable_fst.fst).compl.inter (hT.preimage measurable_fst.snd).compl
  filter_upwards [Q.ae_ae_original_pairKernel_of_palm hB (hps.and hpt)] with scene hp
  rw [physicalScenePairKernel_apply] at hp
  exact ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hp

/-- The actual path restriction and spatial window can be arbitrary: a true null
clock class has zero source/target port mass on that same original scene. -/
theorem originalStage_port_clock_class_zero_of_edges_avoid
    (scene : LegalMarkedOptimalInputScene q) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (havoid : ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 ∉ S ∧ e.2.2 ∉ T)
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (K : Set (Fin q → ℝ)) :
    (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).fst {p | p.2 ∈ S} = 0 ∧
    (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).snd {p | p.2 ∈ T} = 0 := by
  have hs : ∀ᵐ p ∂(originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).fst,
      p.2 ∉ S :=
    (ae_map_iff measurable_fst.aemeasurable (hS.preimage measurable_snd).compl).mpr
      (ae_restrict_of_ae (havoid.mono fun _ hp ↦ hp.1))
  have ht : ∀ᵐ p ∂(originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).snd,
      p.2 ∉ T :=
    (ae_map_iff measurable_snd.aemeasurable (hT.preimage measurable_snd).compl).mpr
      (ae_restrict_of_ae (havoid.mono fun _ hp ↦ hp.2))
  exact ⟨by simpa only [not_not] using ae_iff.mp hs,by simpa only [not_not] using ae_iff.mp ht⟩

/-- One original-scene event excludes every true zero-law block from all actual ports. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_zeroClockBlocks_port_class_zero
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) (G : OriginalStageClockGrid) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ block : G.ClockSlabBlock μ ν, block ∉ G.positiveSlabBlocks μ ν →
      ∀ A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)), ∀ K : Set (Fin q → ℝ),
        (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).fst
          {p | p.2 ∈ G.sourceBlockCell μ ν block} = 0 ∧
        (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).snd
          {p | p.2 ∈ G.targetBlockCell μ ν block} = 0 := by
  have hh (block : G.ClockSlabBlock μ ν) :
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      block ∉ G.positiveSlabBlocks μ ν →
      ∀ A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)), ∀ K : Set (Fin q → ℝ),
        (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).fst
          {p | p.2 ∈ G.sourceBlockCell μ ν block} = 0 ∧
        (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).snd
          {p | p.2 ∈ G.targetBlockCell μ ν block} = 0 := by
    by_cases hb : block ∈ G.positiveSlabBlocks μ ν
    · exact ae_of_all _ (fun _ hn ↦ (hn hb).elim)
    have hz := G.zeroSlabBlock_restrict block hb
    filter_upwards [Q.ae_originalEdges_avoid_null_clock_sets
      (G.blockCells_measurable block).1 (G.blockCells_measurable block).2
      (Measure.restrict_eq_zero.mp hz.1) (Measure.restrict_eq_zero.mp hz.2)] with scene hs
    intro _ A K
    exact originalStage_port_clock_class_zero_of_edges_avoid scene
      (G.blockCells_measurable block).1 (G.blockCells_measurable block).2 hs A K
  exact ae_all_iff.mpr hh

end OTSelector.Reconstruction
