import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocks
import OTSelector.Reconstruction.OriginalMarkedWindowCounts
import OTSelector.Reconstruction.OriginalStageResidualDensityWindowPorts

/-! The same actual stationary matching and every retained original core stay inside
the true half-open clock blocks, including blocks separated by zero Hall cuts. -/

open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
variable {q : ℕ} {μ ν : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
  (G : OriginalStageClockGrid) {δ D : ℝ} (hδ : 0 < δ)
  (hsep : ConditionalClockSupportBounds μ ν δ D)
  (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
  (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
  (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
include hδ hsep hs ht hmono

/-- A single full-scene event certifies all true blocks of the unchanged original
matching. The Palm clock coupling and its forwardness are constructed from Q. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_originalEdges_same_clockSlabBlock :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ b : G.ClockSlabBlock μ ν,
        ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)),
          e.1.2 ∈ G.sourceBlockCell μ ν b ↔ e.2.2 ∈ G.targetBlockCell μ ν b := by
  let η := legalMarkedJointPalm q Q.law
  let π := η.map Prod.fst
  have : IsProbabilityMeasure η := Q.palm_probability
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hπ : Vlasov.IsCoupling π μ ν := by
    constructor
    · simpa only [π, η, Measure.map_map measurable_fst measurable_fst,
        Function.comp_def] using Q.source_clock
    · simpa only [π, η, Measure.map_map measurable_snd measurable_fst,
        Function.comp_def] using Q.target_clock
  have hw : ∀ᵐ p ∂π, p.1 ≤ p.2 :=
    (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).mpr
      (Q.ae_palm_forward.mono fun _ hp ↦ hp.le)
  have hp : ∀ᵐ m ∂η, ∀ b : G.ClockSlabBlock μ ν,
      m.1.1 ∈ G.sourceBlockCell μ ν b ↔ m.1.2 ∈ G.targetBlockCell μ ν b :=
    ae_all_iff.mpr fun b ↦ ae_of_ae_map measurable_fst.aemeasurable
      (G.ae_same_blockCells hδ hsep π hπ hs ht hmono hw b)
  have hB : MeasurableSet {m : PhysicalPairPalmMark (Fin q) |
      ∀ b : G.ClockSlabBlock μ ν,
        m.1.1 ∈ G.sourceBlockCell μ ν b ↔ m.1.2 ∈ G.targetBlockCell μ ν b} :=
    by
      simpa only [ofPred_forall] using MeasurableSet.iInter
        (fun b : G.ClockSlabBlock μ ν ↦
          ((G.blockCells_measurable b).1.preimage measurable_fst.fst).iff
            ((G.blockCells_measurable b).2.preimage measurable_fst.snd))
  filter_upwards [Q.ae_ae_original_pairKernel_of_palm hB hp] with scene hscene
  rw [physicalScenePairKernel_apply] at hscene
  have he := ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hscene
  intro b
  exact he.mono fun _ h ↦ h b

/-- Every actual original path restriction inherits the same-block relation and
has literally equal restrictions by its source and target block. This universal
statement includes the actual oriented path-length retained set. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalStageRestrictedPathPlan_same_clockSlabBlock :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
        (b : G.ClockSlabBlock μ ν),
      (∀ᵐ e ∂(originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)),
        e.1.2 ∈ G.sourceBlockCell μ ν b ↔ e.2.2 ∈ G.targetBlockCell μ ν b) ∧
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)).restrict
          {e | e.1.2 ∈ G.sourceBlockCell μ ν b} =
        (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)).restrict
          {e | e.2.2 ∈ G.targetBlockCell μ ν b} := by
  filter_upwards [Q.ae_ae_originalEdges_same_clockSlabBlock G hδ hsep hs ht hmono]
    with scene hscene
  intro A b
  have he : ∀ᵐ e ∂(originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)),
      e.1.2 ∈ G.sourceBlockCell μ ν b ↔ e.2.2 ∈ G.targetBlockCell μ ν b :=
    ae_restrict_of_ae (hscene b)
  exact ⟨he, Measure.restrict_congr_set (he.mono fun _ h ↦ propext h)⟩

/-- A genuine finite counting representation forces every retained original-index
edge into the same actual block. Repeated points and empty arrays are allowed. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalIndex_edges_same_clockSlabBlock :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (m n : ℕ)
        (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
        (σ : OTSelector.PartialMatching m n),
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)) =
          ∑ ij ∈ σ.edges, Measure.dirac (x ij.1, y ij.2) →
      ∀ b : G.ClockSlabBlock μ ν, ∀ ij ∈ σ.edges,
        (x ij.1).2 ∈ G.sourceBlockCell μ ν b ↔ (y ij.2).2 ∈ G.targetBlockCell μ ν b := by
  filter_upwards [Q.ae_originalStageRestrictedPathPlan_same_clockSlabBlock G hδ hsep hs ht hmono]
    with scene hscene
  intro A m n x y σ hσ b ij hij
  have he := (hscene A b).1
  rw [hσ] at he
  have hdir := ae_finsetSum_measure_iff.mp he ij hij
  simpa only [ae_dirac_eq, eventually_pure] using hdir

end OTSelector.Reconstruction
