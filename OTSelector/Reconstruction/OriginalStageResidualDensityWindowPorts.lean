import OTSelector.Reconstruction.OriginalWindowPortConservation

/-! One shared actual restriction/port decomposition for every Borel physical window and path set. -/
open Set Function Filter MeasureTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The unchanged original edge plan restricted by one literal original path-anchor set. -/
def originalStageRestrictedPathPlan {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (scene : LegalMarkedOptimalInputScene q) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (physicalPairAnchor ⁻¹' A), inferInstance⟩

/-- Actual original source-window edges not in that same selected path set. -/
def originalStageWindowSourcePortPlan {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (K : Set (Fin q → ℝ))
    (scene : LegalMarkedOptimalInputScene q) : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    ({e | e.1.1 ∈ K} \ (physicalPairAnchor ⁻¹' A)), inferInstance⟩

/-- Actual original target-window edges not in exactly the same selected set. -/
def originalStageWindowTargetPortPlan {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (K : Set (Fin q → ℝ))
    (scene : LegalMarkedOptimalInputScene q) : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    ({e | e.2.1 ∈ K} \ (physicalPairAnchor ⁻¹' A)), inferInstance⟩

/-- A Borel retained original path set whose actual endpoints stay in the chosen Borel
physical window yields the exact two original window marginals = retained + actual ports.
This shared lemma applies to arbitrary orientations without altering the original scene. -/
theorem IsFullOriginalInputMatching.originalStage_window_eq_restricted_add_ports {q : ℕ}
    {scene : LegalMarkedOptimalInputScene q} (hfull : IsFullOriginalInputMatching q scene)
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (hsource : ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      physicalPairAnchor e ∈ A → e.1.1 ∈ K)
    (htarget : ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      physicalPairAnchor e ∈ A → e.2.1 ∈ K) :
    (legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ K} =
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)).fst +
      (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).fst ∧
    (legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ K} =
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)).snd +
      (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).snd := by
  let π : Measure (LegalMarkedPhysicalEdge q) := scene.1.1
  let B := physicalPairAnchor ⁻¹' A
  let W : Set (LegalMarkedPhysicalPoint q) := {p | p.1 ∈ K}
  have hB : MeasurableSet B := hA.preimage measurable_physicalPairAnchor
  have hW : MeasurableSet W := hK.preimage measurable_fst
  have hs := measure_restrict_eq_retained_add_unused_of_ae_subset π hB hsource
  have ht := measure_restrict_eq_retained_add_unused_of_ae_subset π hB htarget
  have hsm := congrArg (fun ρ : Measure (LegalMarkedPhysicalEdge q) ↦ ρ.fst) hs
  have htm := congrArg (fun ρ : Measure (LegalMarkedPhysicalEdge q) ↦ ρ.snd) ht
  rw [Measure.fst_add] at hsm
  rw [Measure.snd_add] at htm
  constructor
  · rw [← hfull.source_marginal]
    change (π.map Prod.fst).restrict W = _
    rw [Measure.restrict_map measurable_fst hW]
    exact hsm
  · rw [← hfull.target_marginal]
    change (π.map Prod.snd).restrict W = _
    rw [Measure.restrict_map measurable_snd hW]
    exact htm

/-- All restrictions keep the actual original unit occupied atoms. -/
theorem IsFullOriginalInputMatching.originalStage_restrictions_simple {q : ℕ}
    {scene : LegalMarkedOptimalInputScene q} (hfull : IsFullOriginalInputMatching q scene)
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (K : Set (Fin q → ℝ)) :
    IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge q) (originalStageRestrictedPathPlan A scene) ∧
    IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge q) (originalStageWindowSourcePortPlan A K scene) ∧
    IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge q) (originalStageWindowTargetPortPlan A K scene) := by
  exact ⟨isLegalSimpleCountingMeasure_restrict _ _ hfull.simple_edges _,
    isLegalSimpleCountingMeasure_restrict _ _ hfull.simple_edges _,
    isLegalSimpleCountingMeasure_restrict _ _ hfull.simple_edges _⟩

end OTSelector.Reconstruction
