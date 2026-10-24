import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts
import OTSelector.Reconstruction.OriginalActualInputBoundaryLawTransfer
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowColors

/-! Actual original oriented retained plans and both port plans are finite. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Any genuine original two-color compact spatial window has finite full original counts,
with all clock marks retained and no probability law imposed on selected ports. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalStageWindowColors_finite
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ c : Fin 2, legalInputColorMeasure q scene.2 c {p | p.1 ∈ K} < (∞ : ℝ≥0∞) := by
  filter_upwards [Q.ae_finite_fullSpatialInput hK] with scene hfinite
  intro c
  have hW : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ K} := hK.measurableSet.preimage measurable_fst
  rw [legalInputColorMeasure_apply_prod q _ c hW]
  have hsub : ({p : LegalMarkedPhysicalPoint q | p.1 ∈ K} ×ˢ ({c} : Set (Fin 2))) ⊆
      ((K ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set (Fin 2))) := by
    intro p hp
    exact ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩
  exact lt_of_le_of_lt (measure_mono hsub) hfinite

/-- Exact actual retained/port decompositions and finite original input counts imply that
all three actual edge restrictions are finite. No selected cloud law is needed. -/
theorem originalStageWindowPlans_finite_of_decomposition {q : ℕ}
    (scene : LegalMarkedOptimalInputScene q)
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (K : Set (Fin q → ℝ))
    (hs : (legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ K} =
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)).fst +
      (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).fst)
    (ht : (legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ K} =
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)).snd +
      (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).snd)
    (hsource : legalInputColorMeasure q scene.2 0 {p | p.1 ∈ K} < (∞ : ℝ≥0∞))
    (htarget : legalInputColorMeasure q scene.2 1 {p | p.1 ∈ K} < (∞ : ℝ≥0∞)) :
    IsFiniteMeasure (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)) ∧
    IsFiniteMeasure (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)) ∧
    IsFiniteMeasure (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)) := by
  have hfst (π : Measure (LegalMarkedPhysicalEdge q)) : π.fst univ = π univ := by
    change (π.map Prod.fst) univ = π univ
    rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    rfl
  have hsnd (π : Measure (LegalMarkedPhysicalEdge q)) : π.snd univ = π univ := by
    change (π.map Prod.snd) univ = π univ
    rw [Measure.map_apply measurable_snd MeasurableSet.univ]
    rfl
  have hs' := congrArg (fun π : Measure (LegalMarkedPhysicalPoint q) ↦ π univ) hs
  have ht' := congrArg (fun π : Measure (LegalMarkedPhysicalPoint q) ↦ π univ) ht
  simp only [Measure.restrict_apply_univ, Measure.add_apply, hfst, hsnd] at hs' ht'
  refine ⟨⟨lt_of_le_of_lt ?_ hsource⟩, ⟨lt_of_le_of_lt ?_ hsource⟩, ⟨lt_of_le_of_lt ?_ htarget⟩⟩
  · rw [hs']
    exact le_add_right le_rfl
  · rw [hs']
    exact le_add_left le_rfl
  · rw [ht']
    exact le_add_left le_rfl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The same original matching and chosen physical cube internally produce finite actual
retained and port plans, using their genuine complete-path endpoint inclusion. -/
theorem ae_originalOrientedStagePlans_finite
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      let A := originalOrientedPathLengthRetained S w b R ell
      let K := originalCenteredPhysicalCubeRegion b (2 * R)
      IsFiniteMeasure (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) ∧
      IsFiniteMeasure (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) ∧
      IsFiniteMeasure (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  filter_upwards [D.ae_originalOriented_windows_eq_retained_add_ports hF hw Q b hell hR,
    Q.ae_originalStageWindowColors_finite (isCompact_originalStagePhysicalCube b (2 * R))]
    with scene hdec hfinite
  exact originalStageWindowPlans_finite_of_decomposition scene _ _ hdec.1 hdec.2 (hfinite 0) (hfinite 1)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
