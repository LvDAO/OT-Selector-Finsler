import OTSelector.Reconstruction.OriginalStageResidualDensityReflectedMass
import OTSelector.Reconstruction.OriginalActualInputBoundaryLawTransfer

/-! Genuine reflected densities of the unchanged original retained-complement ports. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual reflected source-port density in an unchanged scalar mark class. -/
def originalStageSourcePortDensity (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (C : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ :=
  originalStageReflectedClassDensity η R C
    (originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst

/-- The actual reflected target-port density in the same original scalar mark class. -/
def originalStageTargetPortDensity (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (C : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ :=
  originalStageReflectedClassDensity η R C
    (originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd

/-- Both true port populations remain supported in the same original physical cube. -/
theorem originalStagePortMeasures_ae_mem_cube (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    (R ell : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∀ᵐ p ∂(originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst,
      p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R) ∧
    (∀ᵐ p ∂(originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd,
      p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R) := by
  have hS := (measurableSet_originalPathSourcePorts S hF hw R ell).preimage
    measurable_physicalPairAnchor
  have hT := (measurableSet_originalPathTargetPorts S hF hw R ell).preimage
    measurable_physicalPairAnchor
  constructor
  · apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem hS] with e he
    exact he.1
  · apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem hT] with e he
    have hpos : e.1.1 + (e.2.1 - e.1.1) = e.2.1 := by abel
    change e.2.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R
    simpa only [physicalPairAnchor, hpos] using he.1

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Exact original input-window conservation and its actual Poisson law make both port
marginals finite; no selected-port law or completed count identity is assumed. -/
theorem ae_originalStagePortMeasures_finite
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasure (originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ∧
      IsFiniteMeasure (originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd := by
  have : IsProbabilityMeasure μ := D.support.source.probability
  have : IsProbabilityMeasure ν := D.support.target.probability
  filter_upwards [Q.ae_finite_fullSpatialInput (K := haarRootCube _ R) isCompact_Icc,
    D.ae_original_windows_eq_retained_add_ports hF hw Q hell hR]
    with scene hfinite hsplit
  let W : Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
    {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R}
  have hW : MeasurableSet W := measurableSet_Icc.preimage measurable_fst
  have hcolor (c : Fin 2) : legalInputColorMeasure _ scene.2 c W < (∞ : ℝ≥0∞) := by
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst hW,
      Measure.restrict_apply (hW.preimage measurable_fst)]
    apply lt_of_le_of_lt (measure_mono ?_) hfinite
    intro p hp
    exact ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩
  have hS := congrArg (fun m : Measure (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) ↦
    m univ) hsplit.1
  have hT := congrArg (fun m : Measure (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) ↦
    m univ) hsplit.2
  simp only [Measure.restrict_apply_univ, Measure.add_apply] at hS hT
  constructor
  · constructor
    apply lt_of_le_of_lt ?_ (hcolor 0)
    rw [hS]
    exact le_add_left le_rfl
  · constructor
    apply lt_of_le_of_lt ?_ (hcolor 1)
    rw [hT]
    exact le_add_left le_rfl

/-- Every true original port-class smoothing has exactly its original class count as mass,
for both colors on one event; the endpoint laws remain those of the same original input. -/
theorem ae_all_originalStagePortDensities_integrable_mass
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) (hRone : 1 ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ C : Set ℝ,
      (Integrable (originalStageSourcePortDensity S w R ell η C scene)
        (volume.restrict (haarRootCube _ R)) ∧
        (∫ z in haarRootCube _ R, originalStageSourcePortDensity S w R ell η C scene z) =
          (originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst.real {p | p.2 ∈ C}) ∧
      (Integrable (originalStageTargetPortDensity S w R ell η C scene)
        (volume.restrict (haarRootCube _ R)) ∧
        (∫ z in haarRootCube _ R, originalStageTargetPortDensity S w R ell η C scene z) =
          (originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd.real {p | p.2 ∈ C}) := by
  filter_upwards [D.ae_originalStagePortMeasures_finite hF hw Q hell hR] with scene hscene
  have : IsFiniteMeasure (originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst := hscene.1
  have : IsFiniteMeasure (originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd := hscene.2
  have hsupp := originalStagePortMeasures_ae_mem_cube S hF hw R ell scene
  intro C
  exact ⟨originalStageReflectedClassDensity_integrable_mass hη hηI hηone hηsupport hηeven
      hηM hRone _ hsupp.1 C,
    originalStageReflectedClassDensity_integrable_mass hη hηI hηone hηsupport hηeven
      hηM hRone _ hsupp.2 C⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
