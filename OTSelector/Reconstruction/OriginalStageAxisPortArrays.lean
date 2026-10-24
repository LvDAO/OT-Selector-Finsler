import OTSelector.Reconstruction.OriginalStagePortAtomArrays
import OTSelector.Reconstruction.OriginalStageAxisPortProbability

/-! Actual axis-aligned original port arrays for the literal stage arrival laws. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual original simple integer ports produce the exact endpoint arrays used in the
axis stage law. Their points and class counts belong to the original input, with no iid law
assigned to selected ports and no completed count representation supplied as a premise. -/
theorem ae_exists_originalAxisStagePortArrays
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (∃ n : ℕ, ∃ points : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker),
        (originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst =
          ∑ i, Measure.dirac (points i) ∧ ∀ i, (points i).1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R) ∧
      (∃ n : ℕ, ∃ points : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker),
        (originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd =
          ∑ i, Measure.dirac (points i) ∧ ∀ i, (points i).1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R) := by
  filter_upwards [Q.full_matching, D.ae_originalStagePortMeasures_finite hF hw Q hell hR]
    with scene hfull hfinite
  have hsimple := hfull.simple_originalPathPortPlans (S := S) (w := w) R ell
  have hsupp := originalStagePortMeasures_ae_mem_cube S hF hw R ell scene
  have hmassS : (originalPathSourcePortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ < (∞ : ℝ≥0∞) := by
    have hm := hfinite.1.measure_univ_lt_top
    change ((originalPathSourcePortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).map Prod.fst) univ < (∞ : ℝ≥0∞) at hm
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] using hm
  have hmassT : (originalPathTargetPortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ < (∞ : ℝ≥0∞) := by
    have hm := hfinite.2.measure_univ_lt_top
    change ((originalPathTargetPortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).map Prod.snd) univ < (∞ : ℝ≥0∞) at hm
    simpa only [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ] using hm
  obtain ⟨ns, es, _, hs, _⟩ := exists_originalFiniteEdgeEndpointArrays
    (originalPathSourcePortPlan S w R ell scene) hsimple.1 hmassS
  obtain ⟨nt, et, _, _, ht⟩ := exists_originalFiniteEdgeEndpointArrays
    (originalPathTargetPortPlan S w R ell scene) hsimple.2 hmassT
  refine ⟨⟨ns, fun i ↦ (es i).1, hs, ?_⟩, ⟨nt, fun i ↦ (et i).2, ht, ?_⟩⟩
  · apply originalFiniteAtoms_forall_of_ae (fun i ↦ (es i).1)
      (P := fun p ↦ p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R)
    rw [← hs]
    exact hsupp.1
  · apply originalFiniteAtoms_forall_of_ae (fun i ↦ (et i).2)
      (P := fun p ↦ p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R)
    rw [← ht]
    exact hsupp.2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
