import OTSelector.Reconstruction.OriginalStageResidualDensityFiniteCountingArray
import OTSelector.Reconstruction.OriginalStageResidualDensityActualPorts
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedActualPorts

/-! Actual original port restrictions produce finite unchanged endpoint arrays. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators ContDiff Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A true finite original integer edge measure produces both endpoint tuples from the
same original edges. No endpoint count or selected spatial distribution is assumed. -/
theorem exists_originalFiniteEdgeEndpointArrays {q : ℕ}
    (π : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hπ : IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge q) π)
    (hfinite : (π : Measure (LegalMarkedPhysicalEdge q)) univ < (∞ : ℝ≥0∞)) :
    ∃ n : ℕ, ∃ edges : Fin n → LegalMarkedPhysicalEdge q,
      (π : Measure (LegalMarkedPhysicalEdge q)) = ∑ i, Measure.dirac (edges i) ∧
      (π : Measure (LegalMarkedPhysicalEdge q)).fst = ∑ i, Measure.dirac (edges i).1 ∧
      (π : Measure (LegalMarkedPhysicalEdge q)).snd = ∑ i, Measure.dirac (edges i).2 := by
  obtain ⟨n, edges, heq⟩ := exists_originalFiniteCountingArray 0 π
    ((isLegalSimpleCountingMeasure_iff _ _).mp hπ).1 hfinite
  refine ⟨n, edges, heq, ?_, ?_⟩
  · change (π : Measure (LegalMarkedPhysicalEdge q)).map Prod.fst = _
    rw [heq, Measure.map_finset_sum measurable_fst.aemeasurable]
    simp only [Measure.map_dirac]
  · change (π : Measure (LegalMarkedPhysicalEdge q)).map Prod.snd = _
    rw [heq, Measure.map_finset_sum measurable_snd.aemeasurable]
    simp only [Measure.map_dirac]

/-- A property of the actual finite point measure holds for every original indexed atom.
Thus uniform pointwise kernel laws can be used on the actual endpoint arrays. -/
theorem originalFiniteAtoms_forall_of_ae {q n : ℕ}
    (points : Fin n → LegalMarkedPhysicalPoint q) {P : LegalMarkedPhysicalPoint q → Prop}
    (hP : ∀ᵐ p ∂(∑ i, Measure.dirac (points i)), P p) : ∀ i, P (points i) := by
  rw [← Measure.sum_fintype, Measure.ae_sum_iff] at hP
  intro i
  simpa only [ae_dirac_eq, Filter.eventually_pure] using hP i

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The genuine original same-orientation source and target ports internally produce
finite arrays of their unchanged original edges and endpoints, all in the same physical
cube. The arrays are not given an iid spatial law. -/
theorem ae_exists_originalOrientedStagePortArrays
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      let A := originalOrientedPathLengthRetained S w b R ell
      let K := originalCenteredPhysicalCubeRegion b (2 * R)
      (∃ n : ℕ, ∃ points : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker),
        (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst =
          ∑ i, Measure.dirac (points i) ∧ ∀ i, (points i).1 ∈ K) ∧
      (∃ n : ℕ, ∃ points : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker),
        (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd =
          ∑ i, Measure.dirac (points i) ∧ ∀ i, (points i).1 ∈ K) := by
  filter_upwards [Q.full_matching, D.ae_originalOrientedStagePlans_finite hF hw Q b hell hR]
    with scene hfull hfinite
  dsimp only at hfinite ⊢
  let A := originalOrientedPathLengthRetained S w b R ell
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  have hsimple := hfull.originalStage_restrictions_simple A K
  have hsupp := originalStageWindowPortMeasures_ae_mem_cube
    (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell)
    (isCompact_originalStagePhysicalCube b (2 * R)).measurableSet scene
  obtain ⟨ns, es, _, hsource, _⟩ := exists_originalFiniteEdgeEndpointArrays
    (originalStageWindowSourcePortPlan A K scene) hsimple.2.1 hfinite.2.1.measure_univ_lt_top
  obtain ⟨nt, et, _, _, htarget⟩ := exists_originalFiniteEdgeEndpointArrays
    (originalStageWindowTargetPortPlan A K scene) hsimple.2.2 hfinite.2.2.measure_univ_lt_top
  refine ⟨⟨ns, fun i ↦ (es i).1, hsource, ?_⟩,
    ⟨nt, fun i ↦ (et i).2, htarget, ?_⟩⟩
  · apply originalFiniteAtoms_forall_of_ae (fun i ↦ (es i).1) (P := fun p ↦ p.1 ∈ K)
    rw [← hsource]
    exact hsupp.1
  · apply originalFiniteAtoms_forall_of_ae (fun i ↦ (et i).2) (P := fun p ↦ p.1 ∈ K)
    rw [← htarget]
    exact hsupp.2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
