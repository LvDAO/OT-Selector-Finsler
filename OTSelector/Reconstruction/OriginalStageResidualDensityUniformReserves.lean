import OTSelector.Reconstruction.OriginalStageResidualDensityCanonical

/-! One full-scene event suffices for every reserve array and every kept original index set. -/
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
namespace OriginalStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {R ell : ℝ}
  {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
  (A : OriginalStageResidualDensityData S w R ell η)

/-- The same original scene with empty reserve index sets, used only as an algebraic base. -/
def emptyReserves : OriginalStageResidualDensityData S w R ell η :=
  ⟨A.scene, ⟨0, fun _ ↦ 0⟩, ⟨0, fun _ ↦ 0⟩, ∅, ∅⟩

omit [BorelSpace E] in
/-- Every original reserve array changes both stage densities by exactly the same constant.
The common shift follows from its literal half-open prefix-count identity. -/
theorem densities_eq_emptyReserves_add_common_constant {s t : ℝ} (hst : s ≤ t) :
    ∃ k : ℝ, (∀ z, A.sourceDensity s t z = A.emptyReserves.sourceDensity s t z + k) ∧
      ∀ z, A.targetDensity s t z = A.emptyReserves.targetDensity s t z + k := by
  let hs : ℝ := originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t)
  let ht : ℝ := originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t)
  have hinc := originalStageRemainingReservePrefix_increment A.sourceReserve A.targetReserve
    A.sourceKept A.targetKept hst
  change A.reservePrefix t - A.reservePrefix s = hs - ht at hinc
  refine ⟨(A.reservePrefix s + hs) / A.cubeVolume, ?_, ?_⟩
  · intro z
    simp [sourceDensity, gamma, emptyReserves, reservePrefix,
      originalStageRemainingReservePrefix, originalStageRemainingReserveClassCount, hs, cubeVolume,
      portPrefix]
    ring
  · intro z
    have hsame : (A.reservePrefix t + ht) / A.cubeVolume =
        (A.reservePrefix s + hs) / A.cubeVolume := by congr 1; linarith
    rw [← hsame]
    simp [targetDensity, gamma, emptyReserves, reservePrefix,
      originalStageRemainingReservePrefix, originalStageRemainingReserveClassCount, ht, cubeVolume,
      portPrefix]
    ring

end OriginalStageResidualDensityData
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- A single actual full-scene event supplies genuine L1 and equal stage mass for all
original reserve arrays and all original kept indices, including fully adaptive choices.
The proof uses one empty-reserve event and a common constant shift, avoiding uncountable
intersections or any conditional spatial-law premise. -/
theorem ae_all_originalCanonicalStageDensities_integrable_equal_mass_uniform_reserves
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier _) :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      Integrable (A.sourceDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      Integrable (A.targetDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      (∫ z in haarRootCube _ R, A.sourceDensity s t z) =
        ∫ z in haarRootCube _ R, A.targetDensity s t z := by
  let empty : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ := ⟨0, fun _ ↦ 0⟩
  filter_upwards [D.ae_all_originalCanonicalStageDensities hF hw Q hell hR empty empty hst]
    with scene hscene
  have hbase := hscene ∅ ∅
  intro sourceReserve targetReserve sourceKept targetKept
  dsimp only
  let A : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier _) :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  have hL1s : Integrable (A.emptyReserves.sourceDensity s t)
      (volume.restrict (haarRootCube _ R)) := hbase.1
  have hL1t : Integrable (A.emptyReserves.targetDensity s t)
      (volume.restrict (haarRootCube _ R)) := hbase.2.1
  have hmass : (∫ z in haarRootCube _ R, A.emptyReserves.sourceDensity s t z) =
      ∫ z in haarRootCube _ R, A.emptyReserves.targetDensity s t z := hbase.2.2.1
  have : IsFiniteMeasure (volume.restrict (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  obtain ⟨k, hs, ht⟩ := A.densities_eq_emptyReserves_add_common_constant hst
  have hfs : A.sourceDensity s t = fun z ↦ A.emptyReserves.sourceDensity s t z + k := funext hs
  have hft : A.targetDensity s t = fun z ↦ A.emptyReserves.targetDensity s t z + k := funext ht
  rw [hfs, hft]
  refine ⟨hL1s.add (integrable_const _), hL1t.add (integrable_const _), ?_⟩
  rw [integral_add hL1s (integrable_const _), integral_add hL1t (integrable_const _), hmass]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
