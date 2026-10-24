import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedReflectedMass
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedPlanFiniteness

/-! Actual same-orientation port marginals have their genuine reflected class densities. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Actual source and target port marginals remain in the literal chosen window, for any
Borel original retained path set. This uses the restrictions, not a sampling assertion. -/
theorem originalStageWindowPortMeasures_ae_mem_cube {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (scene : LegalMarkedOptimalInputScene q) :
    (∀ᵐ p ∂(originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).fst, p.1 ∈ K) ∧
    (∀ᵐ p ∂(originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)).snd, p.1 ∈ K) := by
  have hs : MeasurableSet ({e : LegalMarkedPhysicalEdge q | e.1.1 ∈ K} \ physicalPairAnchor ⁻¹' A) :=
    (hK.preimage measurable_fst.fst).diff (hA.preimage measurable_physicalPairAnchor)
  have ht : MeasurableSet ({e : LegalMarkedPhysicalEdge q | e.2.1 ∈ K} \ physicalPairAnchor ⁻¹' A) :=
    (hK.preimage measurable_snd.fst).diff (hA.preimage measurable_physicalPairAnchor)
  constructor
  · apply (ae_map_iff measurable_fst.aemeasurable (hK.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem hs] with e he
    exact he.1
  · apply (ae_map_iff measurable_snd.aemeasurable (hK.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem ht] with e he
    exact he.1

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Every actual same-orientation source/target port class has exactly its original count
as reflected mass. The one scene event is uniform over all original Borel clock classes. -/
theorem ae_all_originalOrientedStagePortDensities_integrable_mass
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    (hRone : 1 ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      let A := originalOrientedPathLengthRetained S w b R ell
      let K := originalCenteredPhysicalCubeRegion b (2 * R)
      ∀ C : Set ℝ,
      (Integrable (originalOrientedStageReflectedClassDensity b R C
          (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst)
        (volume.restrict K) ∧
        (∫ z in K, originalOrientedStageReflectedClassDensity b R C
          (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst z) =
          (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst.real {p | p.2 ∈ C}) ∧
      (Integrable (originalOrientedStageReflectedClassDensity b R C
          (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd)
        (volume.restrict K) ∧
        (∫ z in K, originalOrientedStageReflectedClassDensity b R C
          (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd z) =
          (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd.real {p | p.2 ∈ C}) := by
  filter_upwards [D.ae_originalOrientedStagePlans_finite hF hw Q b hell hR] with scene hfinite
  dsimp only at hfinite ⊢
  let A := originalOrientedPathLengthRetained S w b R ell
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  let : IsFiniteMeasure (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := hfinite.2.1
  let : IsFiniteMeasure (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := hfinite.2.2
  have hsupp := originalStageWindowPortMeasures_ae_mem_cube
    (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell)
    (isCompact_originalStagePhysicalCube b (2 * R)).measurableSet scene
  intro C
  exact ⟨originalOrientedStageReflectedClassDensity_integrable_mass b hRone _ hsupp.1 C,
    originalOrientedStageReflectedClassDensity_integrable_mass b hRone _ hsupp.2 C⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
