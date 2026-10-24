import OTSelector.Reconstruction.OriginalMinimizerActualRawFluxNearFrameReadouts
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualFrame

/-! Genuine original minimizing currents produce good physical frames near any prescribed frame. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The original density model internally supplies the genuine coordinate L2
currents once. For each neighborhood of each actual frame, it then chooses a
single frame annihilating every face-invariant component of the whole countable
clock family. Neither L2 evidence nor a boundary rate is supplied by the caller. -/
theorem OriginalSeedConditionalMoments.exists_actualCanonical_current_near_frames
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {densityμ densityν : M → ℝ} {v : M → E → ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀ x, 0 ≤ densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀ x, 0 ≤ densityν x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ,E) old).target, 0 ≤ v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {I : Type*} [Countable I] (A : I → Set ℝ) :
    let q := finrank ℝ S.covector.ker
    let η := originalEuclideanMollifier q
    ∃ hL2 : ∀ a k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w η (A a) scene k) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q)),
    ∀ (b₀ : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (δ : ℝ), 0 < δ →
      ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)),
        (∀ i, ‖b i-b₀ i‖ < δ) ∧
        ∀ i a C, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
          (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
            (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a) C) = 0 := by
  obtain ⟨hL2,_⟩ := D.exists_actualCanonicalCurrent_boundary_budget hF hw hq cμ cν
    hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb τ Q hmin A
  refine ⟨hL2,fun b₀ δ hδ ↦ ?_⟩
  exact D.exists_basis_near_projection_all_pathClockSetCurrent_readouts_zero hF hw hq hgap
    hbounds Q τ hmin (fun _ ↦ originalEuclideanMollifier _) 
    (fun _ ↦ (contDiff_originalEuclideanMollifier _).continuous.measurable)
    (fun _ ↦ integrable_originalEuclideanMollifier _) A hL2 b₀ hδ

end OTSelector.Reconstruction
