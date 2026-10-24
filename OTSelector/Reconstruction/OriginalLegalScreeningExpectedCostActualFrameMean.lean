import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostActualProducerMean
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximum

/-! The real original minimizer controls FULL finite means on any actual admissible frame. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- On any genuine common current frame, the actual original focal model
constructs every legal repair and all expectation budgets internally. No stage
plan, signed-maximum producer, finite-value comparison or exceptional rate is an
input. The same physical cost constant controls good and bad observations. -/
theorem OriginalSeedConditionalMoments.original_screening_fullValue_mean_in_frame
    (D : OriginalSeedConditionalMoments S w μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {densityμ densityν : M → ℝ} {v : M → E → ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀ x, 0 ≤ densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀ x, 0 ≤ densityν x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ,E) old).target, 0 ≤ v old y)
    (hdensityμ : PopulationSeedClockDensity S w (μ.map (fun x : ℝ ↦ x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w (ν.map (fun x : ℝ ↦ x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {g : ℝ → ℝ → ℝ} {Gbound : ℝ} (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ Gbound)
    (tilt : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value tilt ≤ Q'.value tilt)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (hlo : G.cut 0 = D.lo+(S.level : ℝ)) (hhi : G.cut G.count = D.hi+(S.level : ℝ))
    (hwidth : ∀ k : Fin G.count, G.cut (k+1)-G.cut k < gap)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus μ ν k)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (hproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (G.cut a.val) (G.cut (a.val+1)))) (hj a) (originalEuclideanNormalReadout (b i))) = 0)
    (hcj : ∀ a : Fin (G.count+1), ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (D.lo+(S.level : ℝ)) (G.cut a.val)) scene k) 2 (Q.law : Measure _))
    (hcproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (D.lo+(S.level : ℝ)) (G.cut a.val))) (hcj a) (originalEuclideanNormalReadout (b i))) = 0)
    {rawRate C : ℝ} (hrate : 0 < rawRate) (hC : 0 ≤ C)
    (hphysical : ∀ (a d : ℝ) (x y : Fin (finrank ℝ S.covector.ker) → ℝ) (t : ℝ),
      D.originalFocalKinetic gap a d (y-x)-t*g a d ≤
        C*dist ((EuclideanSpace.equiv _ ℝ).symm x) ((EuclideanSpace.equiv _ ℝ).symm y)^2+|t| * Gbound)
    {ell : ℝ → ℝ} (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
    let FullLaw := fun R ↦ twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
      (Real.toNNReal (1+rawRate)*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
    (∀ R, 0 ≤ R → Integrable (originalScreeningFullValue b R (D.originalFocalKinetic gap) g tilt) (FullLaw R)) ∧
    ∀ ε > 0, ∀ᶠ R : ℝ in atTop,
      (∫ cloud, originalScreeningFullValue b R (D.originalFocalKinetic gap) g tilt cloud ∂FullLaw R)/V R ≤
        Q.value tilt+(12*C*(G.count : ℝ)*(finrank ℝ S.covector.ker : ℝ)*
          dyadicMatchingConstant (finrank ℝ S.covector.ker))*rawRate^(1-2/(finrank ℝ S.covector.ker : ℝ))+
          2*|tilt| * Gbound*rawRate+ε := by
  have hk0 := D.originalFocalKinetic_nonneg hF hw hgap
  have hkb := originalScreening_quadratic_bound_of_physical_cost hk0 hphysical
  have hp := D.originalActualClockBlock_signedMaximumProducer hF hw hq hgap hbounds hC
    ((abs_nonneg (g 0 0)).trans (hgb 0 0)) hphysical tilt Q G hs ht hmono h₀ hN b hrate hj
  exact D.original_screening_actualProducer_fullValue_mean hF hw hq cμ cν
    hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb tilt Q hmin
    G h₀ hN hlo hhi hwidth hmono hH b hj hproj hcj hcproj hrate hC hkb hp hlarge hsmall

end OTSelector.Reconstruction
