import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostActualFrameMean
import OTSelector.Reconstruction.OriginalLegalWeightedClockCoupling
import OTSelector.Reconstruction.OriginalReversePressureOriginalFocalFrameLimit
import OTSelector.Reconstruction.OriginalReversePressureOrientedPoissonReadout
import OTSelector.Reconstruction.OriginalReversePressureSmallReserve

/-! The true original FULL screening experiment bounds pressure in its same physical frame. -/
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

/-- The actual original model and any true common current frame produce the
whole framed pressure, its concavity and Lipschitz regularity, and its upper bound
by the same original minimizer at the chosen tilt. Palm clock coupling, every
FULL finite expectation, exact Poisson normalization and vanishing reserve are
internal; no pressure limit or comparison is an input. -/
theorem OriginalSeedConditionalMoments.exists_originalFrame_pressure_le_minimizer
    (D : OriginalSeedConditionalMoments S w μ ν)
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
    : let : IsProbabilityMeasure μ := D.support.source.probability
    let : IsProbabilityMeasure ν := D.support.target.probability
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker)
        id id μ ν (originalScreeningFrameKinetic b (D.originalFocalKinetic gap)) g R t)
        atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧
      LipschitzWith ⟨Gbound,(abs_nonneg (g 0 0)).trans (hgb 0 0)⟩ p ∧
      p tilt ≤ Q.value tilt := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  have hG : 0 ≤ Gbound := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  obtain ⟨π,hprob,hπ,hstrict⟩ := Q.exists_originalForwardClockCoupling
  let : IsProbabilityMeasure π := hprob
  obtain ⟨p,hlim,hconc,hlip⟩ := D.exists_originalFocalFrame_pressure_limit hF hw hq hgap hbounds
    π hπ (hstrict.mono fun _ h ↦ h.le) hG hg hgb b
  obtain ⟨C,hC,hphysical⟩ := D.exists_originalFocalMarkedCost_physical_quadratic_bound
    hF hw hgap hbounds g hgb
  refine ⟨p,hlim,hconc,hlip,?_⟩
  apply originalPressure_le_sameCandidate_of_scaled_reserve_bounds
    (q := finrank ℝ S.covector.ker)
    (C := 12*C*(G.count : ℝ)*(finrank ℝ S.covector.ker : ℝ)*dyadicMatchingConstant (finrank ℝ S.covector.ker))
    (L := 2*|tilt| * Gbound) (by omega)
    hlip.continuous.continuousAt
  intro rawRate hrate
  have hm := D.original_screening_fullValue_mean_in_frame hF hw hq cμ cν
    hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb tilt Q hmin
    G h₀ hN hlo hhi hwidth hmono hs ht hH b hj hproj hcj hcproj hrate hC hphysical
    sqrt_collar_limits.1 sqrt_collar_limits.2
  apply originalPressure_frame_le_of_actualFullValue_mean_bound (q := finrank ℝ S.covector.ker) (by omega) μ ν b
    (D.originalFocalKinetic gap) (fun a d c _ x ↦ D.originalFocalKinetic_homogeneous gap a d c x) g
    (by linarith : 0 < 1+rawRate) (hlim _) 
  intro ε hε
  filter_upwards [hm.2 ε hε] with R hR
  have hrateEq : Real.toNNReal ((1+rawRate)*volume.real (originalCenteredPhysicalCubeRegion b (2*R))) =
      Real.toNNReal (1+rawRate)*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal := by
    rw [Real.toNNReal_mul (by linarith : 0 ≤ 1+rawRate),measureReal_def,ENNReal.toNNReal_toReal_eq]
  simpa only [hrateEq,mul_assoc] using hR

end OTSelector.Reconstruction
