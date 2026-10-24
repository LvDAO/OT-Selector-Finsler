import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostActualFrameMean
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCutCostFrame

/-! Natural original-model expected screening cost on the literal FULL sampler. -/
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

/-- The original model chooses one quadratic constant before the tilt, matching
and reserve intensity. Every actual minimizer then chooses one physical frame,
before the reserve intensity, on which the literal FULL finite optimum has the
stated normalized expected-cost bound. All current, stage, label, bad-event and
finite-comparison inputs are produced internally. -/
theorem OriginalSeedConditionalMoments.exists_original_screening_fullValue_mean_frame
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
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (hlo : G.cut 0 = D.lo+(S.level : ℝ)) (hhi : G.cut G.count = D.hi+(S.level : ℝ))
    (hwidth : ∀ k : Fin G.count, G.cut (k+1)-G.cut k < gap)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus μ ν k) :
    let : IsProbabilityMeasure μ := D.support.source.probability
    let : IsProbabilityMeasure ν := D.support.target.probability
    ∃ C ≥ 0, ∀ (tilt : ℝ)
      (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g),
      (∀ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g, Q.value tilt ≤ Q'.value tilt) →
      ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
      ∀ rawRate : ℝ, 0 < rawRate →
      let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
      let FullLaw := fun R ↦ twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
        (Real.toNNReal (1+rawRate)*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
      (∀ R, 0 ≤ R → Integrable (originalScreeningFullValue b R (D.originalFocalKinetic gap) g tilt) (FullLaw R)) ∧
      ∀ ε > 0, ∀ᶠ R : ℝ in atTop,
        (∫ cloud, originalScreeningFullValue b R (D.originalFocalKinetic gap) g tilt cloud ∂FullLaw R)/V R ≤
          Q.value tilt+(12*C*(G.count : ℝ)*(finrank ℝ S.covector.ker : ℝ)*
            dyadicMatchingConstant (finrank ℝ S.covector.ker))*rawRate^(1-2/(finrank ℝ S.covector.ker : ℝ))+
            2*|tilt| * Gbound*rawRate+ε := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨C,hC,hphysical⟩ := D.exists_originalFocalMarkedCost_physical_quadratic_bound hF hw hgap hbounds g hgb
  refine ⟨C,hC,fun tilt Q hmin ↦ ?_⟩
  have hcuts (a : Fin (G.count+1)) : D.lo+(S.level : ℝ) ≤ G.cut a.val := by
    rw [← hlo]
    exact G.strictMono.monotone (Nat.zero_le _)
  obtain ⟨hL2,b,hproj,_hface,_hcut⟩ := D.exists_actualCanonical_screening_frame_cut_costs
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb tilt Q hmin (fun i : Fin G.count ↦ Ioc (G.cut i.val) (G.cut (i.val+1)))
    (fun a : Fin (G.count+1) ↦ G.cut a.val) hcuts
  refine ⟨b,fun rawRate hrate ↦ ?_⟩
  exact D.original_screening_fullValue_mean_in_frame hF hw hq cμ cν
    hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb tilt Q hmin
    G h₀ hN hlo hhi hwidth hmono hs ht hH b (fun i ↦ hL2 (Sum.inl i))
    (fun a i ↦ hproj i (Sum.inl a) (originalEuclideanNormalReadout (b i)))
    (fun a ↦ hL2 (Sum.inr a))
    (fun a i ↦ hproj i (Sum.inr a) (originalEuclideanNormalReadout (b i)))
    hrate hC hphysical sqrt_collar_limits.1 sqrt_collar_limits.2

end OTSelector.Reconstruction
