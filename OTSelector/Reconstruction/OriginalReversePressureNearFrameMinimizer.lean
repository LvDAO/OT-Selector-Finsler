import OTSelector.Reconstruction.OriginalReversePressureActualFrame
import OTSelector.Reconstruction.OriginalMinimizerActualRawFluxNearFrame
import OTSelector.Reconstruction.OriginalLegalScreeningOriginalClockGrid

/-! The original model constructs arbitrarily close physical-frame pressures below its same minimizer. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The genuine original model constructs the clock grid, all minimizing
current L2 and a common good frame in any prescribed neighborhood, then
internally completes signed finite repair, its whole expectation, the exact
Poisson pressure normalization and reserve removal. The candidate and tilt
stay fixed throughout. No grid, current, frame, plan or comparison is an input. -/
theorem OriginalSeedConditionalMoments.exists_original_nearFrame_pressure_le_minimizer
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
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
    (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {Gbound : ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ Gbound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ Q'.value τ)
    (b₀ : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {δ : ℝ} (hδ : 0 < δ) :
    let : IsProbabilityMeasure μ := D.support.source.probability
    let : IsProbabilityMeasure ν := D.support.target.probability
    ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
      (∀ i, ‖b i-b₀ i‖ < δ) ∧ ∃ p : ℝ → ℝ,
        (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker)
          id id μ ν (originalScreeningFrameKinetic b (D.originalFocalKinetic gap)) g R t)
          atTop (𝓝 (p t))) ∧
        ConcaveOn ℝ univ p ∧
        LipschitzWith ⟨Gbound,(abs_nonneg (g 0 0)).trans (hgb 0 0)⟩ p ∧
        p τ ≤ Q.value τ := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨π,_hprob,hπ,hforward⟩ := Q.exists_originalForwardClockCoupling
  obtain ⟨G,_hcount,hlo,hhi,hwidth,hs,ht,hmono,h₀,hN,hH,_hsum,_htsum⟩ :=
    D.exists_originalLegalScreeningClockGrid hgap hbounds π hπ
      (hforward.mono fun _ h ↦ h.le)
  let A : Fin G.count ⊕ Fin (G.count+1) → Set ℝ :=
    Sum.elim (fun a ↦ Ioc (G.cut a.val) (G.cut (a.val+1)))
      (fun a ↦ Ioc (D.lo+(S.level : ℝ)) (G.cut a.val))
  obtain ⟨hL2,hframes⟩ := D.exists_actualCanonical_current_near_frames hF hw (by omega)
    cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb τ Q hmin A
  obtain ⟨b,hnear,hproj⟩ := hframes b₀ δ hδ
  obtain ⟨p,hlim,hconc,hlip,hvalue⟩ := D.exists_originalFrame_pressure_le_minimizer
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb τ Q hmin G h₀ hN hlo hhi hwidth hmono hs ht hH b
    (fun a ↦ hL2 (Sum.inl a))
    (fun a i ↦ hproj i (Sum.inl a) (originalEuclideanNormalReadout (b i)))
    (fun a ↦ hL2 (Sum.inr a))
    (fun a i ↦ hproj i (Sum.inr a) (originalEuclideanNormalReadout (b i)))
  exact ⟨b,hnear,p,hlim,hconc,hlip,hvalue⟩

end OTSelector.Reconstruction
