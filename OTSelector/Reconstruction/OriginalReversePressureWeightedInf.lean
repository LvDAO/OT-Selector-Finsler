import OTSelector.Reconstruction.OriginalReversePressureNativeFocal

/-! The native original focal pressure is below the genuine weighted stationary infimum. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual direct method produces an attained original weighted minimizer,
and the genuine native screening comparison bounds pressure by its infimum.
The only transport input is the original forward population clock coupling. -/
theorem OriginalSeedConditionalMoments.originalFocalPressure_le_originalWeightedStationaryInf
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
    (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g) {p | p.1-S.level ∈ Ioo D.lo D.hi ∧
      p.2-S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) (τ : ℝ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) :
    let : IsProbabilityMeasure μ := D.support.source.probability
    let : IsProbabilityMeasure ν := D.support.target.probability
    limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker)
      id id μ ν (D.originalFocalKinetic gap) g R τ) ≤ D.originalWeightedStationaryInf gap g τ := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨Q,hvalue,_hmin⟩ := D.exists_original_weighted_stationary_minimizer
    hF hw hq hgap hbounds π hπ horder hg hgb hgc τ
  exact (D.originalFocalPressure_le_same_candidate hF hw hq cμ cν
    hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb hgc τ Q).trans_eq hvalue

end OTSelector.Reconstruction
