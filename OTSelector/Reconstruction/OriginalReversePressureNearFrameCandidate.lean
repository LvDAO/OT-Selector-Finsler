import OTSelector.Reconstruction.OriginalReversePressureNearFrameMinimizer
import OTSelector.Reconstruction.FinslerOriginalWeightedStationaryMinimizer

/-! Every genuine original candidate bounds a pressure in each prescribed frame neighborhood. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The original candidate supplies its own forward population coupling, and
the actual direct method selects an attained minimizer internally. Its genuine
screening construction yields a nearby physical-frame pressure below the
unchanged candidate's signed value. No minimizer, comparison, Euclidean moment
or pressure limit is assumed. -/
theorem OriginalSeedConditionalMoments.exists_original_nearFrame_pressure_le_candidate
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
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b₀ : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {δ : ℝ} (hδ : 0 < δ) :
    let : IsProbabilityMeasure μ := D.support.source.probability
    let : IsProbabilityMeasure ν := D.support.target.probability
    ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
      (∀ i, ‖b i-b₀ i‖ < δ) ∧ ∃ p : ℝ,
        Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker)
          id id μ ν (originalScreeningFrameKinetic b (D.originalFocalKinetic gap)) g R τ)
          atTop (𝓝 p) ∧ p ≤ Q.value τ := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨π,hprob,hπ,hforward⟩ := Q.exists_originalForwardClockCoupling
  let : IsProbabilityMeasure π := hprob
  obtain ⟨R,_hvalue,hmin⟩ := D.exists_original_weighted_stationary_minimizer hF hw hq
    hgap hbounds π hπ (hforward.mono fun _ h ↦ h.le) hg hgb hgc τ
  obtain ⟨b,hnear,p,hlim,_hconc,_hlip,hvalue⟩ := D.exists_original_nearFrame_pressure_le_minimizer
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb τ R hmin b₀ hδ
  exact ⟨b,hnear,p τ,hlim τ,hvalue.trans (hmin Q)⟩

end OTSelector.Reconstruction
