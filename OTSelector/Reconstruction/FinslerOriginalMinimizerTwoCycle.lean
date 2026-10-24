import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMinimizerTwoCycle
import OTSelector.Reconstruction.FinslerOriginalWeightedStationaryMinimizer

/-! # Legal two-cycles of the actual general Finsler original minimizer -/
open Set Function MeasureTheory Filter Topology Module Manifold
open scoped ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original general Finsler coefficient supplies all analytic bounds
internally, so its actual weighted minimizer obeys the precise legal cycle
defect required by complete-path traffic. -/
theorem original_weighted_minimizer_legal_kineticTwoCycle
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, R.value t ≤ P.value t) :
    ∀ᵐ s ∂(R.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ∀ f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
          e.1.2 < f.2.2 → f.1.2 < e.2.2 →
            D.originalFocalKinetic gap e.1.2 e.2.2 (e.2.1 - e.1.1) +
              D.originalFocalKinetic gap f.1.2 f.2.2 (f.2.1 - f.1.1) ≤
            D.originalFocalKinetic gap e.1.2 f.2.2 (f.2.1 - e.1.1) +
              D.originalFocalKinetic gap f.1.2 e.2.2 (e.2.1 - f.1.1) + 4 * |t| * G := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨C, hC, hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  exact R.minimizer_legal_kineticTwoCycle (D.measurable_originalFocalKinetic hF hw gap)
    (D.originalFocalKinetic_nonneg hF hw hgap) hg hC hkb hgb hmin

/-- The existing actual general Finsler direct-method producer yields a
genuine original weighted stationary minimizer together with its derived
almost-sure all-occupied-edge legal kinetic two-cycle inequality. -/
theorem exists_original_weighted_stationary_minimizer_with_legal_twoCycle
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) (t : ℝ) :
    ∃ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      R.value t = D.originalWeightedStationaryInf gap g t ∧
      (∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g, R.value t ≤ P.value t) ∧
      ∀ᵐ s ∂(R.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
        ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
          ∀ f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
            e.1.2 < f.2.2 → f.1.2 < e.2.2 →
              D.originalFocalKinetic gap e.1.2 e.2.2 (e.2.1 - e.1.1) +
                D.originalFocalKinetic gap f.1.2 f.2.2 (f.2.1 - f.1.1) ≤
              D.originalFocalKinetic gap e.1.2 f.2.2 (f.2.1 - e.1.1) +
                D.originalFocalKinetic gap f.1.2 e.2.2 (e.2.1 - f.1.1) + 4 * |t| * G := by
  obtain ⟨R, hvalue, hmin⟩ := D.exists_original_weighted_stationary_minimizer
    hF hw hq hgap hbounds π hπ horder hg hgb hgc t
  exact ⟨R, hvalue, hmin,
    D.original_weighted_minimizer_legal_kineticTwoCycle hF hw hgap hbounds hg hgb t R hmin⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
