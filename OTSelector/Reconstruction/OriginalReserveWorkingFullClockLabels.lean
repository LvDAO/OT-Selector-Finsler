import OTSelector.Reconstruction.OriginalReserveFullWorkingInputExperiment
import OTSelector.Reconstruction.OriginalStageResidualDensityOriginalReserveLaw
import OTSelector.Reconstruction.OriginalStageClockSlabsActualArrays
import OTSelector.Reconstruction.OriginalStageClockSlabsSupport

/-! Every unchanged FULL label has its actual original clock support and true half-open stage label. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal NNReal Topology ContDiff BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- The actual FULL raw marginal internally puts every original finite label
in its true clock support and the original open clock interval on one event. -/
theorem ae_fullWorkingInput_originalClockSupport
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {Main Reserve : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν kin g}
    {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {ρ R : ℝ} :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R,
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
      (∀ i : Fin p.2.1.1, (p.2.1.2 i).2 ∈ μ.support ∧
        D.lo + (S.level : ℝ) < (p.2.1.2 i).2 ∧
          (p.2.1.2 i).2 < D.hi + (S.level : ℝ)) ∧
      (∀ j : Fin p.2.2.1, (p.2.2.2 j).2 ∈ ν.support ∧
        D.lo + (S.level : ℝ) < (p.2.2.2 j).2 ∧
          (p.2.2.2 j).2 < D.hi + (S.level : ℝ)) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  intro X
  have hc : ∀ᵐ cloud ∂(X.fullLaw : Measure
      (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map Prod.snd,
      (∀ i : ℕ, (cloud.1.2 i).2 ∈ μ.support ∧
        D.lo + (S.level : ℝ) < (cloud.1.2 i).2 ∧
          (cloud.1.2 i).2 < D.hi + (S.level : ℝ)) ∧
      (∀ j : ℕ, (cloud.2.2 j).2 ∈ ν.support ∧
        D.lo + (S.level : ℝ) < (cloud.2.2 j).2 ∧
          (cloud.2.2 j).2 < D.hi + (S.level : ℝ)) := by
    rw [X.fullLaw_full_sampler]
    filter_upwards [D.ae_all_originalReserveCloud_clock_support _,
      D.ae_all_originalReserveCloud_interior_clocks _] with cloud hs hi
    exact ⟨fun i ↦ ⟨hs.1 i, hi.1 i⟩, fun j ↦ ⟨hs.2 j, hi.2 j⟩⟩
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hc] with p hp
  exact ⟨fun i ↦ hp.1 i, fun j ↦ hp.2 j⟩

omit [BorelSpace E] in
/-- All FULL original labels are bounded and monochrome in every actual fine
grid with the original outer clock cuts. True support separation supplies the
monochromaticity; no finite sample balance or nonzero-class assumption occurs. -/
theorem ae_fullWorkingInput_all_grid_labels
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {Main Reserve : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν kin g}
    {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {ρ R : ℝ} :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R,
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
      ∀ G : OriginalStageClockGrid,
      G.cut 0 = D.lo + (S.level : ℝ) → G.cut G.count = D.hi + (S.level : ℝ) →
      (∀ i : Fin p.2.1.1, G.sourceLabel (p.2.1.2 i).2 < G.count) ∧
      (∀ j : Fin p.2.2.1, G.targetLabel (p.2.2.2 j).2 < G.count) ∧
      ∀ {δ diameter : ℝ}, ConditionalClockSupportBounds μ ν δ diameter →
        (∀ k : Fin G.count, G.cut (k+1)-G.cut k < δ) →
        ∀ k < G.count, (∀ i : Fin p.2.1.1, G.sourceLabel (p.2.1.2 i).2 ≠ k) ∨
          (∀ j : Fin p.2.2.1, G.targetLabel (p.2.2.2 j).2 ≠ k) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  intro X
  filter_upwards [D.ae_fullWorkingInput_originalClockSupport X] with p hp
  intro G hlo hhi
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply G.sourceLabel_lt_count
    rw [hlo, hhi]
    exact ⟨(hp.1 i).2.1.le, (hp.1 i).2.2⟩
  · intro j
    apply G.targetLabel_lt_count
    rw [hlo, hhi]
    exact ⟨(hp.2 j).2.1, (hp.2 j).2.2.le⟩
  · intro δ diameter hsep hwidth
    exact G.originalAtomLabels_monochrome hsep hwidth
      (fun i : Fin p.2.1.1 ↦ (p.2.1.2 i).2) (fun j : Fin p.2.2.1 ↦ (p.2.2.2 j).2)
      (fun i ↦ (hp.1 i).1) (fun j ↦ (hp.2 j).1)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
