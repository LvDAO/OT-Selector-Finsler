import OTSelector.Reconstruction.FinslerOriginalPalmMeanLowerBound
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMinimizingSequence

/-! Original Finsler data produce a true minimizing Palm and its actual sequence. -/
open Set Function MeasureTheory Filter Topology Module Manifold
open scoped ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Produce a genuine original minimizing sequence and its actual true-Palm
weak limit with original marginal laws and signed energy at most the infimum.
All tightness and energy witnesses come from the original conditional data. -/
theorem exists_original_minimizing_truePalm_energy_le
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
    (∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, D.originalWeightedStationaryInf gap g t ≤ R.value t) ∧
    ∃ Q : ℕ → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g,
      ∃ η : ProbabilityMeasure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
        Tendsto (fun n ↦ (Q n).value t) atTop
          (𝓝 (D.originalWeightedStationaryInf gap g t)) ∧
        (∀ n, (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) (Q n).law) ≤
            D.originalWeightedStationaryInf gap g t + 1 + |t| * G) ∧
        Tendsto (fun n ↦ (Q n).truePalmProbability) atTop (𝓝 η) ∧
        (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map
          (fun m ↦ m.1.1) = μ ∧
        (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map
          (fun m ↦ m.1.2) = ν ∧
        Integrable (fun m ↦ D.originalFocalKinetic gap m.1.1 m.1.2 m.2)
          (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) ∧
        Integrable (fun m ↦ g m.1.1 m.1.2)
          (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) ∧
        (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))) +
            t * (∫ m, g m.1.1 m.1.2
              ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))) ≤
                D.originalWeightedStationaryInf gap g t := by
  obtain ⟨hinf, Q, _hQ, hmean, hB⟩ := D.exists_original_weighted_minimizing_sequence
    hF hw hq hgap hbounds π hπ horder hg hgb t
  obtain ⟨η, φ, hφ, hweak, hs, ht, _hcarrier⟩ :=
    D.exists_original_weighted_truePalm_subsequence hF hw hgap hbounds Q
      (D.originalWeightedStationaryInf gap g t + 1 + |t| * G) hB
  have hmean' := hmean.comp hφ.tendsto_atTop
  have henergy := D.integrable_original_focal_signedPalm_of_truePalm_weak hF hw
    hgap hbounds hg hgc hgb (fun n ↦ Q (φ n)) η hweak t
    (D.originalWeightedStationaryInf gap g t) hmean'
  exact ⟨hinf, (fun n ↦ Q (φ n)), η, hmean', (fun n ↦ hB (φ n)), hweak,
    hs, ht, henergy.1, henergy.2.1, henergy.2.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
