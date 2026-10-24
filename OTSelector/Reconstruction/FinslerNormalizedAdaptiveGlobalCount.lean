import OTSelector.Reconstruction.FinslerNormalizedAdaptiveGlobalEnvelope

/-! # Whole original source counts dominate all adaptively chosen actual tubes -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Even on the geometric bad event, every later selected admissible curve
and its actual edge subfamily are dominated by one unchanged original count. -/
theorem ae_count_normalizedSourcePathPhaseTube_le_globalEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ,
        ‖γ 0‖ ≤ (m : ℝ) →
        (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
          ‖γ a - γ b‖ ≤ (m : ℝ) * |a - b|) →
        ∀ V : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)),
          (∀ e ∈ V, e.1.2 ∈ D.sourcePhaseClocks cut ∧
            ∃ t ∈ Icc (0 : ℝ) 1,
              ‖phasePairVector (normalizedMomentumNodePosition S w T (cut + S.level) e)
                (normalizedMomentumNodeValue S w T e) - γ t‖ ≤ r) →
          (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V < (∞ : ℝ≥0∞) ∧
            ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V).toReal ≤
              ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
                (D.normalizedAdaptiveGlobalSourceEnvelope T cut m r ×ˢ {0})).toReal := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hB := D.measurableSet_normalizedAdaptiveGlobalSourceEnvelope hF hw T hcut m r
  have hfin := (D.normalizedAdaptiveGlobalSourceEnvelope_intensity_lt_top hF hw T hcut m r).ne
  have hN := (Q.original_source_fourth_moment hB hfin).1
  filter_upwards [Q.full_matching, hN] with s hs hN
  intro γ hroot hLip V hV
  have hsub : V ⊆ Prod.fst ⁻¹' D.normalizedAdaptiveGlobalSourceEnvelope T cut m r := by
    intro e he
    apply D.normalized_source_pathPhaseTube_mem_globalSourceEnvelope hF hw T hcut
      γ hroot hLip hr e.1.1 (physicalPairAnchor e).2 (hV e he).1
    simpa only [normalizedMomentumNodePosition, normalizedMomentumNodeValue,
      originalMomentumNodePosition, originalMomentumNodeValue] using (hV e he).2
  have hle : (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V ≤
      (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.normalizedAdaptiveGlobalSourceEnvelope T cut m r ×ˢ {0}) := by
    apply (measure_mono hsub).trans_eq
    rw [← Measure.fst_apply hB, hs.source_marginal, legalInputColorMeasure_apply_prod _ _ _ hB]
  exact ⟨hle.trans_lt hN, ENNReal.toReal_mono hN.ne hle⟩

/-- The full count dominating every adaptive source tube has polynomial
fourth-moment prefactor and the exact exponentially small original bad-event factor. -/
theorem normalizedSourcePhaseCurveBadEvent_globalEnvelope_second_moment
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {r : ℝ} (hr : 0 ≤ r) (K : ℝ) :
    let N : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ := fun s ↦
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.normalizedAdaptiveGlobalSourceEnvelope T cut m r ×ˢ {0})).toReal
    let v₁ := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 1)).toReal
    let v := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 (r + 2))).toReal
    Integrable (fun s ↦ ((D.normalizedSourcePhaseCurveBadEvent T cut m r K).indicator N s) ^ 2)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, ((D.normalizedSourcePhaseCurveBadEvent T cut m r K).indicator N s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        (192 * Real.exp (Real.exp 1 - 1) *
          (1 + ((2 * (m : ℝ) + r) ^ finrank ℝ S.covector.ker * v₁) ^ 4)) ^ (1 / 2 : ℝ) *
          Real.exp ((-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
            (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) - 2 * v * (Real.exp 1 - 1)) *
              (m : ℝ)) * (1 / 2 : ℝ)) := by
  have h := D.normalizedSourcePhaseCurveBadEvent_count_second_moment hF hw T hcut hm Q r K
    (D.measurableSet_normalizedAdaptiveGlobalSourceEnvelope hF hw T hcut m r)
    (D.normalizedAdaptiveGlobalSourceEnvelope_intensity_lt_top hF hw T hcut m r).ne
  simpa only [D.normalizedAdaptiveGlobalSourceEnvelope_intensity_real hF hw T hcut m hr] using h

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
