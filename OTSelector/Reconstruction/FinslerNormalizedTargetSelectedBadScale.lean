import OTSelector.Reconstruction.FinslerNormalizedTargetBadEnvelopeSummability
import OTSelector.Probability.SelectedIntegerBadEventSecondMoment

/-! # Actual target-envelope L2 tail at any scene-dependent measurable scale -/
open Set Function MeasureTheory Filter Module Manifold
open scoped ContDiff Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The literal whole original target-color count in the fixed normalized envelope. -/
def normalizedGlobalTargetEnvelopeCount
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (m : ℕ) (r : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
    (D.normalizedAdaptiveGlobalTargetEnvelope T cut m r ×ˢ {1})).toReal

theorem measurable_normalizedGlobalTargetEnvelopeCount
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    Measurable (D.normalizedGlobalTargetEnvelopeCount T cut m r) :=
  ((Measure.measurable_coe
    ((D.measurableSet_normalizedAdaptiveGlobalTargetEnvelope hF hw T hcut m r).prod
      (measurableSet_singleton 1))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal

/-- Current-bad errors dominated by the literal complete target envelope at
any measurable selected scale are integrable above each positive cutoff;
their L2 cost is bounded by the fixed original-count tail sum and vanishes. -/
theorem normalizedTarget_selected_bad_sq_tail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {r : ℝ} (hr : 0 ≤ r) {K : ℝ}
    (hK : (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
      (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
      2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
        (D.normalizedTargetPhaseCell T cut 0 0 (r + 2))).toReal *
          (Real.exp 1 - 1) + 1 ≤ K)
    {k : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℕ} (hk : Measurable k)
    {f : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∈ D.normalizedTargetPhaseCurveBadEvent T cut (k s) r K →
        |f s| ≤ C * |D.normalizedGlobalTargetEnvelopeCount T cut (k s) r s|) :
    let B := fun m ↦ D.normalizedTargetPhaseCurveBadEvent T cut m r K
    let W := fun m ↦ D.normalizedGlobalTargetEnvelopeCount T cut m r
    (∀ N : ℕ, 1 ≤ N →
      Integrable (fun s ↦ (({s | N ≤ k s ∧ s ∈ B (k s)}).indicator f s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, (({s | N ≤ k s ∧ s ∈ B (k s)}).indicator f s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        C ^ 2 * ∑' n : ℕ, ∫ s, ((B (n + N)).indicator (W (n + N)) s) ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ∧
    Tendsto (fun N : ℕ ↦ ∫ s,
      (({s | N ≤ k s ∧ s ∈ B (k s)}).indicator f s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
      atTop (𝓝 0) := by
  have hs := D.normalizedTargetPhaseCurveBadEvent_globalCount_summable hF hw T hcut Q hr hK
  have hB := fun m ↦ D.measurableSet_normalizedTargetPhaseCurveBadEvent hF hw T hcut m r K
  exact ⟨fun N hN ↦ integrable_selected_bad_sq_and_integral_le_tsum hk hB hf hC hdom
    hs.1 hs.2 hN, tendsto_selected_bad_sq_integral_zero hk hB hf hC hdom hs.1 hs.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
