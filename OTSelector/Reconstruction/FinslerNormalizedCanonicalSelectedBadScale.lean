import OTSelector.Reconstruction.FinslerNormalizedSourceSelectedBadScale
import OTSelector.Reconstruction.FinslerNormalizedTargetSelectedBadScale
import OTSelector.Reconstruction.FinslerOriginalMeasurableCanonicalScale

/-! # Actual current-bad L2 tails at the internally constructed canonical scale -/
open Set Function MeasureTheory Filter Module Manifold
open scoped ContDiff Topology ENNReal NNReal
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

/-- Current-bad errors dominated by the literal complete source envelope at
the actual canonical scale are integrable above each positive cutoff;
their L2 cost is bounded by the fixed original-count tail sum and vanishes. -/
theorem normalizedCanonicalSource_selected_bad_sq_tail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (h : ℝ) (L : ℝ≥0) (ρ A : ℝ)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {r : ℝ} (hr : 0 ≤ r) {K : ℝ}
    (hK : (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
      (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
      2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
        (D.normalizedSourcePhaseCell T cut 0 0 (r + 2))).toReal *
          (Real.exp 1 - 1) + 1 ≤ K)
    {f : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
      ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∈ D.normalizedSourcePhaseCurveBadEvent T cut (k s) r K →
        |f s| ≤ C * |D.normalizedGlobalSourceEnvelopeCount T cut (k s) r s|) :
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let B := fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m r K
    let W := fun m ↦ D.normalizedGlobalSourceEnvelopeCount T cut m r
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
  exact D.normalizedSource_selected_bad_sq_tail hF hw T hcut Q hr hK
    (D.measurable_normalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A) hf hC hdom

/-- Current-bad errors dominated by the literal complete target envelope at
the actual canonical scale are integrable above each positive cutoff;
their L2 cost is bounded by the fixed original-count tail sum and vanishes. -/
theorem normalizedCanonicalTarget_selected_bad_sq_tail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (h : ℝ) (L : ℝ≥0) (ρ A : ℝ)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {r : ℝ} (hr : 0 ≤ r) {K : ℝ}
    (hK : (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
      (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
      2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
        (D.normalizedTargetPhaseCell T cut 0 0 (r + 2))).toReal *
          (Real.exp 1 - 1) + 1 ≤ K)
    {f : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
      ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∈ D.normalizedTargetPhaseCurveBadEvent T cut (k s) r K →
        |f s| ≤ C * |D.normalizedGlobalTargetEnvelopeCount T cut (k s) r s|) :
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
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
  exact D.normalizedTarget_selected_bad_sq_tail hF hw T hcut Q hr hK
    (D.measurable_normalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A) hf hC hdom

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
