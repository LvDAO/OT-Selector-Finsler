import OTSelector.Analysis.PolynomialExponentialSquareRootDecay
import OTSelector.Reconstruction.FinslerOriginalAdaptiveGlobalCount
import OTSelector.Analysis.PolynomialExponentialThreshold

/-! # Actual source bad-event mean square vanishes with no additional moment input -/
open Set Function MeasureTheory Filter Module Manifold
open scoped ContDiff Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
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

/-- A threshold determined only by original geometry and input intensities
makes the actual all-adaptive source-envelope bad-event count vanish in mean
square. All fourth moments, candidate cardinalities, rates, envelope growth
and event/count dependence have already been derived from those same data. -/
theorem exists_sourcePhaseCurveBadEvent_globalCount_second_moment_tendsto_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {r : ℝ} (hr : 0 ≤ r) :
    let N : ℕ → LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ := fun m s ↦
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.adaptiveGlobalSourceEnvelope cut m r ×ˢ {0})).toReal
    ∃ K : ℝ, 0 < K ∧
      (∀ m : ℕ, 1 ≤ m → Integrable
        (fun s ↦ ((D.sourcePhaseCurveBadEvent cut m r K).indicator (N m) s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ∧
      Tendsto (fun m : ℕ ↦ ∫ s,
        ((D.sourcePhaseCurveBadEvent cut m r K).indicator (N m) s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
        atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let N : ℕ → LegalMarkedOptimalInputScene q → ℝ := fun m s ↦
    ((s.2 : Measure (LegalColoredInputPoint q)) (D.adaptiveGlobalSourceEnvelope cut m r ×ˢ {0})).toReal
  let v₁ := (((volume : Measure (Fin q → ℝ)).prod μ)
    (markedPhaseSourceCell 1 (D.sourcePhaseLeg cut) 0 (D.sourcePhaseClocks cut) 1)).toReal
  let v := (((volume : Measure (Fin q → ℝ)).prod μ)
    (markedPhaseSourceCell 1 (D.sourcePhaseLeg cut) 0 (D.sourcePhaseClocks cut) (r + 2))).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  -- Conditions: polynomial growth and the actual envelope estimate.
  -- Objects: the threshold-indexed masked squared count on the unchanged scene law.
  -- Proof: choose one threshold above the exponential rate, then squeeze its means.
  refine Analysis.exists_threshold_mean_tendsto_zero
    (Q.law : Measure (LegalMarkedOptimalInputScene q)) q
    (C := 192 * Real.exp (Real.exp 1 - 1)) (v := v₁) (r := r)
    (rate := (3 * (2 * q : ℝ) + (3 : ℝ) ^ (2 * q)) + 2 * v * (Real.exp 1 - 1))
    (by positivity) hr (by
      have hexp : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr
        (Real.one_le_exp_iff.mpr zero_le_one)
      positivity)
    (fun K m s ↦ ((D.sourcePhaseCurveBadEvent cut m r K).indicator (N m) s) ^ 2)
    (fun _ _ _ ↦ sq_nonneg _) ?_
  intro K m hm
  simpa only [q, N, v₁, v, sub_sub] using
    D.sourcePhaseCurveBadEvent_globalEnvelope_second_moment hF hw hcut hm Q hr K

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
