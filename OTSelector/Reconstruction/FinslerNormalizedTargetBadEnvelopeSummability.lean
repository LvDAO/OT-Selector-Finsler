import OTSelector.Analysis.PolynomialFourthRootExponentialSummability
import OTSelector.Reconstruction.FinslerNormalizedAdaptiveTargetGlobalCount

/-! # Summable actual target-envelope costs on the normalized fixed-scale bad events -/
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

/-- Any threshold above the original-data exponential-rate threshold makes
the actual complete target-envelope bad-event square expectations summable. -/
theorem normalizedTargetPhaseCurveBadEvent_globalCount_summable
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
          (Real.exp 1 - 1) + 1 ≤ K) :
    let N : ℕ → LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ := fun m s ↦
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.normalizedAdaptiveGlobalTargetEnvelope T cut m r ×ˢ {1})).toReal
    (∀ m : ℕ, 1 ≤ m → Integrable
      (fun s ↦ ((D.normalizedTargetPhaseCurveBadEvent T cut m r K).indicator (N m) s) ^ 2)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ∧
      Summable (fun m : ℕ ↦ ∫ s,
        ((D.normalizedTargetPhaseCurveBadEvent T cut m r K).indicator (N m) s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) := by
  let q := finrank ℝ S.covector.ker
  let N : ℕ → LegalMarkedOptimalInputScene q → ℝ := fun m s ↦
    ((s.2 : Measure (LegalColoredInputPoint q))
      (D.normalizedAdaptiveGlobalTargetEnvelope T cut m r ×ˢ {1})).toReal
  let v₁ := (((volume : Measure (Fin q → ℝ)).prod ν)
    (D.normalizedTargetPhaseCell T cut 0 0 1)).toReal
  let v := (((volume : Measure (Fin q → ℝ)).prod ν)
    (D.normalizedTargetPhaseCell T cut 0 0 (r + 2))).toReal
  let a : ℕ → ℝ := fun m ↦
    (192 * Real.exp (Real.exp 1 - 1) *
      (1 + ((2 * (m : ℝ) + r) ^ q * v₁) ^ 4)) ^ (1 / 2 : ℝ) * Real.exp (-(m : ℝ) / 2)
  have hbound (m : ℕ) (hm : 1 ≤ m) :
      Integrable
        (fun s ↦ ((D.normalizedTargetPhaseCurveBadEvent T cut m r K).indicator (N m) s) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ((D.normalizedTargetPhaseCurveBadEvent T cut m r K).indicator (N m) s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ a m := by
    have h := D.normalizedTargetPhaseCurveBadEvent_globalEnvelope_second_moment
      hF hw T hcut hm Q hr K
    dsimp only at h
    refine ⟨h.1, h.2.trans ?_⟩
    change (192 * Real.exp (Real.exp 1 - 1) *
      (1 + ((2 * (m : ℝ) + r) ^ q * v₁) ^ 4)) ^ (1 / 2 : ℝ) *
        Real.exp ((-(K - (3 * (2 * q : ℝ) + (3 : ℝ) ^ (2 * q)) -
          2 * v * (Real.exp 1 - 1)) * (m : ℝ)) * (1 / 2 : ℝ)) ≤ a m
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    apply Real.exp_le_exp.mpr
    change (3 * (2 * q : ℝ) + (3 : ℝ) ^ (2 * q)) +
      2 * v * (Real.exp 1 - 1) + 1 ≤ K at hK
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  refine ⟨fun m hm ↦ (hbound m hm).1, ?_⟩
  apply (summable_polynomialFourthRoot_exp_neg_half_nat q
    (C := 192 * Real.exp (Real.exp 1 - 1)) (v := v₁) (r := r)
    (by positivity) hr).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_of_nonneg (integral_nonneg (fun s ↦ sq_nonneg _))]
  exact (hbound m hm).2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
