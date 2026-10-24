import OTSelector.Reconstruction.FiniteWeightedPathLengthTail
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! # Literal long-path traffic of the unchanged original matching -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Complete absolute traffic of exactly those original edges whose true full
physical path length exceeds the threshold. -/
def originalSeedLongPathAbsoluteTraffic (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (R : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (fun z ↦ if R < originalSeedPairPathLength S w z.1 then
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ else 0) scene

theorem measurable_originalSeedLongPathAbsoluteTraffic
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) (R : ℝ) :
    Measurable (originalSeedLongPathAbsoluteTraffic S w η R) :=
  measurable_legalMarkedCompletePathTraffic _
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal
    (Measurable.ite (measurableSet_lt measurable_const
      ((measurable_originalSeedPairPathLength S hF hw).comp measurable_fst))
      (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal measurable_const)

/-- The literal long-path readout is the indicator restriction of the same
original pair kernel and the same full original clock integral. -/
theorem originalSeedLongPathAbsoluteTraffic_eq_pairTail
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (R : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalSeedLongPathAbsoluteTraffic S w η R scene =
      ∫⁻ a, if R < originalSeedPairPathLength S w a.2 then
        (∫⁻ c : ℝ, ENNReal.ofReal (η (a.1 + originalSeedPathOffset S w c a.2)) *
          ENNReal.ofReal ‖originalSeedClockOccupation S w c a.2‖ ∂volume) else 0
        ∂physicalScenePairKernel scene.1 := by
  apply lintegral_congr_ae
  filter_upwards [] with a
  by_cases h : R < originalSeedPairPathLength S w a.2 <;> simp only [h, ite_true, ite_false, mul_zero, lintegral_zero]

/-- Literal long-path absolute traffic is dominated in every scene by the
same full absolute traffic, without a count or independence assumption. -/
theorem originalSeedLongPathAbsoluteTraffic_le_full
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (R : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalSeedLongPathAbsoluteTraffic S w η R scene ≤
      originalSeedCompletePathAbsoluteTraffic S w η scene := by
  apply lintegral_mono
  intro a
  apply lintegral_mono
  intro c
  by_cases h : R < originalSeedPairPathLength S w a.2
  · simp only [h, ite_true, le_refl]
  · simp only [h, ite_false, mul_zero, zero_le]

/-- In each original scene with finite full traffic, literal long-path traffic
vanishes. The controlling measure is the actual weighted original pair kernel. -/
theorem tendsto_originalSeedLongPathAbsoluteTraffic_zero_of_finite
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hfinite : originalSeedCompletePathAbsoluteTraffic S w η scene ≠ (⊤ : ℝ≥0∞)) :
    Tendsto (fun R : ℝ ↦ originalSeedLongPathAbsoluteTraffic S w η R scene) atTop (𝓝 0) := by
  simp_rw [originalSeedLongPathAbsoluteTraffic_eq_pairTail]
  exact tendsto_lintegral_weighted_real_readout_tail _ hfinite
    ((measurable_originalSeedPairPathLength S hF hw).comp measurable_snd)

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Genuine original weighted energy produces the almost-sure finite dominating
traffic and hence the actual original long-path traffic limit. -/
theorem ae_tendsto_original_longPathAbsoluteTraffic_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηm : Measurable η) (hηi : Integrable η volume) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Tendsto (fun R : ℝ ↦ originalSeedLongPathAbsoluteTraffic S w η R scene) atTop (𝓝 0) := by
  filter_upwards [D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hηm hηi]
    with scene hscene
  exact tendsto_originalSeedLongPathAbsoluteTraffic_zero_of_finite S hF hw η scene hscene.ne

/-- The actual full-traffic square estimate transfers to a vanishing literal
long-path second moment on the same original weighted matching. -/
theorem integrable_sq_and_tendsto_original_longPathAbsoluteTraffic_sq
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηm : Measurable η) (hηi : Integrable η volume)
    (hfullI : Integrable (fun scene ↦
      (originalSeedCompletePathAbsoluteTraffic S w η scene).toReal ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) :
    (∀ R : ℝ, Integrable (fun scene ↦
      (originalSeedLongPathAbsoluteTraffic S w η R scene).toReal ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ∧
    Tendsto (fun R : ℝ ↦ ∫ scene,
      (originalSeedLongPathAbsoluteTraffic S w η R scene).toReal ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
      atTop (𝓝 0) :=
  integrable_sq_and_tendsto_integral_sq_of_nonnegative_tail _
    (measurable_originalSeedLongPathAbsoluteTraffic S hF hw hηm)
    ((D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hηm hηi).mono
      fun _ h ↦ h.ne) hfullI (originalSeedLongPathAbsoluteTraffic_le_full S w η)
    (D.ae_tendsto_original_longPathAbsoluteTraffic_zero hF hw hbounds Q hηm hηi)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
