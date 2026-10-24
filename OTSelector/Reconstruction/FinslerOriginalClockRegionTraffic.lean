import OTSelector.Reconstruction.OriginalClockTrafficRegions
import OTSelector.Reconstruction.OriginalCompletePathCountableWeights
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Literal original-clock regions reconstruct the same complete path on the
actual original scene law. Clock endpoints are removed only on Lebesgue-null
singletons and all original source/target clock marginals are retained. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The unchanged original half-open physical occupation restricted to one
actual source/target birth/old and focal/regular clock region. -/
def originalClockRegionWeight (ε : ℝ) (i : Fin 8)
    (z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
    originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε i z

theorem measurable_originalClockRegionWeight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (ε : ℝ) (i : Fin 8) :
    Measurable (D.originalClockRegionWeight ε i) :=
  (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
    (measurable_originalClockTrafficRegionMask _ _ ε i)

/-- The actual original true-Palm clock marginals and the unchanged clock
occupation internally give the exact finite region partition. -/
theorem ae_originalClockRegionWeight_sum
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (ε : ℝ) :
    ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      ∀ᵐ c : ℝ ∂volume, (∑ i : Fin 8, D.originalClockRegionWeight ε i (m, c)) =
        ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ := by
  have ha : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ae_of_ae_map measurable_fst.fst.aemeasurable (by rw [Q.source_clock]; exact D.support.source.ae_open)
  have hb : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ae_of_ae_map measurable_fst.snd.aemeasurable (by rw [Q.target_clock]; exact D.support.target.ae_open)
  filter_upwards [ha, hb] with m ham hbm
  filter_upwards [(volume : Measure ℝ).ae_ne m.1.1] with c hc
  by_cases hactive : c ∈ Ioo m.1.1 m.1.2
  · simp only [originalClockRegionWeight, ← Finset.mul_sum]
    rw [sum_originalClockTrafficRegionMask _ _ ε (m, c)
      (by dsimp; linarith [ham.1]) (by dsimp; linarith [hbm.2]) hactive.1 hactive.2, mul_one]
  · have hnot : c ∉ Ico m.1.1 m.1.2 := by
      intro hm
      exact hactive ⟨lt_of_le_of_ne hm.1 (Ne.symm hc), hm.2⟩
    have hz : originalSeedClockOccupation S w c m = 0 := by
      rw [originalSeedClockOccupation_eq_indicator_velocity, indicator_of_notMem hnot]
    simp only [originalClockRegionWeight, hz, norm_zero, ENNReal.ofReal_zero,
      zero_mul, Finset.sum_const_zero]

/-- A region's literal original-scene complete-path traffic. -/
def originalClockRegionTraffic
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞) (ε : ℝ) (i : Fin 8)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) η (D.originalClockRegionWeight ε i) s

theorem measurable_originalClockRegionTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hη : Measurable η)
    (ε : ℝ) (i : Fin 8) : Measurable (D.originalClockRegionTraffic η ε i) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη (D.measurable_originalClockRegionWeight hF hw ε i)

/-- The eight actual original clock regions sum to the literal full original
traffic on the same genuine scene. No region identification is postulated. -/
theorem ae_completePathTraffic_eq_sum_originalClockRegions
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hη : Measurable η)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (ε : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η
        (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖) s =
      ∑ i : Fin 8, D.originalClockRegionTraffic η ε i s := by
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have hf := (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal
  have hp := D.measurable_originalClockRegionWeight hF hw ε
  have hsplit : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      ∀ᵐ c : ℝ ∂volume, (∑' i : Fin 8, D.originalClockRegionWeight ε i (m, c)) =
        ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ := by
    simpa only [tsum_fintype] using D.ae_originalClockRegionWeight_sum Q ε
  have hfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞) := by
    rw [D.lintegral_original_clockOccupation_norm_eq_pathLength hF hw hbounds Q]
    exact ENNReal.mul_ne_top hηfinite ENNReal.ofReal_ne_top
  have heq := Q.ae_completePathTraffic_congr_weights d hd hη
    (Measurable.tsum hp) hf hsplit hfinite
  filter_upwards [heq] with s hs
  rw [← hs, legalMarkedCompletePathTraffic_tsum_weights d hd hη _ hp s, tsum_fintype]
  rfl

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
