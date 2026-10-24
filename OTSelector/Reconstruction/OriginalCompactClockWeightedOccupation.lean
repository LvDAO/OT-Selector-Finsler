import OTSelector.Reconstruction.FinslerOriginalClockOccupationPathMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalMomentum
import Mathlib.MeasureTheory.Integral.Prod

/-! Compact original physical-clock windows have true momentum-weighted occupation
moments from the original kinetic moment alone. All normalizers are deterministic. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Any deterministic normalized full momentum times the actual original
occupation is integrable on every compact interior physical-clock window. -/
theorem OriginalSeedConditionalMoments.integrable_original_compactClock_weightedOccupation
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hclock : ∀ c ∈ J, c - (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    Integrable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ‖T *ᵥ originalSeedPairMomentum S w z.1‖ * ‖originalSeedClockOccupation S w z.2 z.1‖)
      ((legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).prod (volume.restrict J)) := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  let κ : Measure ℝ := volume.restrict J
  have : IsFiniteMeasure κ := ⟨by simpa only [κ, Measure.restrict_apply_univ] using hJ.measure_lt_top⟩
  have hKcont : ContinuousOn (fun c : ℝ ↦ originalSeedKernel S w (c - (S.level : ℝ))) J :=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_id.sub continuousOn_const) hclock
  obtain ⟨L₀, hL₀⟩ := hJ.exists_bound_of_continuousOn hKcont
  let L : ℝ := max L₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  have hK : ∀ c ∈ J, ‖originalSeedKernel S w (c - (S.level : ℝ))‖ ≤ L :=
    fun c hc ↦ (hL₀ c hc).trans (le_max_left _ _)
  have hOcc (c : ℝ) (hc : c ∈ J) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
      ‖originalSeedClockOccupation S w c m‖ ≤ L * ‖originalSeedPairMomentum S w m‖ := by
    rw [originalSeedClockOccupation_eq_indicator_velocity]
    by_cases hm : c ∈ Ico m.1.1 m.1.2
    · rw [indicator_of_mem hm]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (hK c hc) (norm_nonneg _))
    · rw [indicator_of_notMem hm, norm_zero]
      exact mul_nonneg hL (norm_nonneg _)
  have hP := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have hmajor := (hP.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ)) κ)).const_mul (‖T‖ * L)
  have hmomentum : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      T *ᵥ originalSeedPairMomentum S w z.1) :=
    (Matrix.toLin' T).continuous_of_finiteDimensional.measurable.comp
      ((measurable_originalSeedPairMomentum S hF hw).comp measurable_fst)
  have hmeas : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ‖T *ᵥ originalSeedPairMomentum S w z.1‖ * ‖originalSeedClockOccupation S w z.2 z.1‖) :=
    hmomentum.norm.mul (measurable_originalSeedClockOccupation S hF hw).norm
  have hclockAE : ∀ᵐ z ∂η.prod κ, z.2 ∈ J :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (hJ.measurableSet.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ ↦ ae_restrict_mem hJ.measurableSet)
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [hclockAE] with z hz
  change |‖T *ᵥ originalSeedPairMomentum S w z.1‖ *
    ‖originalSeedClockOccupation S w z.2 z.1‖| ≤ _
  rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ (‖T‖ * ‖originalSeedPairMomentum S w z.1‖) *
        (L * ‖originalSeedPairMomentum S w z.1‖) :=
      mul_le_mul (Matrix.linfty_opNorm_mulVec _ _) (hOcc z.2 hz z.1)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- Any jointly chosen mask bounded by one and confined to an actual compact
clock window has finite normalized-momentum-weighted original occupation. -/
theorem OriginalSeedConditionalMoments.lintegral_original_compactClock_maskedWeightedOccupation_lt_top
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hclock : ∀ c ∈ J, c - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (hmask : ∀ z, mask z ≤ 1) (hzero : ∀ m c, c ∉ J → mask (m, c) = 0) :
    (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖T *ᵥ originalSeedPairMomentum S w m‖ *
      (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))
      ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) < (∞ : ℝ≥0∞) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := Q.palm_probability
  have hI := D.integrable_original_compactClock_weightedOccupation hF hw hgap hbounds Q T hJ hclock
  have hmomentum : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      T *ᵥ originalSeedPairMomentum S w z.1) :=
    (Matrix.toLin' T).continuous_of_finiteDimensional.measurable.comp
      ((measurable_originalSeedPairMomentum S hF hw).comp measurable_fst)
  have hmeas : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ‖T *ᵥ originalSeedPairMomentum S w z.1‖ * ‖originalSeedClockOccupation S w z.2 z.1‖) :=
    hmomentum.norm.mul (measurable_originalSeedClockOccupation S hF hw).norm
  have hfinite : (∫⁻ m, ∫⁻ c in J, ENNReal.ofReal
      (‖T *ᵥ originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖)
      ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) < (∞ : ℝ≥0∞) := by
    rw [← lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
    exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hI.2
  apply lt_of_le_of_lt _ hfinite
  apply lintegral_mono
  intro m
  dsimp only
  rw [← lintegral_indicator hJ.measurableSet]
  apply lintegral_mono
  intro c
  by_cases hc : c ∈ J
  · rw [indicator_of_mem hc, ENNReal.ofReal_mul (norm_nonneg _)]
    calc
      _ ≤ ENNReal.ofReal ‖T *ᵥ originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * 1) :=
        mul_le_mul_right (mul_le_mul_right (hmask (m, c)) _) _
      _ = _ := by rw [mul_one]
  · simp only [hzero m c hc, mul_zero, indicator_of_notMem hc, le_refl]

end OTSelector.Reconstruction
