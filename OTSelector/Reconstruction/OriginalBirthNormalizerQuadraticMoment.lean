import OTSelector.Reconstruction.BirthNormalizerQuadraticEnergy
import OTSelector.Reconstruction.OriginalFocalResiduePalmEnergy
import OTSelector.Reconstruction.FinslerOriginalClockOccupationPathMoment

/-! The same actual canonical birth-frame mark has its own true-Palm quadratic
energy bound. No momentum independence or extra original moment premise enters. -/
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

/-- The actual left birth-normalized momentum second moment retains the
same band's focal energy and full original momentum energy. -/
theorem OriginalSeedConditionalMoments.original_left_birthNormalizer_quadraticMoment_le
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hB : MeasurableSet B)
    (ha : ∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t)) :
    (∫⁻ m in B, ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
        originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
    ENNReal.ofReal (s * (finrank ℝ S.covector.ker : ℝ)) *
      (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
    ENNReal.ofReal (2 * s / t) *
      (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  have hv : Measurable (fun m ↦ ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)) :=
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2).ennreal_ofReal
  have he : Measurable (fun m ↦ ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)) :=
    (measurable_originalSeedLeftPoleEnergy hF hw D.lo G).ennreal_ofReal
  rw [← lintegral_const_mul _ hv, ← lintegral_const_mul _ he,
    ← lintegral_add_left (hv.const_mul _)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hB] with m hm
  have hb := birthNormalizer_momentum_sq_le_source_energy hG ht hs
    (ht.trans_le (ha m hm).1) (ha m hm).2 (originalSeedPairMomentum S w m)
  have hb' : ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
        originalSeedPairMomentum S w m‖ ^ 2 ≤
      (s * (finrank ℝ S.covector.ker : ℝ)) * ‖originalSeedPairMomentum S w m‖ ^ 2 +
        (2 * s / t) * originalSeedLeftPoleEnergy S w D.lo G m := by
    simpa only [Fintype.card_fin, originalSeedLeftPoleEnergy, originalSeedRightPoleEnergy] using hb
  exact (ENNReal.ofReal_le_ofReal hb').trans (ENNReal.ofReal_add_le.trans_eq
    (by rw [ENNReal.ofReal_mul (show 0 ≤ s * (finrank ℝ S.covector.ker : ℝ) by positivity),
      ENNReal.ofReal_mul (show 0 ≤ 2 * s / t by positivity)]))

/-- The actual right birth-normalized momentum second moment retains the
same band's focal energy and full original momentum energy. -/
theorem OriginalSeedConditionalMoments.original_right_birthNormalizer_quadraticMoment_le
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hB : MeasurableSet B)
    (ha : ∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t)) :
    (∫⁻ m in B, ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
        originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
    ENNReal.ofReal (s * (finrank ℝ S.covector.ker : ℝ)) *
      (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
    ENNReal.ofReal (2 * s / t) *
      (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  have hv : Measurable (fun m ↦ ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)) :=
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2).ennreal_ofReal
  have he : Measurable (fun m ↦ ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)) :=
    (measurable_originalSeedRightPoleEnergy hF hw D.hi G).ennreal_ofReal
  rw [← lintegral_const_mul _ hv, ← lintegral_const_mul _ he,
    ← lintegral_add_left (hv.const_mul _)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hB] with m hm
  have hb := birthNormalizer_momentum_sq_le_source_energy hG ht hs
    (ht.trans_le (ha m hm).1) (ha m hm).2 (originalSeedPairMomentum S w m)
  have hb' : ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
        originalSeedPairMomentum S w m‖ ^ 2 ≤
      (s * (finrank ℝ S.covector.ker : ℝ)) * ‖originalSeedPairMomentum S w m‖ ^ 2 +
        (2 * s / t) * originalSeedRightPoleEnergy S w D.hi G m := by
    simpa only [Fintype.card_fin, originalSeedLeftPoleEnergy, originalSeedRightPoleEnergy] using hb
  exact (ENNReal.ofReal_le_ofReal hb').trans (ENNReal.ofReal_add_le.trans_eq
    (by rw [ENNReal.ofReal_mul (show 0 ≤ s * (finrank ℝ S.covector.ker : ℝ) by positivity),
      ENNReal.ofReal_mul (show 0 ≤ 2 * s / t by positivity)]))

/-- Every deterministic actual normalized full-momentum square is integrable
under the unchanged true Palm law, using only the original kinetic moment. -/
theorem OriginalSeedConditionalMoments.integrable_original_normalizedMomentum_sq
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ) :
    Integrable (fun m ↦ ‖T *ᵥ originalSeedPairMomentum S w m‖ ^ 2)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  have hP := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have hm : Measurable (fun m ↦ T *ᵥ originalSeedPairMomentum S w m) :=
    (Matrix.toLin' T).continuous_of_finiteDimensional.measurable.comp
      (measurable_originalSeedPairMomentum S hF hw)
  apply (hP.const_mul (‖T‖ ^ 2)).mono' (hm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with m
  change |‖T *ᵥ originalSeedPairMomentum S w m‖ ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (‖T‖ * ‖originalSeedPairMomentum S w m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (Matrix.linfty_opNorm_mulVec _ _) 2
    _ = _ := mul_pow _ _ _

end OTSelector.Reconstruction
