import OTSelector.Reconstruction.OriginalSameResiduePalmEnergy
import OTSelector.Reconstruction.OriginalBirthNormalizerQuadraticMoment

/-! The actual canonical quadratic moment is converted to the real same-band
energy budget only after genuine true-Palm finiteness is produced internally. -/
open Set Matrix Module Manifold MeasureTheory
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

/-- The same actual left residue yields the canonical real second moment
bound by its original same-band focal and full-momentum energies. -/
theorem OriginalSeedConditionalMoments.original_left_birthNormalizer_quadraticMoment_toReal_le
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hB : MeasurableSet B)
    (ha : ∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t)) :
    (∫⁻ m in B, ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
      originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal ≤
    (s * (finrank ℝ S.covector.ker : ℝ)) *
      (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
    (2 * s / t) * (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by
  have hIE := (D.original_left_sameResidue_focalEnergy_integrable hF hw hη hηspan
    hG hRem hpole hgap hbounds Q).2.1
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have he : (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIE.2).ne
      (setLIntegral_le_lintegral _ _)
  have hv : (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
      (setLIntegral_le_lintegral _ _)
  have hv' := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := s * (finrank ℝ S.covector.ker : ℝ))) hv
  have he' := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 * s / t)) he
  have hfin := ENNReal.add_ne_top.mpr ⟨hv', he'⟩
  have hr := ENNReal.toReal_mono hfin
    (D.original_left_birthNormalizer_quadraticMoment_le hF hw Q hG ht hs hB ha)
  rw [ENNReal.toReal_add hv' he'] at hr
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ s * (finrank ℝ S.covector.ker : ℝ) by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ 2 * s / t by positivity)] using hr

/-- The same actual right residue yields the canonical real second moment
bound by its original same-band focal and full-momentum energies. -/
theorem OriginalSeedConditionalMoments.original_right_birthNormalizer_quadraticMoment_toReal_le
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hB : MeasurableSet B)
    (ha : ∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t)) :
    (∫⁻ m in B, ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
      originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal ≤
    (s * (finrank ℝ S.covector.ker : ℝ)) *
      (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
    (2 * s / t) * (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by
  have hIE := (D.original_right_sameResidue_focalEnergy_integrable hF hw hη hηspan
    hG hRem hpole hgap hbounds Q).2.1
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have he : (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIE.2).ne
      (setLIntegral_le_lintegral _ _)
  have hv : (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
      (setLIntegral_le_lintegral _ _)
  have hv' := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := s * (finrank ℝ S.covector.ker : ℝ))) hv
  have he' := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 * s / t)) he
  have hfin := ENNReal.add_ne_top.mpr ⟨hv', he'⟩
  have hr := ENNReal.toReal_mono hfin
    (D.original_right_birthNormalizer_quadraticMoment_le hF hw Q hG ht hs hB ha)
  rw [ENNReal.toReal_add hv' he'] at hr
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ s * (finrank ℝ S.covector.ker : ℝ) by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ 2 * s / t by positivity)] using hr

end OTSelector.Reconstruction
