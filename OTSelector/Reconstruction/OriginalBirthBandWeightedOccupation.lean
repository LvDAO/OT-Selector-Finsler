import OTSelector.Reconstruction.OriginalBirthMomentumVelocityProduct
import OTSelector.MeasureTheory.Integral.MaskedProductBound

/-! The actual original birth-band Campbell momentum integral has its quantitative
same-residue energy bound. Mark and clock restrictions retain all correlations. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The same original left masked Campbell bound holds for all strictly
positive focal endpoint distances, keeping the literal clock window. -/
theorem OriginalSeedConditionalMoments.exists_original_left_focalBand_weightedOccupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {gap : ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g),
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Ioc 0 (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal (C * Real.sqrt s) *
        (ENNReal.ofReal ((t ^ 2)⁻¹) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ENNReal.ofReal t⁻¹ *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
  obtain ⟨ε, C, hε, hεη, hC, hproduct⟩ :=
    D.exists_original_left_focalMomentum_occupation_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap g} Q {t s} ht ht1 hs htε {B} hB ha {I} hI hc mask hm hz ↦ ?_⟩
  apply lintegral_masked_band_product_le
    (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) volume hB hI
    (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
        originalSeedPairMomentum S w z.1‖ *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z))
    (measurable_originalSeedLeftPoleEnergy hF hw D.lo G).ennreal_ofReal
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2).ennreal_ofReal
    (ENNReal.ofReal (C * Real.sqrt s)) (ENNReal.ofReal ((t ^ 2)⁻¹)) (ENNReal.ofReal t⁻¹)
  · intro m hmb c hci
    have ha0 : 0 < m.1.1 - (S.level : ℝ) - D.lo := (ha m hmb).1
    have he : 0 ≤ originalSeedLeftPoleEnergy S w D.lo G m :=
      div_nonneg (by simpa only [star_trivial] using
        hG.dotProduct_mulVec_nonneg (originalSeedPairMomentum S w m)) ha0.le
    have hp := hproduct ht ht1 hs htε m (ha m hmb) c (hc c hci)
    calc
      _ ≤ ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * 1) :=
        mul_le_mul_right (mul_le_mul_right (hm (m, c)) _) _
      _ = ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖) := by
        rw [mul_one, ← ENNReal.ofReal_mul (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (C * Real.sqrt s *
          (originalSeedLeftPoleEnergy S w D.lo G m / t ^ 2 + ‖originalSeedPairMomentum S w m‖ ^ 2 / t)) :=
        ENNReal.ofReal_le_ofReal hp
      _ = _ := by
        rw [show originalSeedLeftPoleEnergy S w D.lo G m / t ^ 2 + ‖originalSeedPairMomentum S w m‖ ^ 2 / t =
          (t ^ 2)⁻¹ * originalSeedLeftPoleEnergy S w D.lo G m + t⁻¹ * ‖originalSeedPairMomentum S w m‖ ^ 2 by ring]
        rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Real.sqrt_nonneg _)),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  · intro m c hzero
    simp only [hz m c hzero, mul_zero]

/-- On an actual left birth band, Campbell's normalized-momentum occupation
integral is bounded by `sqrt s` times the original band energy `e/t² + v/t`.
The same deterministic physical window contributes its exact Haar length. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birthBand_weightedOccupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {gap : ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g),
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal (C * Real.sqrt s) *
        (ENNReal.ofReal ((t ^ 2)⁻¹) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ENNReal.ofReal t⁻¹ *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_left_focalBand_weightedOccupation_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro gap g Q t s ht ht1 hs htε B hB ha I hI hc mask hm hz
  exact hbound Q ht ht1 hs htε hB
    (fun m hm ↦ ⟨ht.trans_le (ha m hm).1, (ha m hm).2⟩) hI hc mask hm hz

/-- The same original right masked Campbell bound holds for all strictly
positive focal endpoint distances, keeping the literal clock window. -/
theorem OriginalSeedConditionalMoments.exists_original_right_focalBand_weightedOccupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {gap : ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g),
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Ioc 0 (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal (C * Real.sqrt s) *
        (ENNReal.ofReal ((t ^ 2)⁻¹) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ENNReal.ofReal t⁻¹ *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
  obtain ⟨ε, C, hε, hεη, hC, hproduct⟩ :=
    D.exists_original_right_focalMomentum_occupation_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap g} Q {t s} ht ht1 hs htε {B} hB ha {I} hI hc mask hm hz ↦ ?_⟩
  apply lintegral_masked_band_product_le
    (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) volume hB hI
    (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
        originalSeedPairMomentum S w z.1‖ *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z))
    (measurable_originalSeedRightPoleEnergy hF hw D.hi G).ennreal_ofReal
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2).ennreal_ofReal
    (ENNReal.ofReal (C * Real.sqrt s)) (ENNReal.ofReal ((t ^ 2)⁻¹)) (ENNReal.ofReal t⁻¹)
  · intro m hmb c hci
    have ha0 : 0 < D.hi - (m.1.2 - (S.level : ℝ)) := (ha m hmb).1
    have he : 0 ≤ originalSeedRightPoleEnergy S w D.hi G m :=
      div_nonneg (by simpa only [star_trivial] using
        hG.dotProduct_mulVec_nonneg (originalSeedPairMomentum S w m)) ha0.le
    have hp := hproduct ht ht1 hs htε m (ha m hmb) c (hc c hci)
    calc
      _ ≤ ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * 1) :=
        mul_le_mul_right (mul_le_mul_right (hm (m, c)) _) _
      _ = ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖) := by
        rw [mul_one, ← ENNReal.ofReal_mul (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (C * Real.sqrt s *
          (originalSeedRightPoleEnergy S w D.hi G m / t ^ 2 + ‖originalSeedPairMomentum S w m‖ ^ 2 / t)) :=
        ENNReal.ofReal_le_ofReal hp
      _ = _ := by
        rw [show originalSeedRightPoleEnergy S w D.hi G m / t ^ 2 + ‖originalSeedPairMomentum S w m‖ ^ 2 / t =
          (t ^ 2)⁻¹ * originalSeedRightPoleEnergy S w D.hi G m + t⁻¹ * ‖originalSeedPairMomentum S w m‖ ^ 2 by ring]
        rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Real.sqrt_nonneg _)),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  · intro m c hzero
    simp only [hz m c hzero, mul_zero]

/-- On an actual right birth band, Campbell's normalized-momentum occupation
integral is bounded by `sqrt s` times the original band energy `e/t² + v/t`.
The same deterministic physical window contributes its exact Haar length. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthBand_weightedOccupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {gap : ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g),
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal (C * Real.sqrt s) *
        (ENNReal.ofReal ((t ^ 2)⁻¹) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ENNReal.ofReal t⁻¹ *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_right_focalBand_weightedOccupation_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro gap g Q t s ht ht1 hs htε B hB ha I hI hc mask hm hz
  exact hbound Q ht ht1 hs htε hB
    (fun m hm ↦ ⟨ht.trans_le (ha m hm).1, (ha m hm).2⟩) hI hc mask hm hz
end OTSelector.Reconstruction
