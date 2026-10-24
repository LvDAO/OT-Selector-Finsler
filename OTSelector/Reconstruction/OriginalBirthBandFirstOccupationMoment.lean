import OTSelector.Reconstruction.OriginalBirthMomentumVelocityProduct
import OTSelector.MeasureTheory.Integral.MaskedProductBound
import OTSelector.MeasureTheory.Integral.BandSquareRootMoment

/-! The true original birth-band first occupation moment is controlled by the
same band's focal/full energies and exact original mass, retaining correlations. -/
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

/-- The same original left first occupation moment holds throughout the
positive focal endpoint region, under the unchanged actual Palm law. -/
theorem OriginalSeedConditionalMoments.exists_original_left_focalBand_firstOccupationMoment_bound
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
      ∀ {t : ℝ}, 0 < t → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Ioc 0 (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ) +
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ)) := by
  obtain ⟨L, hL, hGn⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hRn⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  let C : ℝ := L * Real.sqrt 2 + M₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min η δ, C, lt_min hη hδ, min_le_left _ _, hC,
    fun {gap g} Q {t} ht htε {B} hB ha {I} hI hc mask hm hz ↦ ?_⟩
  have hraw : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
      ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
          (∫⁻ m in B, ENNReal.ofReal (Real.sqrt (originalSeedLeftPoleEnergy S w D.lo G m))
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
          1 * (∫⁻ m in B, ENNReal.ofReal ‖originalSeedPairMomentum S w m‖
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
    apply lintegral_masked_band_product_le
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) volume hB hI
      (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z)
      (measurable_originalSeedLeftPoleEnergy hF hw D.lo G).sqrt.ennreal_ofReal
      (measurable_originalSeedPairMomentum S hF hw).norm.ennreal_ofReal
      (ENNReal.ofReal C) (ENNReal.ofReal (t ^ (-3 / 2 : ℝ))) 1
    · intro m hmb c hci
      let r : ℝ := c - (S.level : ℝ) - D.lo
      have hr0 : 0 < r := ht.trans_le (hc c hci).1
      have hrη : r < η := ((hc c hci).2.trans_lt htε).trans_le (min_le_left _ _)
      have hrδ : r < δ := ((hc c hci).2.trans_lt htε).trans_le (min_le_right _ _)
      have hvel : ‖originalSeedClockOccupation S w c m‖ ≤ C *
          (t ^ (-3 / 2 : ℝ) * Real.sqrt (originalSeedLeftPoleEnergy S w D.lo G m) +
            ‖originalSeedPairMomentum S w m‖) := by
        apply (norm_originalSeedClockOccupation_le_velocity S w m c).trans
        have hc_eq : c - (S.level : ℝ) = D.lo + r := by dsimp [r]; ring
        rw [hc_eq, hpole r ⟨hr0, hrη⟩]
        exact pole_velocity_le_source_energy_scale hG hL.le hM.le ht (hc c hci).1
          (ha m hmb).1 (ha m hmb).2 hGn (hRn r ⟨hr0, hrδ⟩)
          (originalSeedPairMomentum S w m)
      calc
        _ ≤ ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * 1 :=
          mul_le_mul_right (hm (m, c)) _
        _ ≤ ENNReal.ofReal (C * (t ^ (-3 / 2 : ℝ) *
            Real.sqrt (originalSeedLeftPoleEnergy S w D.lo G m) + ‖originalSeedPairMomentum S w m‖)) := by
          rw [mul_one]; exact ENNReal.ofReal_le_ofReal hvel
        _ = _ := by
          rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_add (by positivity) (norm_nonneg _),
            ENNReal.ofReal_mul (by positivity), one_mul]
    · intro m c hzero
      simp only [hz m c hzero, mul_zero]
  simp only [one_mul] at hraw
  have hroot := setLIntegral_sqrt_le_sqrt_energy_mul_sqrt_mass
    (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) B
    (measurable_originalSeedLeftPoleEnergy hF hw D.lo G)
  have hp := setLIntegral_sqrt_le_sqrt_energy_mul_sqrt_mass
    (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) B
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2)
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hp
  apply hraw.trans
  exact mul_le_mul_right
    (add_le_add (by simpa only [mul_assoc] using
      mul_le_mul_right hroot (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)))) hp) _

/-- The actual left birth band's small-phase first occupation estimate
uses Cauchy-Schwarz under its unchanged true Palm law, without independence. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birthBand_firstOccupationMoment_bound
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
      ∀ {t : ℝ}, 0 < t → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ) +
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ)) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_left_focalBand_firstOccupationMoment_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro gap g Q t ht htε B hB ha I hI hc mask hm hz
  exact hbound Q ht htε hB
    (fun m hm ↦ ⟨ht.trans_le (ha m hm).1, (ha m hm).2⟩) hI hc mask hm hz

/-- The same original right first occupation moment holds throughout the
positive focal endpoint region, under the unchanged actual Palm law. -/
theorem OriginalSeedConditionalMoments.exists_original_right_focalBand_firstOccupationMoment_bound
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
      ∀ {t : ℝ}, 0 < t → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Ioc 0 (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ) +
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ)) := by
  obtain ⟨L, hL, hGn⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hRn⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  let C : ℝ := L * Real.sqrt 2 + M₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min η δ, C, lt_min hη hδ, min_le_left _ _, hC,
    fun {gap g} Q {t} ht htε {B} hB ha {I} hI hc mask hm hz ↦ ?_⟩
  have hraw : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
      ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
          (∫⁻ m in B, ENNReal.ofReal (Real.sqrt (originalSeedRightPoleEnergy S w D.hi G m))
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
          1 * (∫⁻ m in B, ENNReal.ofReal ‖originalSeedPairMomentum S w m‖
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
    apply lintegral_masked_band_product_le
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) volume hB hI
      (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z)
      (measurable_originalSeedRightPoleEnergy hF hw D.hi G).sqrt.ennreal_ofReal
      (measurable_originalSeedPairMomentum S hF hw).norm.ennreal_ofReal
      (ENNReal.ofReal C) (ENNReal.ofReal (t ^ (-3 / 2 : ℝ))) 1
    · intro m hmb c hci
      let r : ℝ := D.hi - (c - (S.level : ℝ))
      have hr0 : 0 < r := ht.trans_le (hc c hci).1
      have hrη : r < η := ((hc c hci).2.trans_lt htε).trans_le (min_le_left _ _)
      have hrδ : r < δ := ((hc c hci).2.trans_lt htε).trans_le (min_le_right _ _)
      have hvel : ‖originalSeedClockOccupation S w c m‖ ≤ C *
          (t ^ (-3 / 2 : ℝ) * Real.sqrt (originalSeedRightPoleEnergy S w D.hi G m) +
            ‖originalSeedPairMomentum S w m‖) := by
        apply (norm_originalSeedClockOccupation_le_velocity S w m c).trans
        have hc_eq : c - (S.level : ℝ) = D.hi - r := by dsimp [r]; ring
        rw [hc_eq, hpole r ⟨hr0, hrη⟩]
        exact pole_velocity_le_source_energy_scale hG hL.le hM.le ht (hc c hci).1
          (ha m hmb).1 (ha m hmb).2 hGn (hRn r ⟨hr0, hrδ⟩)
          (originalSeedPairMomentum S w m)
      calc
        _ ≤ ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * 1 :=
          mul_le_mul_right (hm (m, c)) _
        _ ≤ ENNReal.ofReal (C * (t ^ (-3 / 2 : ℝ) *
            Real.sqrt (originalSeedRightPoleEnergy S w D.hi G m) + ‖originalSeedPairMomentum S w m‖)) := by
          rw [mul_one]; exact ENNReal.ofReal_le_ofReal hvel
        _ = _ := by
          rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_add (by positivity) (norm_nonneg _),
            ENNReal.ofReal_mul (by positivity), one_mul]
    · intro m c hzero
      simp only [hz m c hzero, mul_zero]
  simp only [one_mul] at hraw
  have hroot := setLIntegral_sqrt_le_sqrt_energy_mul_sqrt_mass
    (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) B
    (measurable_originalSeedRightPoleEnergy hF hw D.hi G)
  have hp := setLIntegral_sqrt_le_sqrt_energy_mul_sqrt_mass
    (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) B
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2)
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hp
  apply hraw.trans
  exact mul_le_mul_right
    (add_le_add (by simpa only [mul_assoc] using
      mul_le_mul_right hroot (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)))) hp) _

/-- The actual right birth band's small-phase first occupation estimate
uses Cauchy-Schwarz under its unchanged true Palm law, without independence. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthBand_firstOccupationMoment_bound
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
      ∀ {t : ℝ}, 0 < t → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t)) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      volume I * ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ) +
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) *
            (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law B) ^ (1 / 2 : ℝ)) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_right_focalBand_firstOccupationMoment_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro gap g Q t ht htε B hB ha I hI hc mask hm hz
  exact hbound Q ht htε hB
    (fun m hm ↦ ⟨ht.trans_le (ha m hm).1, (ha m hm).2⟩) hI hc mask hm hz
end OTSelector.Reconstruction
