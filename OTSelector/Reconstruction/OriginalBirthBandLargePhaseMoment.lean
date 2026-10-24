import OTSelector.Reconstruction.OriginalBirthBandWeightedOccupation
import OTSelector.Reconstruction.BirthLargePhaseMomentScale

/-! Actual true-Palm birth-band weighted occupation gives the physical large-phase
energy exponents after the exact coarse scale and physical window length are applied. -/
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

/-- The actual left birth-band large-phase moment has the original physical
`s² t^(-2+1/q)` and `s² t^(-1+1/q)` energy coefficients. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birthBand_largePhaseMoment_bound
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
      ∀ {A : ℝ}, 0 ≤ A → volume I ≤ ENNReal.ofReal (A * s) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      ENNReal.ofReal ((birthTrafficCoarseScale (finrank ℝ S.covector.ker) t s)⁻¹) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      ENNReal.ofReal (A * C) *
        (ENNReal.ofReal (s ^ 2 * t ^ (-2 + 1 / (finrank ℝ S.covector.ker : ℝ))) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ENNReal.ofReal (s ^ 2 * t ^ (-1 + 1 / (finrank ℝ S.covector.ker : ℝ))) *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_left_birthBand_weightedOccupation_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap g} Q {t s} ht ht1 hs htε {B} hB ha
    {I} hI hc {A} hA hlen mask hm hz ↦ ?_⟩
  exact birthLargePhase_moment_le_of_window_bound ht hs hA hC.le hlen
    (hbound Q ht ht1 hs htε hB ha hI hc mask hm hz)

/-- The actual right birth-band large-phase moment has the original physical
`s² t^(-2+1/q)` and `s² t^(-1+1/q)` energy coefficients. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthBand_largePhaseMoment_bound
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
      ∀ {A : ℝ}, 0 ≤ A → volume I ≤ ENNReal.ofReal (A * s) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      ENNReal.ofReal ((birthTrafficCoarseScale (finrank ℝ S.covector.ker) t s)⁻¹) *
      (∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      ENNReal.ofReal (A * C) *
        (ENNReal.ofReal (s ^ 2 * t ^ (-2 + 1 / (finrank ℝ S.covector.ker : ℝ))) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ENNReal.ofReal (s ^ 2 * t ^ (-1 + 1 / (finrank ℝ S.covector.ker : ℝ))) *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_right_birthBand_weightedOccupation_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap g} Q {t s} ht ht1 hs htε {B} hB ha
    {I} hI hc {A} hA hlen mask hm hz ↦ ?_⟩
  exact birthLargePhase_moment_le_of_window_bound ht hs hA hC.le hlen
    (hbound Q ht ht1 hs htε hB ha hI hc mask hm hz)

end OTSelector.Reconstruction
