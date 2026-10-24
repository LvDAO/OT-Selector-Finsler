import OTSelector.Reconstruction.OriginalBirthBandFirstOccupationMoment
import OTSelector.Reconstruction.OriginalPalmClockBandMass
import OTSelector.Reconstruction.BirthSmallFirstMomentScale

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

/-- The actual left small-phase first moment has its precise birth-shell
energy powers, using the original clock marginal to bound the same Palm band. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birthBand_smallFirstMoment_bound
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
      ∀ {t s : ℝ}, 0 < t → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t)) →
      ∀ {A K : ℝ}, 0 ≤ A → 0 ≤ K → volume I ≤ ENNReal.ofReal (A * s) →
      ∀ {J : Set ℝ}, MeasurableSet J →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) ∈ J) →
      (μ.map (fun a : ℝ ↦ a - (S.level : ℝ))) J ≤ ENNReal.ofReal (K * t ^ G.rank * s) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      ENNReal.ofReal (A * C * Real.sqrt K) *
        (ENNReal.ofReal (s ^ (3 / 2 : ℝ) * t ^ (((G.rank : ℝ) - 3) / 2)) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (s ^ (3 / 2 : ℝ) * t ^ ((G.rank : ℝ) / 2)) *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ)) := by
  obtain ⟨ε, C, hε, hεη, hC, hfirst⟩ :=
    D.exists_original_left_birthBand_firstOccupationMoment_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap g} Q {t s} ht hs htε {B} hB ha
    {I} hI hc {A K} hA hK hlen {J} hJ hBJ hmass mask hm hz ↦ ?_⟩
  have hPalmMass := (Q.palm_sourceClockBand_mass_le (S.level : ℝ) hJ hBJ).trans hmass
  exact smallBirth_firstMoment_le_of_band_window_bounds ht hs hA hC.le hK hlen hPalmMass
    (hfirst Q ht htε hB ha hI hc mask hm hz)

/-- The actual right small-phase first moment has its precise birth-shell
energy powers, using the original clock marginal to bound the same Palm band. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthBand_smallFirstMoment_bound
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
      ∀ {t s : ℝ}, 0 < t → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I → (∀ c ∈ I, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t)) →
      ∀ {A K : ℝ}, 0 ≤ A → 0 ≤ K → volume I ≤ ENNReal.ofReal (A * s) →
      ∀ {J : Set ℝ}, MeasurableSet J →
      (∀ m ∈ B, m.1.2 - (S.level : ℝ) ∈ J) →
      (ν.map (fun a : ℝ ↦ a - (S.level : ℝ))) J ≤ ENNReal.ofReal (K * t ^ G.rank * s) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      ENNReal.ofReal (A * C * Real.sqrt K) *
        (ENNReal.ofReal (s ^ (3 / 2 : ℝ) * t ^ (((G.rank : ℝ) - 3) / 2)) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (s ^ (3 / 2 : ℝ) * t ^ ((G.rank : ℝ) / 2)) *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ (1 / 2 : ℝ)) := by
  obtain ⟨ε, C, hε, hεη, hC, hfirst⟩ :=
    D.exists_original_right_birthBand_firstOccupationMoment_bound hF hw hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap g} Q {t s} ht hs htε {B} hB ha
    {I} hI hc {A K} hA hK hlen {J} hJ hBJ hmass mask hm hz ↦ ?_⟩
  have hPalmMass := (Q.palm_targetClockBand_mass_le (S.level : ℝ) hJ hBJ).trans hmass
  exact smallBirth_firstMoment_le_of_band_window_bounds ht hs hA hC.le hK hlen hPalmMass
    (hfirst Q ht htε hB ha hI hc mask hm hz)

end OTSelector.Reconstruction
