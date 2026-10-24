import OTSelector.Reconstruction.FinslerOriginalDensityResidueRate
import OTSelector.Reconstruction.FinslerOriginalShellBandMass
import OTSelector.Reconstruction.OriginalFocalResiduePalmEnergy
import OTSelector.MeasureTheory.DyadicClockBandPartition
import OTSelector.Reconstruction.OriginalFinslerKernelLeftDoublePole
import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole

/-! One actual original residue simultaneously controls true-Palm focal energy
and both unchanged physical clock densities on every dyadic birth band. -/
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
  {w : S.covector.ker} {μ ν σ : Measure ℝ}

/-- The left focal energy moment and both dyadic clock-band masses use
one and the same internally produced original residue; no extra energy moment
or density exponent is supplied. -/
theorem OriginalSeedConditionalMoments.exists_original_left_coherent_focalEnergy_birthBands
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (σ : Fin 2 → Measure ℝ) (ρ : Fin 2 → M → ℝ) {v : M → E → ℝ}
    (c : Fin 2 → ℝ≥0∞)
    (hρ : ∀ i, Continuous (ρ i)) (hρ0 : ∀ i x, 0 ≤ ρ i x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : ∀ i, PopulationSeedClockDensity S w
      ((σ i).map (fun x : ℝ ↦ x - S.level)) (ρ i) v (c i).toReal) :
    ∃ η : ℝ, 0 < η ∧ η < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      (∃ Ce : ℝ, 0 < Ce ∧ Integrable (originalSeedLeftPoleEnergy S w D.lo G)
          (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
        (∫ m, originalSeedLeftPoleEnergy S w D.lo G m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
          Ce * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
        ∀ (i : Fin 2) {t : ℝ} (j : ℕ), 0 < t → 2 * t < ε →
          ∀ n ∈ Finset.range (dyadicBirthBandCount j),
            ((σ i).map (fun x : ℝ ↦ x - S.level))
              (clockGridBand (D.lo + t) (t / (dyadicBirthBandCount j : ℝ)) n) ≤
              ENNReal.ofReal (C * t ^ G.rank * ((t / (2 : ℝ) ^ j) / 8)) := by
  obtain ⟨η, hη, hηh, G, Rem, hG, hRem, hpole, Ce, hCe, _, _, heI, heMean⟩ :=
    D.exists_original_left_pole_and_focalEnergy_integrable hF hw hgap hbounds Q
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hη, hη⟩)
  have heach (i : Fin 2) := D.exists_original_left_shell_band_mass_bound
    hF hw (c i) (hρ i) (hρ0 i) hv hv0 (hdensity i) hη hRem0 hpole
  choose ε C hε hεh hC hband using heach
  have hεmin (i : Fin 2) : min (ε 0) (ε 1) ≤ ε i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hCmax (i : Fin 2) : C i ≤ max (C 0) (C 1) := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨η, hη, hηh, G, Rem, hG, hRem, hpole, ⟨Ce, hCe, heI, heMean⟩,
    min (ε 0) (ε 1), max (C 0) (C 1), lt_min (hε 0) (hε 1),
    (min_le_left _ _).trans_lt (hεh 0), (hC 0).trans_le (le_max_left _ _), ?_⟩
  intro i t j ht h2t n hn
  have hwid := dyadicBirthBand_width_and_total ht j
  have hend := clockGridBand_endpoints (D.lo + t) hwid.1.le (Finset.mem_range.mp hn)
  have ha : D.lo + t ≤
      (D.lo + t) + (n : ℝ) * (t / (dyadicBirthBandCount j : ℝ)) := hend.1
  have hb : (D.lo + t) + ((n : ℝ) + 1) * (t / (dyadicBirthBandCount j : ℝ)) ≤
      D.lo + 2 * t := by
    have hh := hend.2.1
    rw [hwid.2.2] at hh
    linarith
  have hmass := hband i ht (h2t.trans_le (hεmin i)) ha hb hend.2.2.le
  have hscale : C i * t ^ G.rank * (t / (dyadicBirthBandCount j : ℝ)) ≤
      max (C 0) (C 1) * t ^ G.rank * (t / (dyadicBirthBandCount j : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCmax i) (pow_nonneg ht.le _)) hwid.1.le
  have hmass' := hmass.trans (ENNReal.ofReal_le_ofReal hscale)
  rw [hwid.2.1] at hmass'
  simpa only [clockGridBand, hwid.2.1] using hmass'

/-- The right focal energy moment and both dyadic clock-band masses use
one and the same internally produced original residue; no extra energy moment
or density exponent is supplied. -/
theorem OriginalSeedConditionalMoments.exists_original_right_coherent_focalEnergy_birthBands
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (σ : Fin 2 → Measure ℝ) (ρ : Fin 2 → M → ℝ) {v : M → E → ℝ}
    (c : Fin 2 → ℝ≥0∞)
    (hρ : ∀ i, Continuous (ρ i)) (hρ0 : ∀ i x, 0 ≤ ρ i x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : ∀ i, PopulationSeedClockDensity S w
      ((σ i).map (fun x : ℝ ↦ x - S.level)) (ρ i) v (c i).toReal) :
    ∃ η : ℝ, 0 < η ∧ η < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      (∃ Ce : ℝ, 0 < Ce ∧ Integrable (originalSeedRightPoleEnergy S w D.hi G)
          (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
        (∫ m, originalSeedRightPoleEnergy S w D.hi G m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
          Ce * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
        ∀ (i : Fin 2) {t : ℝ} (j : ℕ), 0 < t → 2 * t < ε →
          ∀ n ∈ Finset.range (dyadicBirthBandCount j),
            ((σ i).map (fun x : ℝ ↦ x - S.level))
              (clockGridBand (D.hi - 2 * t) (t / (dyadicBirthBandCount j : ℝ)) n) ≤
              ENNReal.ofReal (C * t ^ G.rank * ((t / (2 : ℝ) ^ j) / 8)) := by
  obtain ⟨η, hη, hηh, G, Rem, hG, hRem, hpole, Ce, hCe, _, _, heI, heMean⟩ :=
    D.exists_original_right_pole_and_focalEnergy_integrable hF hw hgap hbounds Q
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hη, hη⟩)
  have heach (i : Fin 2) := D.exists_original_right_shell_band_mass_bound
    hF hw (c i) (hρ i) (hρ0 i) hv hv0 (hdensity i) hη hRem0 hpole
  choose ε C hε hεh hC hband using heach
  have hεmin (i : Fin 2) : min (ε 0) (ε 1) ≤ ε i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hCmax (i : Fin 2) : C i ≤ max (C 0) (C 1) := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨η, hη, hηh, G, Rem, hG, hRem, hpole, ⟨Ce, hCe, heI, heMean⟩,
    min (ε 0) (ε 1), max (C 0) (C 1), lt_min (hε 0) (hε 1),
    (min_le_left _ _).trans_lt (hεh 0), (hC 0).trans_le (le_max_left _ _), ?_⟩
  intro i t j ht h2t n hn
  have hwid := dyadicBirthBand_width_and_total ht j
  have hend := clockGridBand_endpoints (D.hi - 2 * t) hwid.1.le (Finset.mem_range.mp hn)
  have ha : D.hi - 2 * t ≤
      (D.hi - 2 * t) + (n : ℝ) * (t / (dyadicBirthBandCount j : ℝ)) := hend.1
  have hb : (D.hi - 2 * t) + ((n : ℝ) + 1) * (t / (dyadicBirthBandCount j : ℝ)) ≤
      D.hi - t := by
    have hh := hend.2.1
    rw [hwid.2.2] at hh
    linarith
  have hmass := hband i ht (h2t.trans_le (hεmin i)) ha hb hend.2.2.le
  have hscale : C i * t ^ G.rank * (t / (dyadicBirthBandCount j : ℝ)) ≤
      max (C 0) (C 1) * t ^ G.rank * (t / (dyadicBirthBandCount j : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCmax i) (pow_nonneg ht.le _)) hwid.1.le
  have hmass' := hmass.trans (ENNReal.ofReal_le_ofReal hscale)
  rw [hwid.2.1] at hmass'
  simpa only [clockGridBand, hwid.2.1] using hmass'

end OTSelector.Reconstruction
