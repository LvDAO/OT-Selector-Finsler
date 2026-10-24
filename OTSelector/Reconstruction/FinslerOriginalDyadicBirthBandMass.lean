import OTSelector.Reconstruction.FinslerOriginalDensityResidueRate
import OTSelector.Reconstruction.FinslerOriginalTwoColorShellBand
import OTSelector.MeasureTheory.DyadicClockBandPartition
import OTSelector.Reconstruction.OriginalFinslerKernelLeftDoublePole
import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole

/-! Actual original two-color dyadic birth bands. The same kernel residue
determines the density power, and every finite band has its true dyadic width. -/
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

/-- Both original colors obey the left shell-width rate for one internally
produced original residue, on a common collar with one finite constant. -/
theorem OriginalSeedConditionalMoments.exists_original_left_twoColor_dyadicBirthBand_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
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
      ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
        ∀ (i : Fin 2) {t : ℝ} (j : ℕ), 0 < t → 2 * t < ε →
          ∀ n ∈ Finset.range (dyadicBirthBandCount j),
            ((σ i).map (fun x : ℝ ↦ x - S.level))
              (clockGridBand (D.lo + t) (t / (dyadicBirthBandCount j : ℝ)) n) ≤
              ENNReal.ofReal (C * t ^ G.rank * ((t / (2 : ℝ) ^ j) / 8)) := by
  obtain ⟨η, hη, hηh, G, Rem, hRem, hpole, ε, C, hε, hεh, hC, hband⟩ :=
    D.exists_original_left_twoColor_shell_band_bound hF hw σ ρ c hρ hρ0 hv hv0 hdensity
  refine ⟨η, hη, hηh, G, Rem, hRem, hpole, ε, C, hε, hεh, hC, ?_⟩
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
  have hmass := hband i ht hwid.1.le h2t ha hb hend.2.2.le
  rw [hwid.2.1] at hmass
  simpa only [clockGridBand, hwid.2.1] using hmass

/-- Both original colors obey the right shell-width rate for one internally
produced original residue, on a common collar with one finite constant. -/
theorem OriginalSeedConditionalMoments.exists_original_right_twoColor_dyadicBirthBand_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
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
      ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
        ∀ (i : Fin 2) {t : ℝ} (j : ℕ), 0 < t → 2 * t < ε →
          ∀ n ∈ Finset.range (dyadicBirthBandCount j),
            ((σ i).map (fun x : ℝ ↦ x - S.level))
              (clockGridBand (D.hi - 2 * t) (t / (dyadicBirthBandCount j : ℝ)) n) ≤
              ENNReal.ofReal (C * t ^ G.rank * ((t / (2 : ℝ) ^ j) / 8)) := by
  obtain ⟨η, hη, hηh, G, Rem, hRem, hpole, ε, C, hε, hεh, hC, hband⟩ :=
    D.exists_original_right_twoColor_shell_band_bound hF hw σ ρ c hρ hρ0 hv hv0 hdensity
  refine ⟨η, hη, hηh, G, Rem, hRem, hpole, ε, C, hε, hεh, hC, ?_⟩
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
  have hmass := hband i ht hwid.1.le h2t ha hb hend.2.2.le
  rw [hwid.2.1] at hmass
  simpa only [clockGridBand, hwid.2.1] using hmass

end OTSelector.Reconstruction
