import OTSelector.Reconstruction.FinslerOriginalDensityResidueRate
import OTSelector.Reconstruction.FinslerOriginalReflectedShellBandMass
import OTSelector.MeasureTheory.ClockReflectedBandMass
import OTSelector.MeasureTheory.DyadicClockBandPartition
import OTSelector.Reconstruction.OriginalFinslerKernelLeftDoublePole
import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole

/-! Original clock-band masses inside focal dyadic shells. The power is the rank
of the same original kernel residue; both absolute and relative clocks are kept. -/
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

omit [BorelSpace E] in
/-- Every narrow original right clock band has the same-residue shell estimate. -/
theorem OriginalSeedConditionalMoments.exists_original_right_inward_dyadicBirthBand_mass_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (σ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
      ∀ {t : ℝ} (j : ℕ), 0 < t → 2 * t < ε →
      ∀ n ∈ Finset.range (dyadicBirthBandCount j),
        (σ.map (fun x : ℝ ↦ D.hi - (x - S.level)))
          (clockGridBand t ((t / (2 : ℝ) ^ j) / 8) n) ≤
            ENNReal.ofReal (C * t ^ G.rank * ((t / (2 : ℝ) ^ j) / 8)) := by
  obtain ⟨ε, C, hε, hεh, hC, hband⟩ :=
    D.exists_original_right_reflected_shell_band_mass_bound hF hw c hρ hρ0 hv hv0 hdensity hη hRem hpole
  refine ⟨ε, C, hε, hεh, hC, fun {t} j ht htε n hn ↦ ?_⟩
  have hwid := dyadicBirthBand_width_and_total ht j
  have hend := clockGridBand_endpoints t hwid.1.le (Finset.mem_range.mp hn)
  have hlo : t ≤ t + (n : ℝ) * (t / (dyadicBirthBandCount j : ℝ)) := hend.1
  have hhi : t + ((n : ℝ) + 1) * (t / (dyadicBirthBandCount j : ℝ)) ≤ 2 * t := by
    have hh := hend.2.1
    rw [hwid.2.2] at hh
    linarith
  have ha : D.hi - 2 * t ≤ D.hi - (t + ((n : ℝ) + 1) * (t / (dyadicBirthBandCount j : ℝ))) := by linarith
  have hb : D.hi - (t + (n : ℝ) * (t / (dyadicBirthBandCount j : ℝ))) ≤ D.hi - t := by linarith
  have hwidth : (D.hi - (t + (n : ℝ) * (t / (dyadicBirthBandCount j : ℝ)))) -
      (D.hi - (t + ((n : ℝ) + 1) * (t / (dyadicBirthBandCount j : ℝ)))) ≤
      t / (dyadicBirthBandCount j : ℝ) := by linarith [hend.2.2]
  have hm := hband ht htε ha hb hwidth
  rw [map_clock_sub_Ico] at hm
  rw [hwid.2.1] at hm
  simpa only [clockGridBand, map_clock_right_inward_Ioc, add_sub_assoc] using hm

end OTSelector.Reconstruction
