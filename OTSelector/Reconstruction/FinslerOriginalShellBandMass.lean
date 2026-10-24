import OTSelector.Reconstruction.FinslerOriginalDensityResidueRate
import OTSelector.MeasureTheory.EndpointDensityShellBand
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
/-- Every narrow original left clock band has the density-rank shell estimate. -/
theorem OriginalSeedConditionalMoments.exists_original_left_shell_band_mass_bound
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
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
      ∀ {t a b s : ℝ}, 0 < t → 2 * t < ε → D.lo + t ≤ a → b ≤ D.lo + 2 * t →
        b - a ≤ s → (σ.map (fun x : ℝ ↦ x - S.level)) (Ioc a b) ≤
          ENNReal.ofReal (C * t ^ G.rank * s) := by
  obtain ⟨_, h, ε, K, _, hh, hε, hεh, hK, hlaw, hbound⟩ :=
    D.exists_original_left_density_residue_rate hF hw c hρ hρ0 hv hv0 hdensity hη hRem hpole
  refine ⟨ε, (2 : ℝ) ^ G.rank * K, hε, by linarith, by positivity, ?_⟩
  intro t a b s ht h2t ha hb hwidth
  exact measure_Ioc_left_shell_le_of_density_power_bound hlaw hεh hK.le
    (fun r hr ↦ (hbound r hr).2) ht h2t ha hb hwidth

omit [BorelSpace E] in
/-- Every narrow original right clock band has the same-residue shell estimate. -/
theorem OriginalSeedConditionalMoments.exists_original_right_shell_band_mass_bound
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
      ∀ {t a b s : ℝ}, 0 < t → 2 * t < ε → D.hi - 2 * t ≤ a → b ≤ D.hi - t →
        b - a ≤ s → (σ.map (fun x : ℝ ↦ x - S.level)) (Ioc a b) ≤
          ENNReal.ofReal (C * t ^ G.rank * s) := by
  obtain ⟨_, l, ε, K, hl, _, hε, hεh, hK, hlaw, hbound⟩ :=
    D.exists_original_right_density_residue_rate hF hw c hρ hρ0 hv hv0 hdensity hη hRem hpole
  refine ⟨ε, (2 : ℝ) ^ G.rank * K, hε, by linarith, by positivity, ?_⟩
  intro t a b s ht h2t ha hb hwidth
  exact measure_Ioc_right_shell_le_of_density_power_bound hlaw hεh hK.le
    (fun r hr ↦ (hbound r hr).2) ht h2t ha hb hwidth

end OTSelector.Reconstruction
