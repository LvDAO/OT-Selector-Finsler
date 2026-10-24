import OTSelector.Reconstruction.FinslerOriginalDensityResidueRate
import OTSelector.MeasureTheory.EndpointDensityPowerMass
import OTSelector.Reconstruction.OriginalFinslerKernelLeftDoublePole
import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole

/-! Original endpoint birth mass is controlled by the rank of the actual
original kernel residue. Both the pole and the mass rate are produced internally. -/
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
/-- For either original color, the left endpoint mass has exponent one plus
the rank of the given actual original double-pole residue. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birth_mass_bound
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
    ∃ ε K : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
      (σ.map (fun x : ℝ ↦ x - S.level)) (Ioo D.lo (D.lo + r)) ≤
        ENNReal.ofReal (K * r ^ (G.rank + 1)) := by
  obtain ⟨_, h, ε, K, _, hh, hε, hεh, hK, hlaw, hbound⟩ :=
    D.exists_original_left_density_residue_rate hF hw c hρ hρ0 hv hv0 hdensity hη hRem hpole
  refine ⟨ε, K, hε, by linarith, hK, ?_⟩
  intro r hr
  exact measure_left_endpoint_le_of_density_power_bound hlaw hεh hK.le
    (fun s hs ↦ (hbound s hs).2) hr

omit [BorelSpace E] in
/-- The corresponding right endpoint bound uses the rank of its same actual residue. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birth_mass_bound
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
    ∃ ε K : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
      (σ.map (fun x : ℝ ↦ x - S.level)) (Ioo (D.hi - r) D.hi) ≤
        ENNReal.ofReal (K * r ^ (G.rank + 1)) := by
  obtain ⟨_, l, ε, K, hl, _, hε, hεh, hK, hlaw, hbound⟩ :=
    D.exists_original_right_density_residue_rate hF hw c hρ hρ0 hv hv0 hdensity hη hRem hpole
  refine ⟨ε, K, hε, by linarith, hK, ?_⟩
  intro r hr
  exact measure_right_endpoint_le_of_density_power_bound hlaw hεh hK.le
    (fun s hs ↦ (hbound s hs).2) hr

/-- The actual original kernel and physical density produce their left pole and
matching birth rate, without a pole, rank or rate hypothesis. -/
theorem OriginalSeedConditionalMoments.exists_original_left_pole_and_birth_rate
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (σ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal) :
    ∃ η : ℝ, 0 < η ∧ η < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ ε K : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
        (σ.map (fun x : ℝ ↦ x - S.level)) (Ioo D.lo (D.lo + r)) ≤
          ENNReal.ofReal (K * r ^ (G.rank + 1)) := by
  obtain ⟨η, hη, hηh, G, Rem, hRem, hpole⟩ := D.exists_original_kernel_left_double_pole hF hw
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hη, hη⟩)
  exact ⟨η, hη, hηh, G, Rem, hRem, hpole,
    D.exists_original_left_birth_mass_bound hF hw c hρ hρ0 hv hv0 hdensity hη hRem0 hpole⟩

/-- Both the right pole and its actual original physical birth rate are produced
from the same original comparison and physical population density. -/
theorem OriginalSeedConditionalMoments.exists_original_right_pole_and_birth_rate
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (σ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal) :
    ∃ η : ℝ, 0 < η ∧ η < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ ε K : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
        (σ.map (fun x : ℝ ↦ x - S.level)) (Ioo (D.hi - r) D.hi) ≤
          ENNReal.ofReal (K * r ^ (G.rank + 1)) := by
  obtain ⟨η, hη, hηh, G, Rem, hRem, hpole⟩ := D.exists_original_kernel_right_double_pole hF hw
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hη, hη⟩)
  exact ⟨η, hη, hηh, G, Rem, hRem, hpole,
    D.exists_original_right_birth_mass_bound hF hw c hρ hρ0 hv hv0 hdensity hη hRem0 hpole⟩

end OTSelector.Reconstruction
