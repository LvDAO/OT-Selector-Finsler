import OTSelector.Reconstruction.FinslerOriginalEndpointDensityRate
import OTSelector.Reconstruction.EndpointPhysicalKernelResidueRank
import OTSelector.Reconstruction.EndpointPhysicalKernelRightResidueRank
import OTSelector.Reconstruction.OriginalSeedCompliance

/-! The original endpoint density exponent equals the rank of the same actual
original kernel residue. The density frame is retained throughout the argument. -/
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
/-- The unchanged original physical law has left density at most `K r^rank(G)`
for the same double-pole residue `G` used by the original mobility estimates. -/
theorem OriginalSeedConditionalMoments.exists_original_left_density_residue_rate
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
    ∃ (L : SeedEndpointChart S D.comparison D.lo) (h ε K : ℝ),
      D.lo < h ∧ h < D.hi ∧ 0 < ε ∧ ε < h - D.lo ∧ 0 < K ∧
      (σ.map (fun x : ℝ ↦ x - S.level)).restrict (Ioo D.lo h) =
        (volume.restrict (Ioo D.lo h)).withDensity (fun t ↦
          ENNReal.ofReal (c.toReal * populationSeedChartDensity S ρ v L.center w t)) ∧
      ∀ r ∈ Ioo 0 ε,
        0 ≤ c.toReal * populationSeedChartDensity S ρ v L.center w (D.lo + r) ∧
        c.toReal * populationSeedChartDensity S ρ v L.center w (D.lo + r) ≤ K * r ^ G.rank := by
  obtain ⟨L, h, ε, K, hlh, hh, hI, hε, hεh, hK, hlaw, hbound⟩ :=
    D.exists_original_left_density_rate hF hw c hρ hρ0 hv hv0 hdensity
  let bW := Module.finBasis ℝ S.covector.ker
  have hactive : Ioo D.lo D.hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.support.calibrated
  have hdet (t : ℝ) (ht : t ∈ Ioo D.lo h) :
      (L.jacobiPositionMatrix bW (L.clock t)).det ≠ 0 := by
    have hx := L.geometry.curve_source (w, t) (hI t (Ioo_subset_Icc_self ht))
    rw [← D.curve_eq] at hx
    have hj := D.phase_jet L.old t hx
    exact L.jacobiPositionMatrix_det_ne_zero bW D.curve_eq
      (hI t (Ioo_subset_Icc_self ht)) hj.1 hj.2
      (D.jacobian_pos L.old t (hactive ⟨ht.1, ht.2.trans hh⟩) hx)
  have hrank := L.geometry.actual_physical_kernel_left_doublePole_rank
    D.comparison hF bW (L.spatialBasis bW) hlh hI hdet hη hRem
    (fun r hr ↦ by
      have hp := hpole r hr
      rw [D.original_kernel_eq hF hw] at hp
      exact hp)
  change G.rank = Module.finrank ℝ (LinearMap.ker
    (L.jacobiPositionMatrix bW (L.clock D.lo)).mulVecLin) at hrank
  refine ⟨L, h, ε, K, hlh, hh, hε, hεh, hK, hlaw, ?_⟩
  intro r hr
  rw [hrank]
  exact hbound r hr

omit [BorelSpace E] in
/-- The corresponding right endpoint rate uses the rank of its own unchanged
original kernel residue and its own original physical conditional density. -/
theorem OriginalSeedConditionalMoments.exists_original_right_density_residue_rate
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
    ∃ (L : SeedEndpointChart S D.comparison D.hi) (l ε K : ℝ),
      D.lo < l ∧ l < D.hi ∧ 0 < ε ∧ ε < D.hi - l ∧ 0 < K ∧
      (σ.map (fun x : ℝ ↦ x - S.level)).restrict (Ioo l D.hi) =
        (volume.restrict (Ioo l D.hi)).withDensity (fun t ↦
          ENNReal.ofReal (c.toReal * populationSeedChartDensity S ρ v L.center w t)) ∧
      ∀ r ∈ Ioo 0 ε,
        0 ≤ c.toReal * populationSeedChartDensity S ρ v L.center w (D.hi - r) ∧
        c.toReal * populationSeedChartDensity S ρ v L.center w (D.hi - r) ≤ K * r ^ G.rank := by
  obtain ⟨L, l, ε, K, hl, hlh, hI, hε, hεh, hK, hlaw, hbound⟩ :=
    D.exists_original_right_density_rate hF hw c hρ hρ0 hv hv0 hdensity
  let bW := Module.finBasis ℝ S.covector.ker
  have hactive : Ioo D.lo D.hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.support.calibrated
  have hdet (t : ℝ) (ht : t ∈ Ioo l D.hi) :
      (L.jacobiPositionMatrix bW (L.clock t)).det ≠ 0 := by
    have hx := L.geometry.curve_source (w, t) (hI t (Ioo_subset_Icc_self ht))
    rw [← D.curve_eq] at hx
    have hj := D.phase_jet L.old t hx
    exact L.jacobiPositionMatrix_det_ne_zero bW D.curve_eq
      (hI t (Ioo_subset_Icc_self ht)) hj.1 hj.2
      (D.jacobian_pos L.old t (hactive ⟨hl.trans ht.1, ht.2⟩) hx)
  have hrank := L.geometry.actual_physical_kernel_right_doublePole_rank
    D.comparison hF bW (L.spatialBasis bW) hlh hI hdet hη hRem
    (fun r hr ↦ by
      have hp := hpole r hr
      rw [D.original_kernel_eq hF hw] at hp
      exact hp)
  change G.rank = Module.finrank ℝ (LinearMap.ker
    (L.jacobiPositionMatrix bW (L.clock D.hi)).mulVecLin) at hrank
  refine ⟨L, l, ε, K, hl, hlh, hε, hεh, hK, hlaw, ?_⟩
  intro r hr
  rw [hrank]
  exact hbound r hr

end OTSelector.Reconstruction
