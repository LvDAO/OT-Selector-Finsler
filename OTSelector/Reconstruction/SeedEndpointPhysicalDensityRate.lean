import OTSelector.Reconstruction.SeedEndpointPhysicalJacobiSystem
import OTSelector.Reconstruction.ClosedJacobiEndpointDeterminantRate
import OTSelector.Reconstruction.PhysicalJacobiDensityDeterminantBound
import OTSelector.Reconstruction.FinslerPopulationDensityBounds

/-! The original physical population density has the determinant order of the
same selected actual endpoint Jacobi matrix, in original physical time. -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
  {C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q} {endpoint : ℝ}

omit [BorelSpace E] in
/-- Bound the actual original conditional density by its selected physical-time
Jacobi determinant. The physical population and volume factors remain unchanged. -/
theorem exists_original_density_determinant_bound (G : SeedEndpointChart S C endpoint)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    (hw : w ∈ S.labels) (hcurve : S.curve w = C.curve w)
    {l h : ℝ} (hI : ∀ t ∈ Icc l h, (w, t) ∈ G.geometry.U)
    (hjet : ∀ t ∈ Ioo l h,
      ∃ D : (S.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ),
        HasFDerivAt (F.chartMomentumFamily G.old S.curve) D (w, t) ∧
        HasFDerivAt (F.chartMomentumFamily G.old C.curve) D (w, t))
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ContinuousOn (v G.old) (extChartAt 𝓘(ℝ, E) G.old).target)
    (hv0 : ∀ y ∈ (extChartAt 𝓘(ℝ, E) G.old).target, 0 ≤ v G.old y) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ioo l h,
      0 ≤ c.toReal * populationSeedChartDensity S ρ v G.center w t ∧
      c.toReal * populationSeedChartDensity S ρ v G.center w t ≤
        K * |(G.jacobiPositionMatrix bW (G.clock t)).det| := by
  obtain ⟨_, Rρ, _, hρnonneg, hρbound, hweight, hweight0⟩ :=
    G.population_density_weight_data hF hw hρ hρ0 hv hv0 hI c
  obtain ⟨K, hK, hbound⟩ := exists_physical_jacobi_density_determinant_bound
    (J := fun t ↦ G.jacobiPositionMatrix bW (G.clock t))
    hρnonneg hρbound hweight hweight0
    (G.geometry.continuousOn_clockSpeed hI) (by norm_num : (0 : ℝ) < 1)
    (abs_nonneg _ : 0 ≤ G.parameterNormalization bW)
  refine ⟨K, hK, ?_⟩
  intro t ht
  obtain ⟨D, h₁, h₂⟩ := hjet t ht
  have heq : c.toReal * populationSeedChartDensity S ρ v G.center w t =
      (ρ (S.curve w t) * (c.toReal * v G.old
        (populationSeedChartReadout S G.center (t, w))) / 1) *
        (|G.speed t| * |(G.jacobiPositionMatrix bW (G.clock t)).det| *
          G.parameterNormalization bW) := by
    rw [G.physicalDensity_eq bW ρ v hcurve (hI t (Ioo_subset_Icc_self ht)) h₁ h₂]
    ring
  rw [heq]
  exact hbound t ht

end OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart
