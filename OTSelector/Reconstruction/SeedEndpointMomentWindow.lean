import OTSelector.Reconstruction.SeedEndpointJacobiDensity

/-!
# An actual original-seed conditional moment window

The original physical density and original positive Jacobian construct the moment
window of the selected endpoint. The determinant regularity, graph density and all
clock data are consequences of the same comparison's actual joint phase derivative.
-/

open Set Matrix Module Manifold MeasureTheory Metric
open scoped Topology ContDiff Matrix.Norms.Operator

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

/-- The original physical density in a selected endpoint chart supplies its actual
moment window, without an assumed Jacobi determinant or clock-density formula. -/
def physicalMomentWindowOfDensity (G : SeedEndpointChart S C endpoint)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    (hcurve : S.curve w = C.curve w)
    {l h : ℝ} (hlh : l < h) (hI : ∀ t ∈ Icc l h, (w, t) ∈ G.geometry.U)
    (hjets : ∀ t ∈ Ioo l h, ∃ D : (S.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ),
      HasFDerivAt (F.chartMomentumFamily G.old S.curve) D (w, t) ∧
      HasFDerivAt (F.chartMomentumFamily G.old C.curve) D (w, t))
    (hpos : ∀ t ∈ Ioo l h,
      0 < parameterizedJacobian (populationSeedChartReadout S G.center) S.normalization (t, w))
    {μ : Measure ℝ} {ρ : M → ℝ} {v : M → E → ℝ} {c Rρ : ℝ}
    (hρ : Measurable (fun t ↦ ρ (S.curve w t)))
    (hρ0 : ∀ t ∈ Ioo l h, 0 ≤ ρ (S.curve w t))
    (hρR : ∀ t ∈ Ioo l h, ρ (S.curve w t) ≤ Rρ)
    (hweight : ContinuousOn (fun t ↦
      c * v G.old (populationSeedChartReadout S G.center (t, w))) (Icc l h))
    (hweight0 : ∀ t ∈ Ioo l h,
      0 ≤ c * v G.old (populationSeedChartReadout S G.center (t, w)))
    (hμ : μ.restrict (Ioo l h) = (volume.restrict (Ioo l h)).withDensity
      (fun t ↦ ENNReal.ofReal (c * populationSeedChartDensity S ρ v G.center w t))) :
    PhysicalJacobiMomentWindow
      (fun t ↦ (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w, t))⁻¹)
      μ l h := by
  apply G.geometry.physicalMomentWindow C hF bW (G.spatialBasis bW) hlh hI
    (κ := G.parameterNormalization bW) hρ hweight hρ0 hρR hweight0 (abs_nonneg _)
  · intro t ht
    obtain ⟨D, h₁, h₂⟩ := hjets t ht
    exact G.jacobiPositionMatrix_det_ne_zero bW hcurve (hI t (Ioo_subset_Icc_self ht))
      h₁ h₂ (hpos t ht)
  · rw [hμ]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    obtain ⟨D, h₁, h₂⟩ := hjets t ht
    rw [G.physicalDensity_eq bW ρ v hcurve (hI t (Ioo_subset_Icc_self ht)) h₁ h₂]
    congr 1
    change c * ((ρ (S.curve w t) * v G.old (populationSeedChartReadout S G.center (t, w))) *
      (|G.speed t| * |(G.jacobiPositionMatrix bW (G.clock t)).det| *
        G.parameterNormalization bW)) =
      (ρ (S.curve w t) * (c * v G.old (populationSeedChartReadout S G.center (t, w)))) *
        (|G.speed t| * |(G.jacobiPositionMatrix bW (G.clock t)).det| *
          G.parameterNormalization bW)
    ring

end OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart
