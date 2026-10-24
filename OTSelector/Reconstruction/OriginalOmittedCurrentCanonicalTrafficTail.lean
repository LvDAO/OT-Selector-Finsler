import OTSelector.Reconstruction.OriginalMinimizerPathClockCurrentLtwo
import OTSelector.Reconstruction.OriginalOmittedTrafficDensityLimit
import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice

/-! The genuine original minimizer supplies the omitted long-path square-density limit. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal Topology ContDiff BigOperators Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The original minimizer, its actual independent source/target density inputs, and the
concrete original radial kernel produce subextensive omitted complete-path square traffic.
All eight actual traffic regions, the long-path tail and the spatial collar are internal;
no square-integrability or tail-rate conclusion is supplied as an extra premise. -/
theorem original_minimizer_canonical_omittedTraffic_sq_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 2≤qdim)
    {densityμ densityν : M→ℝ} {v : M→E→ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀x,0≤densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀x,0≤densityν x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ↦x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ↦x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {g : ℝ→ℝ→ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀x y,|g x y|≤gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, ∫⁻ z in haarRootCube (Fin qdim) R,
        originalSeedRestrictedPathAbsoluteTraffic S w
          (fun x ↦ originalEuclideanMollifier qdim (x-z))
          (originalPathLengthRetained S w R (ell R))ᶜ scene ^ 2 ∂volume
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))).toReal /
          volume.real (haarRootCube (Fin qdim) R)) atTop (𝓝 0) := by
  obtain ⟨radius,hrad,hrspan,GLeft,GRight,RemLeft,RemRight,hGLeft,hGRight,
    hRemLeft,hRemRight,hpoleLeft,hpoleRight,_hcomparison⟩ :=
    D.exists_original_both_poles_common_radius hF hw
  have hsupport : ∀ x : Fin qdim → ℝ, 1 < ‖x‖ → originalEuclideanMollifier qdim x = 0 :=
    fun x hx ↦ raw_unit_range_of_euclidean_unit_range
      (originalEuclideanMollifier_unit_range qdim) x hx.le
  have hupper : ∀ x : Fin qdim → ℝ,
      originalEuclideanMollifier qdim x ≤ originalEuclideanMollifierBound qdim :=
    fun x ↦ (le_abs_self _).trans (abs_originalEuclideanMollifier_le qdim x)
  have hfull := D.original_minimizer_completePathAbsoluteTraffic_memLp_two
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hrad hrspan hrad hrspan hGLeft hGRight hRemLeft.continuousOn hRemRight.continuousOn
    hpoleLeft hpoleRight hg hgb τ Q hmin
    (contDiff_originalEuclideanMollifier qdim).continuous.measurable
    (integrable_originalEuclideanMollifier qdim) (originalEuclideanMollifier_nonneg qdim)
    (by norm_num : (0:ℝ) ≤ 1) (originalEuclideanMollifierBound_nonneg qdim) hupper hsupport
  exact D.tendsto_original_wholeCube_omittedTraffic_sq_density_zero hF hw hbounds Q
    (contDiff_originalEuclideanMollifier qdim).continuous.measurable
    (integrable_originalEuclideanMollifier qdim) (by norm_num : (0:ℝ) ≤ 1)
    hsupport hfull.2 hell hlarge hsmall

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
