import OTSelector.Reconstruction.OriginalOmittedCurrentCanonicalEnergyTail
import OTSelector.Reconstruction.OriginalOmittedCurrentLtwoEnergyReadout

/-! The actual original stage bulk-energy random variable has a subextensive expectation. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
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

/-- The actual original minimizer supplies a measurable integrable canonical omitted-current
Euclidean energy at every scale. Its genuine real expectation, which is the bulk term of
the common Neumann budget, vanishes after normalization by the same original cube volume. -/
theorem original_minimizer_canonical_omittedCurrentLtwoEnergy_mean_density_zero
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
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) (A : ℝ → Set ℝ) :
    (∀ R, Measurable (originalCanonicalOmittedCurrentLtwoEnergy S w R (ell R) (A R)) ∧
      Integrable (originalCanonicalOmittedCurrentLtwoEnergy S w R (ell R) (A R))
        (Q.law : Measure (LegalMarkedOptimalInputScene qdim))) ∧
    Tendsto (fun R : ℝ ↦
      (∫ scene, originalCanonicalOmittedCurrentLtwoEnergy S w R (ell R) (A R) scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))) /
          volume.real (haarRootCube (Fin qdim) R)) atTop (𝓝 0) := by
  obtain ⟨hfinite, hlim⟩ := D.original_minimizer_canonical_omittedCurrent_euclidean_sq_density_zero
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb τ Q hmin hell hlarge hsmall A
  have heq (R : ℝ) := integral_originalCanonicalOmittedCurrentLtwoEnergy_eq_of_finite
    S hF hw R (ell R) (A R) (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) (hfinite R)
  refine ⟨fun R ↦ ⟨measurable_originalCanonicalOmittedCurrentLtwoEnergy S hF hw R (ell R) (A R),
    (heq R).1⟩, ?_⟩
  convert hlim using 1
  funext R
  rw [(heq R).2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
