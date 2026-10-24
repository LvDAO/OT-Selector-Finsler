import OTSelector.Reconstruction.OriginalReversePressureNativeFocal
import OTSelector.Reconstruction.OriginalIIDFinalValueFieldReverseProbe
import OTSelector.Reconstruction.FinslerPopulationSupportedComparison
import OTSelector.Reconstruction.FinslerSeedRootPartition

/-! The actual physical clock densities close the original conditional reverse
pressure simultaneously on every selected seed piece and every physical test. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace M] in
/-- The original two physical density laws and original inverse produce the
single almost-everywhere root comparison required by the actual final fields.
Every existing moment witness is used directly; none is replaced or reselected. -/
theorem original_seedRoot_focal_reverse_of_physical_density_laws
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ρ₀ ρ₁ : M → ℝ) (v : M → E → ℝ) (b : Z × ℝ → M)
    (hdensity₀ : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (κ j)
      lambda μ ρ₀ v (P j).seed.level)
    (hdensity₁ : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (κ j)
      lambda ν ρ₁ v (P j).seed.level)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x ≤ u y) ↔ u y-u x=dist x y)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x,u x)=x)
    (hdim : 6 ≤ finrank ℝ E)
    (hρ₀ : Continuous ρ₀) (hρ₁ : Continuous ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ,E) old).target, 0 ≤ v old y)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : ∀ᵐ z ∂lambda, ConditionalClockSupportBounds
      (condDistrib u a μ z) (condDistrib u a ν z) gap diameter) :
    ∀ᵐ z ∂lambda, ∀ f : M × M →ᵇ ℝ, ∀ j,
      ∀ hz : z ∈ populationSeedRootPiece P a κ lambda j,
      ∀ D : OriginalSeedConditionalMoments (P j).seed
        (populationSeedPieceLabel P a κ lambda j ⟨z,hz⟩)
        (condDistrib u a μ z) (condDistrib u a ν z),
      ∀ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
        (condDistrib u a μ z) (condDistrib u a ν z) (D.originalFocalKinetic gap)
        (originalPhysicalRootProbe b f z),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ (P j).seed.covector.ker)
        id id (condDistrib u a μ z) (condDistrib u a ν z) (D.originalFocalKinetic gap)
        (originalPhysicalRootProbe b f z) R t) ≤ Q.value t := by
  have h₀ := ae_all_iff.mpr (fun j ↦ (hdensity₀ j).ae_seedClockDensity)
  have h₁ := ae_all_iff.mpr (fun j ↦ (hdensity₁ j).ae_seedClockDensity)
  filter_upwards [hsep,h₀,h₁] with z hbounds hs ht
  intro f j hz D
  let S := (P j).seed
  let w := populationSeedPieceLabel P a κ lambda j ⟨z,hz⟩
  have hw : w.val ∈ S.labels := w.property
  have hwz : a (S.curve w.val 0) = z := populationSeedPieceLabel_root P a κ lambda j ⟨z,hz⟩
  let : IsProbabilityMeasure (condDistrib u a μ z) := D.support.source.probability
  let : IsProbabilityMeasure (condDistrib u a ν z) := D.support.target.probability
  have hq : 4 < finrank ℝ S.covector.ker := by
    have hh := S.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at hh
    omega
  let ψ := originalCompleteSeedPhysicalProbe S w.val hw hF f
  have hm : Measurable (Function.uncurry (fun x y ↦ f (S.curve w.val (x-S.level),S.curve w.val (y-S.level)))) :=
    ψ.continuous.measurable
  have hbnd (x y : ℝ) : |f (S.curve w.val (x-S.level),S.curve w.val (y-S.level))| ≤ ‖f‖ :=
    by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (S.curve w.val (x-S.level),S.curve w.val (y-S.level))
  have hcont : ContinuousOn
      (Function.uncurry (fun x y ↦ f (S.curve w.val (x-S.level),S.curve w.val (y-S.level))))
      {p | p.1-S.level ∈ Ioo D.lo D.hi ∧ p.2-S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2} :=
    ψ.continuous.continuousOn
  have hseedReverse := fun Qseed t ↦ D.originalFocalPressure_le_same_candidate hF hw hq
    ((populationSeedLabelReference S a (κ j)).rnDeriv lambda z)
    ((populationSeedLabelReference S a (κ j)).rnDeriv lambda z)
    hρ₀ hρ₀nonneg hρ₁ hρ₁nonneg hv hv0 (hs j w.val hw hwz) (ht j w.val hw hwz)
    hbounds hgap hm hbnd hcont t Qseed
  have hphysical := D.original_focal_physical_reverse_of_seed_probe_reverse
    hw hF hcomplete hu horder hinv f gap hseedReverse
  dsimp only [S,w] at hwz
  rw [hwz] at hphysical
  exact hphysical

end OTSelector.Reconstruction
