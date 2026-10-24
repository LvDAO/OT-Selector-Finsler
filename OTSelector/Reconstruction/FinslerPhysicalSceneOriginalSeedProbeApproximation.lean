import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedCompactProbe
import OTSelector.MeasureTheory.SourceLusinProbeApproximation

/-!
# Source-controlled continuous approximation of actual original seed probes

The original complete metric supplies Polishness. The actual seed geometry supplies source
coordinate and source-set measurability, while the unchanged potential is continuous. Thus one
bounded continuous physical pair test approximates the original seed probe uniformly over all
finite original plans with the prescribed source marginal.
-/

open Set Function MeasureTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]

/-- The actual original seed probe has one bounded continuous approximation uniformly for all
finite original plans with the same source marginal. Only that source marginal controls the
approximation, including the absolute error of the full original integral. -/
theorem exists_original_seed_compact_probe_uniform_approximation
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (μ : Measure M) [IsFiniteMeasure μ] (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ test : (M × M) →ᵇ ℝ, ‖test‖ ≤ ‖g.toBoundedContinuousFunction‖ ∧
      ∀ (π : Measure (M × M)) [IsFiniteMeasure π], π.map Prod.fst = μ →
        Integrable (Function.uncurry (physicalSceneOriginalSeedCompactProbe
          (P := P) (a := a) (κ := κ) (lambda := lambda) j g)) π ∧
        (∫ p, |physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 - test p| ∂π) ≤
          2 * ‖g.toBoundedContinuousFunction‖ * ε ∧
        |(∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 ∂π) - ∫ p, test p ∂π| ≤
          2 * ‖g.toBoundedContinuousFunction‖ * ε := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hcoord : Measurable (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j) :=
    (measurable_physicalSceneOriginalSeedPairReadout hF hcomplete hu ha hinj j).fst.comp
      (measurable_id.prodMk measurable_id)
  have hH := measurableSet_physicalSceneOriginalSeedSource
    (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj j
  obtain ⟨test, hbound, happrox⟩ :=
    exists_source_compactProbe_uniform_approximation μ hcoord hH u hu.continuous g hε
  refine ⟨test, hbound, ?_⟩
  intro π hfinite hπ
  exact happrox π hπ

end OTSelector.Reconstruction
