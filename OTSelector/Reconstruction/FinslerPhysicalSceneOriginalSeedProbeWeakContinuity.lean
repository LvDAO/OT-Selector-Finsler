import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeApproximation
import OTSelector.MeasureTheory.FixedSourceWeakReadout

/-!
# The original coordinate readouts are weakly continuous on their source carrier

Source-only Lusin approximation internally removes the merely measurable seed
coordinate and seed indicator. No continuity premise is imposed on the actual
original physical probe.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- Every original seed compact probe has arbitrarily accurate ordinary bounded
continuous readout approximations uniformly over the original source family. -/
theorem exists_original_seed_probe_probability_readout_approximation
    (μ : Measure M) [IsFiniteMeasure μ] (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : (M × M) →ᵇ ℝ, ∀ π : ProbabilityMeasure (M × M),
      (π : Measure (M × M)).fst = μ →
      |(∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 ∂(π : Measure (M × M))) -
        ∫ p, G p ∂(π : Measure (M × M))| ≤ ε := by
  let B := ‖g.toBoundedContinuousFunction‖
  have hB : 0 ≤ B := norm_nonneg _
  have hden : 0 < 2 * B + 1 := by positivity
  have hδ : 0 < ε / (2 * B + 1) := div_pos hε hden
  obtain ⟨G, _, herror⟩ := exists_original_seed_compact_probe_uniform_approximation
    (P := P) (a := a) (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj μ j g hδ
  refine ⟨G, fun π hπ ↦ ?_⟩
  have herr := (herror (π : Measure (M × M)) hπ).2.2
  apply herr.trans
  have heq : (ε / (2 * B + 1)) * (2 * B + 1) = ε := div_mul_cancel₀ ε hden.ne'
  dsimp only [B] at heq hδ ⊢
  nlinarith

/-- The actual merely measurable original source seed readout is continuous
for weak probability plans on the unchanged full source marginal carrier. -/
theorem continuousOn_original_seed_compact_probe_probability_readout
    (μ : Measure M) [IsFiniteMeasure μ] (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPolish : PolishSpace M := inferInstance
    ContinuousOn (fun π : ProbabilityMeasure (M × M) ↦
      ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
        (lambda := lambda) j g p.1 p.2 ∂(π : Measure (M × M)))
      {π | (π : Measure (M × M)).fst = μ} := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  exact continuousOn_probability_integral_of_uniform_source_approx μ _
    (fun ε hε ↦ exists_original_seed_probe_probability_readout_approximation
      hF hcomplete hu ha hinj μ j g hε)

/-- One globally bounded continuous original-plan readout agrees with the actual
seed probe on every probability plan with the unchanged original source. -/
theorem exists_original_seed_compact_probe_boundedContinuous_probability_readout
    (μ : Measure M) [IsProbabilityMeasure μ] (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPolish : PolishSpace M := inferInstance
    ∃ L : ProbabilityMeasure (M × M) →ᵇ ℝ,
      ‖L‖ ≤ ‖g.toBoundedContinuousFunction‖ ∧
      ∀ π : ProbabilityMeasure (M × M), (π : Measure (M × M)).fst = μ →
        L π = ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 ∂(π : Measure (M × M)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  apply exists_boundedContinuous_probability_integral_extension_of_source_approx
    μ _ (norm_nonneg _) (fun p ↦
      abs_physicalSceneOriginalSeedCompactProbe_le (P := P) (a := a) (κ := κ)
        (lambda := lambda) j g p.1 p.2)
  intro ε hε
  exact exists_original_seed_probe_probability_readout_approximation
    hF hcomplete hu ha hinj μ j g hε

end OTSelector.Reconstruction
