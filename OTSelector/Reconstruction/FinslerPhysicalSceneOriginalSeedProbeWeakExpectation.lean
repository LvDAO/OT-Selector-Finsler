import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeWeakContinuity
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSourceProbeWeakExpectation

/-!
# Original seed probe expectations pass the same weak law

The original source-only Lusin producer discharges every approximation and
readout-continuity input. The original target marginal may vary freely.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
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

/-- The complete original seed readout gap, its integrability and its expectation
pass a weak original-plan law using only the unchanged original source. -/
theorem original_seed_probe_gap_expectation_tendsto_of_weak
    (μ : Measure M) [IsProbabilityMeasure μ] (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPolish : PolishSpace M := inferInstance
    ∀ {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
      [OpensMeasurableSpace S] [HasOuterApproxClosed S]
      (R : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
      (_hweak : Tendsto Pn atTop (𝓝 R))
      (π₀ π₁ : S → ProbabilityMeasure (M × M))
      (_hπ₀ : Continuous π₀) (_hπ₁ : Continuous π₁)
      (_hsource₀ : ∀ n, ∀ᵐ s ∂(Pn n : Measure S), (π₀ s : Measure (M × M)).fst = μ)
      (_hsource₁ : ∀ n, ∀ᵐ s ∂(Pn n : Measure S), (π₁ s : Measure (M × M)).fst = μ),
    let obs : S → ℝ := fun s ↦
      |(∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 ∂(π₀ s : Measure (M × M))) -
        ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 ∂(π₁ s : Measure (M × M))|
    (∀ᵐ s ∂(R : Measure S), (π₀ s : Measure (M × M)).fst = μ ∧
      (π₁ s : Measure (M × M)).fst = μ) ∧
    (∀ n, Integrable obs (Pn n : Measure S)) ∧ Integrable obs (R : Measure S) ∧
      Tendsto (fun n ↦ ∫ s, obs s ∂(Pn n : Measure S)) atTop
        (𝓝 (∫ s, obs s ∂(R : Measure S))) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  dsimp only
  intro S instS instM instO instH R Pn hweak π₀ π₁ hπ₀ hπ₁ hsource₀ hsource₁
  exact fixed_source_probe_gap_expectation_tendsto_of_weak R Pn hweak π₀ π₁ hπ₀ hπ₁
    μ (Function.uncurry (physicalSceneOriginalSeedCompactProbe
      (P := P) (a := a) (κ := κ) (lambda := lambda) j g))
    (norm_nonneg _) (fun p ↦ abs_physicalSceneOriginalSeedCompactProbe_le
      (P := P) (a := a) (κ := κ) (lambda := lambda) j g p.1 p.2)
    (fun ε hε ↦ exists_original_seed_probe_probability_readout_approximation
      hF hcomplete hu ha hinj μ j g hε) hsource₀ hsource₁

end OTSelector.Reconstruction
