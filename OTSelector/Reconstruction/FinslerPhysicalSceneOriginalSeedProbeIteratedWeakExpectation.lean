import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeWeakExpectation
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSourceProbeIteratedWeakExpectation

/-!
# Original physical seed probe expectations through both given weak stages

All source-only Lusin and readout continuity inputs are discharged from the
actual original Finsler geometry. The sample and tilt indices remain separate.
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

/-- Both weak stages retain the full actual original seed probe gap and its
real and extended nonnegative expectations, with the original source fixed. -/
theorem original_seed_probe_gap_expectation_limits_of_iterated_weak
    (μ : Measure M) [IsProbabilityMeasure μ] (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPolish : PolishSpace M := inferInstance
    ∀ {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
      [OpensMeasurableSpace S] [HasOuterApproxClosed S]
      (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
      (R : ProbabilityMeasure S) (ψ : ℕ → ℕ)
      (_hinner : ∀ ℓ, Tendsto (Pn ℓ) atTop (𝓝 (Q ℓ)))
      (_houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
      (π₀ π₁ : S → ProbabilityMeasure (M × M))
      (_hπ₀ : Continuous π₀) (_hπ₁ : Continuous π₁)
      (_hsource₀ : ∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₀ s : Measure (M × M)).fst = μ)
      (_hsource₁ : ∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₁ s : Measure (M × M)).fst = μ),
    let obs : S → ℝ := fun s ↦
      |(∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 ∂(π₀ s : Measure (M × M))) -
        ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g p.1 p.2 ∂(π₁ s : Measure (M × M))|
    (∀ᵐ s ∂(R : Measure S), (π₀ s : Measure (M × M)).fst = μ ∧
      (π₁ s : Measure (M × M)).fst = μ) ∧
    (∀ ℓ n, Integrable obs (Pn ℓ n : Measure S)) ∧
    (∀ ℓ, Integrable obs (Q ℓ : Measure S)) ∧ Integrable obs (R : Measure S) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫ s, obs s ∂(Pn ℓ n : Measure S)) atTop
      (𝓝 (∫ s, obs s ∂(Q ℓ : Measure S)))) ∧
    Tendsto (fun ℓ ↦ ∫ s, obs s ∂(Q (ψ ℓ) : Measure S)) atTop
      (𝓝 (∫ s, obs s ∂(R : Measure S))) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Pn ℓ n : Measure S)) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (obs s) ∂(Q ℓ : Measure S)))) ∧
    Tendsto (fun ℓ ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Q (ψ ℓ) : Measure S)) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S))) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  dsimp only
  intro S instS instM instO instH Pn Q R ψ hinner houter π₀ π₁ hπ₀ hπ₁ hsource₀ hsource₁
  exact fixed_source_probe_gap_expectation_limits_of_iterated_weak Pn Q R ψ hinner houter
    π₀ π₁ hπ₀ hπ₁ μ (Function.uncurry (physicalSceneOriginalSeedCompactProbe
      (P := P) (a := a) (κ := κ) (lambda := lambda) j g))
    (norm_nonneg _) (fun p ↦ abs_physicalSceneOriginalSeedCompactProbe_le
      (P := P) (a := a) (κ := κ) (lambda := lambda) j g p.1 p.2)
    (fun ε hε ↦ exists_original_seed_probe_probability_readout_approximation
      hF hcomplete hu ha hinj μ j g hε) hsource₀ hsource₁

end OTSelector.Reconstruction
