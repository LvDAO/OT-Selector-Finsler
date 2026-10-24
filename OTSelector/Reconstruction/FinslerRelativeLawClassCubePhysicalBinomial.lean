import OTSelector.Reconstruction.FinslerRelativeLawClassCubeBinomial
import OTSelector.Reconstruction.FinslerRelativeLawAffineBinomialPrefix

/-! Actual physical full-cube finite-prefix means converge before the microscopic scale grows. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators
  BoundedContinuousFunction Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Mean untruncated affine physical legal value on two independent original
binomial prefixes. The physical intensity remains N; p is only a count probability. -/
def affineBinomialCubeExpectation {q : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) (side : ℝ) (origin : Fin q → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ) : ℝ :=
  ∫ d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B),
    unclampedBlockLegalTilted q source target N kin probe tilt
      (mapBlockData (affineMarkedPoint origin side) d.1)
      (mapBlockData (affineMarkedPoint origin side) d.2)
    ∂(blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
      (binomWeight N (Real.toNNReal (p : ℝ)))).prod
      (blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
        (binomWeight N (Real.toNNReal (p : ℝ))))

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The actual original coefficient core supplies every geometric and finite
model hypothesis for de-Poissonizing the true physical full-cube expectation.
The chosen strict clocks and pair-class laws are fixed before all N and L. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_fullCube_binomial_physical
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ source target : Fin Q.count → ℝ,
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧
      ∀ (density : ℝ≥0) (_hdensity : 0 < density) (L : ℝ) (hL : 0 < L),
      ∀ (origin : ℕ → Fin q → ℝ) (tilt : ℝ),
      (∀ N : ℕ, Integrable
        (fun d : BlockData ((Fin q → ℝ) × Fin Q.count) ×
            BlockData ((Fin q → ℝ) × Fin Q.count) ↦
          unclampedBlockLegalTilted q source target N (C.clockClassKinetic Q z₀)
            (C.clockClassProbe Q z₀ hz₀ f) tilt
            (mapBlockData (affineMarkedPoint (origin N) (microscopicGridSide q L N)) d.1)
            (mapBlockData (affineMarkedPoint (origin N) (microscopicGridSide q L N)) d.2))
        ((blockDataLaw ((cubeMeasure (Fin q) 1).prod (α : Measure _))
          (binomWeight N (Real.toNNReal (microscopicCubeProbability q density L N : ℝ)))).prod
          (blockDataLaw ((cubeMeasure (Fin q) 1).prod (β : Measure _))
            (binomWeight N (Real.toNNReal (microscopicCubeProbability q density L N : ℝ)))))) ∧
      Tendsto (fun N : ℕ ↦ affineBinomialCubeExpectation source target
          (α : Measure _) (β : Measure _) N (microscopicCubeProbability q density L N)
          (microscopicGridSide q L N) (origin N) (C.clockClassKinetic Q z₀)
          (C.clockClassProbe Q z₀ hz₀ f) tilt) atTop
        (𝓝 (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
          (density * ⟨L ^ q, pow_nonneg hL.le q⟩)
          (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt)) := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, _⟩ := C.exists_clockClass_strict_clocks Q
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  refine ⟨source, target, hcode, ?_⟩
  intro density hdensity L hL origin tilt
  have hfinite (N : ℕ) := affineBinomialBlock_integrable_integral
    (kin := C.clockClassKinetic Q z₀) (probe := C.clockClassProbe Q z₀ hz₀ f)
    q hq (measurable_of_countable source) (measurable_of_countable target)
    (α : Measure _) (β : Measure _) N (microscopicCubeProbability q density L N)
    (microscopicGridSide_nonneg q L N) (origin N) hK (norm_nonneg f)
    (C.measurable_clockClassKinetic Q z₀) hbound
    (fun j k c _ v ↦ C.clockClassKinetic_homogeneous Q z₀ j k c v)
    (C.measurable_clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f) tilt
  refine ⟨fun N ↦ (hfinite N).1, ?_⟩
  have hlim := C.tendsto_clockClass_fullCube_binomial Q z₀ hz₀ f P₀ hP₀ hmass hq density hdensity hL tilt
  apply Tendsto.congr' _ hlim
  filter_upwards [] with N
  exact ((hfinite N).2.trans (integral_congr_ae (.of_forall fun cloud ↦
    (finiteClassLegalTilted_eq_clock q _ source target hcode _ _ _ _ cloud).symm))).symm

end OTSelector.Reconstruction
