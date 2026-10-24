import OTSelector.Reconstruction.FinslerRelativeLawClassCubeSum
import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellMass

/-! Actual finite grid covers discharge the full-cube mean normalization bound. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry BoxIntegral
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators
  BoundedContinuousFunction Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- Original finite-volume measurable cells and vanishing added grid mass
suffice for the actual C/P0 summed physical mean limit. The actual filling
volume is kept; no bounded-cardinality or full-cell-volume oracle remains. -/
theorem OriginalPopulationCoefficientCore.exists_original_grid_fullCube_sum_error_tendstoUniformlyOn
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
      ∀ (density : ℝ≥0) (_hdensity : 0 < density) (L : ℝ) (hL : 0 < L)
      (s : Set (Fin q → ℝ)), volume s ≠ (⊤ : ℝ≥0∞) →
      ∀ (cells : ℕ → Finset (Fin q → ℤ)),
      Tendsto (fun N ↦ volume ((⋃ ν ∈ cells N,
        (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) \ s))
        atTop (𝓝 0) →
      ∀ (T : Set ℝ), IsCompact T →
      TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
        (∑ ν ∈ cells N, affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
          (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N)
          (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N)
          (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) / (N : ℝ) -
        volume.real (⋃ ν ∈ cells N,
          (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) *
          (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
            (density * ⟨L ^ q, pow_nonneg hL.le q⟩) (C.densityClockClassKinetic Q z₀ density)
            (C.clockClassProbe Q z₀ hz₀ f) tilt / L ^ q)) (fun _ ↦ 0) atTop T := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, hsum⟩ :=
    C.exists_clockClass_fullCube_sum_error_tendstoUniformlyOn Q z₀ hz₀ f P₀ hP₀ hmass hq
  refine ⟨source, target, hcode, ?_⟩
  intro density hdensity L hL s hs cells hadded T hT
  let J := fun N ↦ ↥(cells N)
  let U := fun N ↦ ⋃ ν ∈ cells N,
    (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))
  have hvolume (N : ℕ) : volume.real (U N) =
      (Fintype.card (J N) : ℝ) * positiveMicroscopicGridSide q L N ^ q := by
    simpa only [U, J, Fintype.card_coe, positiveMicroscopicGridSide] using
      unitPartition_finite_union_volume q (positiveMicroscopicGridOrder q L N) (cells N)
  have hbound := eventually_measureReal_le_of_added_mass_tendsto volume hs U hadded
  have hcardbound : ∀ᶠ N in atTop,
      (Fintype.card (J N) : ℝ) * positiveMicroscopicGridSide q L N ^ q ≤ volume.real s + 1 := by
    filter_upwards [hbound] with N hN
    rw [← hvolume]
    exact hN
  have hresult := hsum density hdensity L hL J
    (fun N ν l ↦ ((ν.val l : ℤ) : ℝ) / positiveMicroscopicGridOrder q L N) T hT
    (volume.real s + 1) (by positivity) hcardbound
  apply hresult.congr
  filter_upwards [] with N
  intro tilt _
  rw [← hvolume]
  have heq := Finset.sum_coe_sort (cells N) (fun ν : Fin q → ℤ ↦
    affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
      (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N)
      (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N)
      (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt)
  exact congrArg (fun value : ℝ ↦ value / (N : ℝ) - volume.real (U N) *
    (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
      (density * ⟨L ^ q, pow_nonneg hL.le q⟩) (C.densityClockClassKinetic Q z₀ density)
      (C.clockClassProbe Q z₀ hz₀ f) tilt / L ^ q)) heq

end OTSelector.Reconstruction
