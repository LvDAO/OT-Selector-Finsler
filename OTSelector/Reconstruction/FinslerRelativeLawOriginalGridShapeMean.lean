import OTSelector.Reconstruction.FinslerRelativeLawOriginalGridClassMean
import OTSelector.Reconstruction.FinslerConcreteUpperClassBinomialShape

/-! Original changing shapes inherit the actual finite-class microscopic pressure reference. -/
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

/-- The actual C/P0 original binomial shape sums converge, after normalization,
to their actual filling volume times the fixed-L legal pressure. Shape laws
remain binomial throughout; only the homogeneous full cubes are Poissonized. -/
theorem OriginalPopulationCoefficientCore.exists_original_grid_binomialShape_pressure_error
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
      ∀ (S : ℕ → (Fin q → ℤ) → Set (Fin q → ℝ)),
      (∀ N ν, ν ∈ cells N → MeasurableSet (S N ν)) →
      Tendsto (fun N ↦ positiveMicroscopicGridSide q L N ^ q *
        ∑ ν ∈ cells N, ((cubeMeasure (Fin q) 1) (S N ν)ᶜ).toReal) atTop (𝓝 0) →
      ∀ T : ℝ, 0 ≤ T →
      TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
        (∑ ν ∈ cells N, affineClassBinomialShapeExpectation source target
          (α : Measure _) (β : Measure _) N (positiveMicroscopicCubeProbability q density L N)
          ⟨positiveMicroscopicGridSide q L N, positiveMicroscopicGridSide_nonneg q L N⟩
          (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N) (S N ν)
          (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) / (N : ℝ) -
        volume.real (⋃ ν ∈ cells N,
          (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) *
          (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
            (density * ⟨L ^ q, pow_nonneg hL.le q⟩) (C.densityClockClassKinetic Q z₀ density)
            (C.clockClassProbe Q z₀ hz₀ f) tilt / L ^ q)) (fun _ ↦ 0) atTop (Icc (-T) T) := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, hfilling⟩ :=
    C.exists_clockClass_binomial_filling_limit Q z₀ hz₀ f P₀ hP₀ hmass hq
  refine ⟨source, target, hcode, ?_⟩
  intro density hdensity L hL s hs cells hadded S hS hfill T hT
  let side : ℕ → ℝ≥0 := fun N ↦
    ⟨positiveMicroscopicGridSide q L N, positiveMicroscopicGridSide_nonneg q L N⟩
  let countBound : ℝ≥0 := density * ⟨L ^ q, pow_nonneg hL.le q⟩
  have hp : ∀ N, (positiveMicroscopicCubeProbability q density L N : ℝ) ≤
      (density : ℝ) * (side N : ℝ) ^ q := fun N ↦ min_le_left _ _
  have hcount : ∀ N : ℕ, (N : ℝ≥0) * density * side N ^ q ≤ countBound := by
    intro N
    have hm := mul_le_mul_of_nonneg_left (positiveMicroscopicGrid_mass_le hq hL N) density.coe_nonneg
    have hc : (N : ℝ) * (density : ℝ) * positiveMicroscopicGridSide q L N ^ q ≤
        (density : ℝ) * L ^ q := by nlinarith only [hm]
    exact_mod_cast hc
  have hshape := hfilling density countBound hdensity T hT (Fin q → ℤ) cells
    (positiveMicroscopicCubeProbability q density L) side hp hcount
    (fun N ν l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N) S hS hfill
  have hmodel := C.tendstoUniformlyOn_original_grid_classMean_error Q z₀ hz₀ f P₀ hP₀ hmass hq
    density hdensity hL s hs cells hadded (isCompact_Icc : IsCompact (Icc (-T) T))
  convert hshape.add hmodel using 1
  · funext N tilt
    dsimp only [Pi.add_apply, finiteClassBinomialMean, side, q]
    exact (sub_add_sub_cancel _ _ _).symm
  · funext tilt
    simp only [Pi.add_apply, add_zero]

end OTSelector.Reconstruction
