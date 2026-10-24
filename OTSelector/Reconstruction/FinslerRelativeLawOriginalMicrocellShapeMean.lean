import OTSelector.Reconstruction.FinslerRelativeLawOriginalGridShapeMean
import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellShapeLaw

/-! The actual measurable cell produces its canonical shape error without an extra filling premise. -/
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

/-- Literal original measurable microcell shapes satisfy the fixed-L pressure
comparison from their actual added volume alone. Measurability and the weighted
hole limit are supplied internally, including Haar-null subcells. -/
theorem OriginalPopulationCoefficientCore.exists_original_microcellShape_pressure_error
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
      (s : Set (Fin q → ℝ)), MeasurableSet s → volume s ≠ (⊤ : ℝ≥0∞) →
      ∀ (cells : ℕ → Finset (Fin q → ℤ)),
      Tendsto (fun N ↦ volume ((⋃ ν ∈ cells N,
        (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) \ s))
        atTop (𝓝 0) → ∀ T : ℝ, 0 ≤ T →
      TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
        (∑ ν ∈ cells N, affineClassBinomialShapeExpectation source target
          (α : Measure _) (β : Measure _) N (positiveMicroscopicCubeProbability q density L N)
          ⟨positiveMicroscopicGridSide q L N, positiveMicroscopicGridSide_nonneg q L N⟩
          (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N)
          (originalMicrocellShape (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ))
            (positiveMicroscopicGridOrder q L N) ν s)
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
  obtain ⟨source, target, hcode, hsum⟩ :=
    C.exists_original_grid_binomialShape_pressure_error Q z₀ hz₀ f P₀ hP₀ hmass hq
  refine ⟨source, target, hcode, ?_⟩
  intro density hdensity L hL s hs hsfin cells hadded T hT
  let S := fun N ν ↦ originalMicrocellShape (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ))
    (positiveMicroscopicGridOrder q L N) ν s
  have hS : ∀ N ν, ν ∈ cells N → MeasurableSet (S N ν) := by
    intro N ν _
    apply measurableSet_affineHaarCubeCoord_image _ _
      (inv_pos.mpr (by exact_mod_cast (positiveMicroscopicGridOrder q L N).pos_of_neZero))
    exact hs.inter (measurableSet_affineHaarCube _ _ _)
  have hfill : Tendsto (fun N ↦ positiveMicroscopicGridSide q L N ^ q *
      ∑ ν ∈ cells N, ((cubeMeasure (Fin q) 1) (S N ν)ᶜ).toReal) atTop (𝓝 0) := by
    apply tendsto_original_microcell_shape_filling_of_hole_mass volume
      (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ)) hs
      (positiveMicroscopicGridOrder q L) cells
    convert hadded using 1
    rfl
  exact hsum density hdensity L hL s hsfin cells hadded S hS hfill T hT

end OTSelector.Reconstruction
