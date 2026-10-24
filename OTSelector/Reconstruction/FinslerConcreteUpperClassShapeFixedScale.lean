import OTSelector.Reconstruction.FinslerConcreteUpperClassShapeSum
import OTSelector.Probability.MicroscopicGridScale

/-!
The actual finite reference model's microscopic shape errors add according to
original filling volume. Normalization cancels the empirical intensity exactly;
no factor depending on the number of microcells is added.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
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

/-- The actual finite class model has a single normalized shape-error constant
at a fixed microscopic count scale and compact tilt interval. It is uniform in
the number, positions and arbitrary measurable shapes of all microcells. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_fixed_scale_shape_sum_bound
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
      ∀ (density countBound : ℝ≥0), 0 < density → ∀ T : ℝ, 0 ≤ T →
      ∃ A : ℝ, 0 ≤ A ∧
      ∀ (J : Type*) [Fintype J] (ambient side : ℝ≥0), 0 < ambient →
      ambient * density * side ^ q ≤ countBound →
      ∀ (origin : J → Fin q → ℝ) (S : J → Set (Fin q → ℝ)), (∀ j, MeasurableSet (S j)) →
      ∀ tilt : ℝ, |tilt| ≤ T →
      |(∑ j, affineClassShapeExpectation source target (α : Measure _) (β : Measure _)
          ambient density side (origin j) (S j) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) /
        (ambient : ℝ) - (Fintype.card J : ℝ) *
          finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
            (ambient * density * side ^ q) (C.densityClockClassKinetic Q z₀ density)
            (C.clockClassProbe Q z₀ hz₀ f) tilt / (ambient : ℝ)| ≤
        A * ((side : ℝ) ^ q * ∑ j, ((cubeMeasure (Fin q) 1) (S j)ᶜ).toReal) := by
  classical
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, bins, K, hcode, hK, hcompare⟩ :=
    C.exists_clockClass_normalized_shape_sum_bound Q z₀ hz₀ f P₀ hP₀ hmass hq
  refine ⟨source, target, hcode, ?_⟩
  intro density countBound hdensity T hT
  let factor := (density : ℝ) ^ (-(2 / (q : ℝ)))
  let B := 2 * ((bins.count : ℝ) + 1)
  let A := 2 * (density : ℝ) * (B *
    ((countBound : ℝ) ^ (2 / (q : ℝ)) * ((factor * K) * q) + T * ‖f‖))
  have hfactor : 0 ≤ factor := Real.rpow_nonneg density.coe_nonneg _
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro J _ ambient side hamb hcount origin S hS tilt htilt
  have hraw := hcompare J ambient density side hamb hdensity origin S hS tilt
  refine hraw.trans ?_
  apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg side.coe_nonneg _)
    (Finset.sum_nonneg fun j _ ↦ ENNReal.toReal_nonneg))
  apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) density.coe_nonneg)
  apply mul_le_mul_of_nonneg_left ?_ hB
  apply add_le_add
  · have hcountReal : ((ambient * density * side ^ q : ℝ≥0) : ℝ) ≤ countBound := by
      exact_mod_cast hcount
    apply mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (NNReal.coe_nonneg _) hcountReal
        (div_nonneg (by norm_num) (Nat.cast_nonneg _)))
    exact mul_nonneg (mul_nonneg hfactor hK) (Nat.cast_nonneg _)
  · exact mul_le_mul_of_nonneg_right htilt (norm_nonneg f)

end OTSelector.Reconstruction
