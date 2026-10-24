import OTSelector.Reconstruction.FinslerConcreteUpperClassShape

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

/-- Expected true affine physical finite value on the original two-color shape
laws at their actual density-weighted count intensity. -/
def affineClassShapeExpectation {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (ambient density side : ℝ≥0) (origin : Fin q → ℝ) (S : Set (Fin q → ℝ))
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ) : ℝ :=
  ∫ d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B),
    unclampedBlockLegalTilted q source target ambient kin probe tilt
      (mapBlockData (affineMarkedPoint origin side) d.1)
      (mapBlockData (affineMarkedPoint origin side) d.2)
    ∂(shapeBlockLaw q α (ambient * density * side ^ q) S).prod
      (shapeBlockLaw q β (ambient * density * side ^ q) S)

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- Summed physical microscopic shape error is bounded by its literal filling
volume times the single fixed-scale coefficient. All kernel, graph and original
class-law data come from the actual original coefficient core. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_normalized_shape_sum_bound
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
    ∃ (source target : Fin Q.count → ℝ) (rankBins : FiniteScalarBins
      (Icc (-((Q.count : ℝ) + 1)) 1) (1 / 2 : ℝ)) (K : ℝ),
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧ 0 ≤ K ∧
      ∀ (J : Type*) [Fintype J] (ambient density side : ℝ≥0), 0 < ambient → 0 < density →
      ∀ (origin : J → Fin q → ℝ) (S : J → Set (Fin q → ℝ)), (∀ j, MeasurableSet (S j)) →
      ∀ tilt : ℝ,
      let countIntensity := ambient * density * side ^ q
      let model := finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
        countIntensity (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt
      |(∑ j, affineClassShapeExpectation source target (α : Measure _) (β : Measure _)
          ambient density side (origin j) (S j) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) /
        (ambient : ℝ) - (Fintype.card J : ℝ) * model / (ambient : ℝ)| ≤
        (2 * (density : ℝ) * (2 * ((rankBins.count : ℝ) + 1) *
          ((countIntensity : ℝ) ^ (2 / (q : ℝ)) *
            (((density : ℝ) ^ (-(2 / (q : ℝ))) * K) * q) + |tilt| * ‖f‖))) *
          ((side : ℝ) ^ q * ∑ j, ((cubeMeasure (Fin q) 1) (S j)ᶜ).toReal) := by
  classical
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, rankBins, K, hcode, hK, hcompare⟩ :=
    C.exists_clockClass_affine_shape_comparison Q z₀ hz₀ f P₀ hP₀ hmass hq
  refine ⟨source, target, rankBins, K, hcode, hK, ?_⟩
  intro J _ ambient density side hamb hdensity origin S hS tilt
  let countIntensity := ambient * density * side ^ q
  let model := finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
    countIntensity (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt
  let value := fun j ↦ affineClassShapeExpectation source target (α : Measure _) (β : Measure _)
    ambient density side (origin j) (S j) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt
  let hole := fun j ↦ ((cubeMeasure (Fin q) 1) (S j)ᶜ).toReal
  let M := 2 * ((rankBins.count : ℝ) + 1) *
    ((countIntensity : ℝ) ^ (2 / (q : ℝ)) *
      (((density : ℝ) ^ (-(2 / (q : ℝ))) * K) * q) + |tilt| * ‖f‖)
  have hcell (j) : |value j - model| ≤ (2 * (countIntensity : ℝ) * hole j) * M :=
    (hcompare ambient density side hdensity (origin j) (S j) (hS j) tilt).2
  have hsum : |∑ j, (value j - model)| ≤ (2 * (countIntensity : ℝ) * M) * ∑ j, hole j := by
    calc
      _ ≤ ∑ j, |value j - model| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (2 * (countIntensity : ℝ) * hole j) * M := Finset.sum_le_sum fun j _ ↦ hcell j
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hambReal : (0 : ℝ) < ambient := by exact_mod_cast hamb
  have heq : (∑ j, value j) / (ambient : ℝ) - (Fintype.card J : ℝ) * model / (ambient : ℝ) =
      (∑ j, (value j - model)) / (ambient : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    ring
  change |(∑ j, value j) / (ambient : ℝ) - (Fintype.card J : ℝ) * model / (ambient : ℝ)| ≤ _
  rw [heq, abs_div, abs_of_pos hambReal]
  refine (div_le_div_of_nonneg_right hsum hambReal.le).trans_eq ?_
  change (2 * (countIntensity : ℝ) * M) * (∑ j, hole j) / (ambient : ℝ) =
    (2 * (density : ℝ) * M) * ((side : ℝ) ^ q * ∑ j, hole j)
  simp only [countIntensity, NNReal.coe_mul, NNReal.coe_pow]
  field_simp

end OTSelector.Reconstruction
