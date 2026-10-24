import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellMass
import OTSelector.Reconstruction.FinslerConcreteUpperClassModel
import OTSelector.Analysis.Normed.BallCubeEmbedding

/-! Actual compact coefficient labels in an integer affine macrobox. Their
physical quadratic kernel changes by the exact squared side, before any grid or
sample is chosen; no coordinate clamp is used. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- Strictly bounded original basis coordinates lie in the open unit cube after
the actual affine normalization, so no boundary deletion is needed. -/
theorem labelCubeCoordinates_mem_openUnitCube
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {q : ℕ}
    (bW : Module.Basis (Fin q) ℝ W) {R : ℝ} (hR : 0 < R) {w : W}
    (hw : ‖bW.equivFun w‖ < R) : labelCubeCoordinates bW R w ∈ unitCube q := by
  intro l _
  have hl := (norm_le_pi_norm (bW.equivFun w) l).trans_lt hw
  rw [Real.norm_eq_abs, abs_lt] at hl
  change 0 < (bW.equivFun w l + R) / (2 * R) ∧
    (bW.equivFun w l + R) / (2 * R) < 1
  exact ⟨div_pos (by linarith) (by positivity),
    (div_lt_iff₀ (by positivity : 0 < 2 * R)).mpr (by linarith)⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The stored original compact coefficient labels produce a fixed integer
macrobox, a measurable unclamped unit-cube observation on every original root,
and the exact physical squared-side kernel. All choices precede the sample size. -/
theorem PopulationLocalPressureCore.exists_original_clockClass_macrobox_model
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : ℚ → M) (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let root := populationSeedRootLabelValue Seed a
    let bW := Module.finBasis ℝ Seed.covector.ker
    let q := Module.finrank ℝ Seed.covector.ker
    ∃ R : ℕ, 0 < R ∧
      Measurable (fun z ↦ labelCubeCoordinates bW (R : ℝ) (root z)) ∧
      (∀ z ∈ C.roots, labelCubeCoordinates bW (R : ℝ) (root z) ∈ unitCube q) ∧
      (∀ w w' : Seed.covector.ker, ∀ j k : Fin Q.count,
        C.clockClassKinetic Q z₀ j k (bW.equivFun (w' - w)) =
          (2 * (R : ℝ)) ^ 2 * C.clockClassKinetic Q z₀ j k
            (labelCubeCoordinates bW R w' - labelCubeCoordinates bW R w)) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ j k (v : Fin q → ℝ),
        |(2 * (R : ℝ)) ^ 2 * C.clockClassKinetic Q z₀ j k v| ≤ K * ∑ l, v l ^ 2 := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let root := populationSeedRootLabelValue Seed a
  let bW := Module.finBasis ℝ Seed.covector.ker
  have hcompact : IsCompact (bW.equivFunL '' (root '' C.roots)) := by
    have h := (D.haar.intensity i).compact_labels.image bW.equivFunL.continuous
    simpa only [D.haar.intensity_roots i] using h
  obtain ⟨B, hB, hnorm⟩ := hcompact.isBounded.exists_pos_norm_lt
  let R := Nat.ceil B + 1
  have hR : 0 < R := by dsimp [R]; omega
  have hRReal : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hlarge : B < (R : ℝ) := by
    have h1 : B < (Nat.ceil B : ℝ) + 1 := (Nat.le_ceil B).trans_lt (lt_add_one _)
    simpa only [R, Nat.cast_add, Nat.cast_one] using h1
  refine ⟨R, hR, ?_, ?_, ?_, ?_⟩
  · exact (continuous_labelCubeCoordinates bW (R : ℝ)).measurable.comp
      (measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj)
  · intro z hz
    apply labelCubeCoordinates_mem_openUnitCube bW hRReal
    exact (hnorm _ (mem_image_of_mem bW.equivFunL (mem_image_of_mem root hz))).trans hlarge
  · intro w w' j k
    rw [← labelCubeCoordinates_sub bW hRReal w' w]
    exact C.clockClassKinetic_homogeneous Q z₀ j k (2 * (R : ℝ)) _
  · obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
    refine ⟨(2 * (R : ℝ)) ^ 2 * K, mul_nonneg (sq_nonneg _) hK, ?_⟩
    intro j k vv
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hbound j k vv) (sq_nonneg _)).trans_eq (by ring)

end OTSelector.Reconstruction
