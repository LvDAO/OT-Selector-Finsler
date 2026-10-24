import OTSelector.Reconstruction.FinslerOriginalScalarRangeClockModel
import OTSelector.Reconstruction.FinslerOriginalWindowGeometryConvergence
import OTSelector.Reconstruction.FinslerOriginalCanonicalClockPressure

/-! The original compact window extends its actual continuous coefficient and
physical probe to measurable global mark kernels. On original supported legal
pairs these extensions have exactly the original cost and probe. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The original actual coefficient, with zero outside its compact clock
window. This is a global extension used only with the exact retained laws. -/
def OriginalPopulationCoefficientCore.originalWindowClockKinetic
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} (z : Z) (x y : range)
    (v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) : ℝ :=
  if (x.val,y.val) ∈ C.window.region then matrixQuadratic (C.matrix z (x.val,y.val)) v else 0

/-- The same original window extension of the actual physical probe. -/
def OriginalPopulationCoefficientCore.originalWindowClockProbe
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} (z : Z) (hz : z ∈ C.roots) (f : M × M → ℝ) (x y : range) : ℝ :=
  if (x.val,y.val) ∈ C.window.region then C.originalRangeClockProbe z hz f x y else 0

/-- The original compact window produces one uniform kinetic growth constant
for every original root, before any original mark law is selected. -/
theorem OriginalPopulationCoefficientCore.exists_originalWindowClockKinetic_bound
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {range : Set ℝ} :
    ∃ K ≥ 0, ∀ z ∈ C.roots, ∀ x y : range, ∀ v,
      |C.originalWindowClockKinetic z x y v| ≤ K * ∑ l, v l ^ 2 := by
  obtain ⟨K,hK,hbound⟩ := exists_compact_matrixQuadratic_sum_bound
    (C.roots_compact.prod C.window.isCompact_region) C.coefficient_continuous
  refine ⟨K,hK,?_⟩
  intro z hz x y v
  by_cases hp : (x.val,y.val) ∈ C.window.region
  · have hb := hbound (z,(x.val,y.val)) ⟨hz,hp⟩ v
    change |matrixQuadratic (C.matrix z (x.val,y.val)) v| ≤ K * ∑ l, v l ^ 2 at hb
    simpa only [originalWindowClockKinetic,hp,↓reduceIte] using hb
  · simp only [originalWindowClockKinetic,hp,↓reduceIte,abs_zero]
    exact mul_nonneg hK (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Positivity of the actual original coefficient supplies nonnegative
kinetic energy of its original window extension. -/
theorem OriginalPopulationCoefficientCore.originalWindowClockKinetic_nonneg
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {range : Set ℝ}
    (z : Z) (hz : z ∈ C.roots) (x y : range) (v) :
    0 ≤ C.originalWindowClockKinetic z x y v := by
  by_cases hp : (x.val,y.val) ∈ C.window.region
  · have hn := (C.coefficient_posDef z hz _ hp).posSemidef.dotProduct_mulVec_nonneg v
    change 0 ≤ dotProduct (star v) ((C.matrix z (x.val,y.val)).mulVec v) at hn
    simp only [star_trivial] at hn
    simp only [originalWindowClockKinetic,hp,↓reduceIte,matrixQuadratic]
    exact mul_nonneg (by norm_num) hn
  · simp only [originalWindowClockKinetic,hp,↓reduceIte,le_refl]

/-- The exact original window extension is still a quadratic kernel. -/
theorem OriginalPopulationCoefficientCore.originalWindowClockKinetic_homogeneous
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {range : Set ℝ}
    (z : Z) (x y : range) (c : ℝ) (v) :
    C.originalWindowClockKinetic z x y (c • v) = c ^ 2 * C.originalWindowClockKinetic z x y v := by
  dsimp only [originalWindowClockKinetic]
  split_ifs
  · exact matrixQuadratic_smul _ _ _
  · exact (mul_zero _).symm

/-- The actual original physical probe has its unchanged global norm bound. -/
theorem OriginalPopulationCoefficientCore.originalWindowClockProbe_abs_le
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {range : Set ℝ}
    (z : Z) (hz : z ∈ C.roots) (f : M × M →ᵇ ℝ) (x y : range) :
    |C.originalWindowClockProbe z hz f x y| ≤ ‖f‖ := by
  dsimp only [originalWindowClockProbe]
  split_ifs
  · exact C.originalRangeClockProbe_abs_le z hz f x y
  · simpa only [abs_zero] using norm_nonneg f

/-- The original window kinetic extension is jointly measurable. -/
theorem OriginalPopulationCoefficientCore.measurable_originalWindowClockKinetic
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {range : Set ℝ} (z : Z) :
    Measurable (Function.uncurry (fun p : range × range ↦ C.originalWindowClockKinetic z p.1 p.2)) := by
  let Ω := (range × range) × (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
  have hmark : Measurable (fun x : Ω ↦ (x.1.1.val,x.1.2.val)) := by fun_prop
  have hmask : MeasurableSet {x : Ω | (x.1.1.val,x.1.2.val) ∈ C.window.region} :=
    C.window.isCompact_region.isClosed.measurableSet.preimage hmark
  have hraw : Measurable (fun x : Ω ↦ matrixQuadratic (C.matrix z (x.1.1.val,x.1.2.val)) x.2) :=
    C.measurable_quadratic_cost hF hcomplete hu ha hinj measurable_const hmark measurable_snd
  exact hraw.ite hmask measurable_const

/-- The same original physical window probe is measurable. -/
theorem OriginalPopulationCoefficientCore.measurable_originalWindowClockProbe
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex) {range : Set ℝ}
    (z : Z) (hz : z ∈ C.roots) (f : M × M →ᵇ ℝ) :
    Measurable (Function.uncurry (C.originalWindowClockProbe (range := range) z hz f)) := by
  have hmask : MeasurableSet {p : range × range | (p.1.val,p.2.val) ∈ C.window.region} :=
    C.window.isCompact_region.isClosed.measurableSet.preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe)
  exact (C.measurable_originalRangeClockProbe hF z hz f).ite hmask measurable_const

/-- On actual original supported legal pairs, the window extension has
exactly the actual continuous coefficient and physical probe. -/
theorem OriginalPopulationCoefficientCore.window_clock_pressure_eq_canonical_original
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {gap : ℝ} (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (z : Z) (hz : z ∈ C.roots) (f : M × M →ᵇ ℝ)
    (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|) (r : ℝ≥0) (t : ℝ) :
    legalMarkedPressure (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β r
      (C.originalWindowClockKinetic z) (C.originalWindowClockProbe z hz f) t =
    legalMarkedPressure (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β r
      (fun x y v ↦ matrixQuadratic (C.matrix z (x.val,y.val)) v)
      (C.originalRangeClockProbe z hz f) t := by
  apply legalMarkedPressure_congr_of_ae_on_legal
  filter_upwards [ae_fst_of_ae hα,ae_snd_of_ae hβ,hsep] with p hpα hpβ hpsep
  intro hforward
  have hp : (p.1.val,p.2.val) ∈ C.window.region := by
    refine ⟨⟨hpα,hpβ⟩,?_⟩
    exact hwindowGap.trans (by simpa only [abs_of_pos (sub_pos.mpr hforward)] using hpsep)
  simp [originalWindowClockKinetic,originalWindowClockProbe,hp]

/-- The exact original canonical identification also holds before every real
spatial scale limit. -/
theorem OriginalPopulationCoefficientCore.window_clock_scalePressure_eq_canonical_original
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {gap : ℝ} (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (z : Z) (hz : z ∈ C.roots) (f : M × M →ᵇ ℝ)
    (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|) (R : ℝ) (t : ℝ) :
    legalMarkedScalePressure (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β
      (C.originalWindowClockKinetic z) (C.originalWindowClockProbe z hz f) R t =
    legalMarkedScalePressure (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β
      (fun x y v ↦ matrixQuadratic (C.matrix z (x.val,y.val)) v)
      (C.originalRangeClockProbe z hz f) R t := by
  by_cases hR : 0 < R
  · simp only [legalMarkedScalePressure,hR,↓reduceIte]
    rw [C.window_clock_pressure_eq_canonical_original hwindowGap z hz f α β hα hβ hsep]
  · simp only [legalMarkedScalePressure,hR,↓reduceIte]

end OTSelector.Reconstruction
