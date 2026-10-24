import OTSelector.Reconstruction.FinslerCoefficientCoreRemainder
import OTSelector.Reconstruction.FinslerCoefficientPressureFreezing
import OTSelector.Analysis.Calculus.UniformQuadraticLinearCoordinates

/-!
# Actual source distance remainders in the coefficient coordinates

The actual inverse label is the source. The target displacement uses the same
fixed basis as the original coefficient, with its true operator norm controlling
the radius. No orthonormality or extra remainder hypothesis is introduced.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

/-- The actual source-fixed distance error in the original coefficient basis coordinates. -/
def OriginalPopulationCoefficientCore.SourceCoordinateRemainderBound
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (z : Z) (η r : ℝ) : Prop :=
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a z
  let bW := Module.finBasis ℝ S.covector.ker
  ∀ t ∈ C.window.region, ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
    ‖v‖ < r → w + bW.equivFun.symm v ∈ coefficientWindowLabels S C.window →
      |populationSeedPairDeficit S t (w, w + bW.equivFun.symm v) -
        matrixQuadratic (C.matrix z t) v| ≤ η * ‖v‖ ^ 2

omit [BorelSpace E] [MeasurableSpace M] in
/-- The original one-Lipschitz potential makes every actual distance deficit nonnegative. -/
theorem populationSeedPairDeficit_nonneg [T2Space M] [PreconnectedSpace M]
    (hu : let _instDeficitMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (S : F.CalibratedLevelSeedPatch u) (t : ℝ × ℝ)
    (y : S.covector.ker × S.covector.ker) : 0 ≤ populationSeedPairDeficit S t y := by
  let _instDeficitMetric : MetricSpace M := F.metricSpace
  have hb := hu.dist_le_mul (S.curve y.2 (t.2 - S.level)) (S.curve y.1 (t.1 - S.level))
  have hdiff : u (S.curve y.2 (t.2 - S.level)) - u (S.curve y.1 (t.1 - S.level)) ≤
      (F.lengthEDist (S.curve y.1 (t.1 - S.level))
        (S.curve y.2 (t.2 - S.level))).toReal := by
    apply (le_abs_self _).trans
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at hb
    rw [dist_comm, F.metricSpace_dist] at hb
    exact hb
  unfold populationSeedPairDeficit
  linarith

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instCoordinateRootMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The original root label itself carries the complete retained scalar window. -/
theorem OriginalPopulationCoefficientCore.root_label_mem_window
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {z : Z} (hz : z ∈ C.roots) :
    populationSeedRootLabelValue (P C.seedIndex).seed a z ∈
      coefficientWindowLabels (P C.seedIndex).seed C.window := by
  refine ⟨?_, fun t ht ↦ interior_subset
    (C.calibrated_label_interval hF hcomplete hu ha hinj hz ht)⟩
  rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
    ⟨z, C.roots_subset_piece hz⟩]
  exact (populationSeedPieceLabel P a κ lambda C.seedIndex
    ⟨z, C.roots_subset_piece hz⟩).property

/-- The produced two-endpoint remainder gives the source-fixed estimate in exactly
the norm used by the actual matrix coefficient and its uniform lower bound. -/
theorem OriginalPopulationCoefficientCore.uniform_source_remainder_in_coordinates
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {K : Set Z} (hK : K ⊆ C.roots)
    (hrem : ∀ η > 0, ∃ r > 0, ∀ z ∈ K, C.RemainderBound z η r) :
    ∀ η > 0, ∃ r > 0, ∀ z ∈ K, C.SourceCoordinateRemainderBound z η r := by
  let S := (P C.seedIndex).seed
  let bW := Module.finBasis ℝ S.covector.ker
  let w := populationSeedRootLabelValue S a
  let error : (Z × (ℝ × ℝ)) → S.covector.ker → ℝ := fun p v ↦
    populationSeedPairDeficit S p.2 (w p.1, w p.1 + v) -
      populationSeedRootQuadratic S a p.1 p.2 (0, v)
  let allowed : (Z × (ℝ × ℝ)) → S.covector.ker → Prop :=
    fun p v ↦ w p.1 + v ∈ coefficientWindowLabels S C.window
  have hlabel : ∀ η > 0, ∃ r > 0, ∀ p ∈ K ×ˢ C.window.region, ∀ v : S.covector.ker,
      ‖v‖ < r → allowed p v → ‖error p v‖ ≤ η * ‖v‖ ^ 2 := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := hrem η hη
    refine ⟨r, hr, ?_⟩
    intro p hp v hv hvallowed
    have hsource := C.root_label_mem_window hF hcomplete hu ha hinj (hK hp.1)
    have hh := hb p.1 hp.1 p.2 hp.2 (w p.1) hsource (w p.1 + v) hvallowed
      (by simpa only [w, S, sub_self, add_sub_cancel_left, Prod.norm_def, norm_zero,
        max_eq_right (norm_nonneg v)] using hv)
    simpa only [error, w, S, sub_self, add_sub_cancel_left, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg v), Real.norm_eq_abs] using hh
  have hcoordinate := uniform_quadratic_remainder_comp_clm
    bW.equivFunL.symm.toContinuousLinearMap (K ×ˢ C.window.region) error allowed hlabel
  intro η hη
  obtain ⟨r, hr, hb⟩ := hcoordinate η hη
  refine ⟨r, hr, ?_⟩
  intro z hz t ht v hv hallowed
  have hh := hb (z, t) ⟨hz, ht⟩ v hv hallowed
  change ‖populationSeedPairDeficit S t (w z, w z + bW.equivFun.symm v) -
    populationSeedRootQuadratic S a z t (0, bW.equivFun.symm v)‖ ≤ η * ‖v‖ ^ 2 at hh
  simpa only [populationSeedRootQuadratic, sub_zero, bW, w, S, LinearEquiv.apply_symm_apply,
    Real.norm_eq_abs, OriginalPopulationCoefficientCore.matrix] using hh

/-- Fixed-basis source radii can be chosen jointly for every member of a finite
family, preserving its original root sets and actual matrix coefficients. -/
theorem OriginalPopulationCoefficientCore.uniform_finite_source_remainder_in_coordinates
    {N : ℕ} {δ : ℝ≥0∞}
    (C : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (K : Fin N → Set Z) (hK : ∀ i, K i ⊆ (C i).roots)
    (hrem : ∀ η > 0, ∃ r > 0, ∀ i, ∀ z ∈ K i, (C i).RemainderBound z η r) :
    ∀ η > 0, ∃ r > 0, ∀ i, ∀ z ∈ K i, (C i).SourceCoordinateRemainderBound z η r := by
  classical
  have hsingle (i : Fin N) := (C i).uniform_source_remainder_in_coordinates
    hF hcomplete hu ha hinj (hK i) (fun η hη ↦ by
      obtain ⟨r, hr, hb⟩ := hrem η hη
      exact ⟨r, hr, hb i⟩)
  intro η hη
  choose r hr hb using fun i ↦ hsingle i η hη
  obtain ⟨R, hR, hRle⟩ := (isCompact_univ : IsCompact (univ : Set (Fin N))).exists_forall_le'
    (f := r) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hr i)
  refine ⟨R, hR, fun i z hz t ht v hv hallowed ↦ ?_⟩
  exact hb i z hz t ht v (hv.trans_le (hRle i (mem_univ i))) hallowed

variable [T2Space Z] [BorelSpace Z] [PolishSpace Z] [IsFiniteMeasure lambda]

/-- The original geometric and root-law producers give an arbitrarily large compact
source core with a common exact-coordinate distance remainder radius. -/
theorem OriginalPopulationCoefficientCore.exists_uniform_source_coordinate_core
    {δ ε : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hε : ε ≠ 0) :
    ∃ K ⊆ C.roots, IsCompact K ∧ lambda (C.roots \ K) < ε ∧
      ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) K ∧
      ∀ η > 0, ∃ r > 0, ∀ z ∈ K, C.SourceCoordinateRemainderBound z η r := by
  obtain ⟨K, hsub, hK, hmass, hcont, hbound⟩ :=
    C.exists_uniform_distance_remainder_core hF hcomplete hu ha hinj hκ hε
  exact ⟨K, hsub, hK, hmass, hcont,
    C.uniform_source_remainder_in_coordinates hF hcomplete hu ha hinj hsub hbound⟩

end OTSelector.Reconstruction
