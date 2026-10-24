import OTSelector.Reconstruction.FinslerCoefficientCoreLabel
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.Analysis.Calculus.CompactUniformQuadraticCore
import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeedUniform

/-!
# Actual distance remainders on original population coefficient cores

The coefficient is the inverse integral of the literal original label kernel.
Fixed absolute labels make the distance independent of the center root, while
the quadratic coefficient varies continuously on the retained root core.
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

/-- The actual quadratic coefficient in the original scalar clock and fixed seed basis. -/
def populationSeedRootQuadratic (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (z : Z) (t : ℝ × ℝ) (ξ : S.covector.ker × S.covector.ker) : ℝ :=
  matrixQuadratic
    (populationSeedRootCoefficient S a (Module.finBasis ℝ S.covector.ker) (z, t))
    ((Module.finBasis ℝ S.covector.ker).equivFun (ξ.2 - ξ.1))

/-- The original distance deficit at two absolute seed labels and scalar times. -/
def populationSeedPairDeficit (S : F.CalibratedLevelSeedPatch u)
    (t : ℝ × ℝ) (y : S.covector.ker × S.covector.ker) : ℝ :=
  (F.lengthEDist (S.curve y.1 (t.1 - S.level)) (S.curve y.2 (t.2 - S.level))).toReal -
    u (S.curve y.2 (t.2 - S.level)) + u (S.curve y.1 (t.1 - S.level))

/-- Absolute neighboring labels carrying the complete fixed scalar window. -/
def coefficientWindowLabels (S : F.CalibratedLevelSeedPatch u)
    (q : RationalScalarPairWindow) : Set S.covector.ker :=
  {w | w ∈ S.labels ∧ Icc ((q.val.1 : ℝ) - S.level)
    ((q.val.2.1 : ℝ) - S.level) ⊆ S.calibrationTimes w}

/-- The actual pointwise distance germ is uniform over each compact active time-pair set. -/
def HasUniformOriginalSeedDistanceRemainder (S : F.CalibratedLevelSeedPatch u)
    (w : S.covector.ker) : Prop :=
  ∀ T : Set (ℝ × ℝ), IsCompact T →
    (∀ t ∈ T, t.1 < t.2 ∧ t.1 ∈ interior (S.calibrationTimes w) ∧
      t.2 ∈ interior (S.calibrationTimes w)) →
    ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ t ∈ T,
      ∀ ξ : S.covector.ker × S.covector.ker, ‖ξ‖ < r →
        ξ ∈ S.distanceExpansionLabels w t.1 t.2 ×ˢ S.distanceExpansionLabels w t.1 t.2 →
        ‖(F.lengthEDist (S.curve (w + ξ.1) t.1) (S.curve (w + ξ.2) t.2)).toReal -
          u (S.curve (w + ξ.2) t.2) + u (S.curve (w + ξ.1) t.1) -
          F.intrinsicLengthQuadratic (Module.finBasis ℝ S.covector.ker)
            S.curve w t.1 t.2 ξ‖ ≤ η * ‖ξ‖ ^ 2

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instRemainderMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The population coefficient is exactly the original intrinsic distance coefficient. -/
theorem populationSeedRootQuadratic_at_label (S : F.CalibratedLevelSeedPatch u)
    (w : S.labels) (t : ℝ × ℝ) (ξ : S.covector.ker × S.covector.ker) :
    populationSeedRootQuadratic S a (a (S.curve w 0)) t ξ =
      F.intrinsicLengthQuadratic (Module.finBasis ℝ S.covector.ker)
        S.curve w (t.1 - S.level) (t.2 - S.level) ξ := by
  unfold populationSeedRootQuadratic
  rw [populationSeedRootCoefficient_at_label S hF hcomplete hu ha hinj]
  rfl

variable {P : ℕ → F.CalibratedSeedWindow u}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z} [SigmaFinite lambda]

/-- The original root partition retains the actual distance expansion at its actual
inverse labels, simultaneously for all countably many original seeds. -/
theorem ae_populationSeedPieceLabel_uniform_distance
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) :
    ∀ᵐ z ∂lambda, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ lambda j,
      HasUniformOriginalSeedDistanceRemainder (P j).seed
        (populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩) := by
  have hσ (j : ℕ) : SigmaFinite (κ j) := by
    have := hκ j
    infer_instance
  apply ae_populationSeedPieceLabel_property P a κ lambda hF hcomplete hu ha hinj hσ
    (fun j ↦ HasUniformOriginalSeedDistanceRemainder (P j).seed)
  intro j
  have := hκ j
  exact ((P j).seed.ae_uniform_distance_deficit_intrinsic_quadratic hF hcomplete hu (κ j)
    (Module.finBasis ℝ (P j).seed.covector.ker)).mono fun _ hw ↦ hw.2

variable [TopologicalSpace Z] {η₀ η₁ : Measure M}
  [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

omit hF hcomplete hu ha hinj [SigmaFinite lambda] [MeasurableSpace.CountablySeparated Z]
    [T2Space M] [PreconnectedSpace M] [BorelSpace M] [BorelSpace E] in
/-- With fixed absolute endpoints, continuity follows from the actual coefficient field;
the moving center cancels out of the endpoint difference. -/
theorem OriginalPopulationCoefficientCore.continuousOn_absolute_quadratic
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (center : Z → (P C.seedIndex).seed.covector.ker)
    {t : ℝ × ℝ} (ht : t ∈ C.window.region)
    (y₁ y₂ : (P C.seedIndex).seed.covector.ker) :
    ContinuousOn (fun z ↦ populationSeedRootQuadratic (P C.seedIndex).seed a z t
      (y₁ - center z, y₂ - center z)) C.roots := by
  have hA := C.coefficient_continuous.comp
    (continuousOn_id.prodMk continuousOn_const) (fun z hz ↦ ⟨hz, ht⟩)
  convert continuous_matrixQuadratic.comp_continuousOn
    (hA.prodMk (continuousOn_const (c :=
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun (y₂ - y₁)))) using 1
  ext z
  simp only [populationSeedRootQuadratic, sub_sub_sub_cancel_right, comp_apply, id_eq]

/-- The exact original distance error, with one radius shared over the retained scalar
pair region and every original absolute label carrying that complete window. -/
def OriginalPopulationCoefficientCore.RemainderBound
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (z : Z) (η r : ℝ) : Prop :=
  ∀ t ∈ C.window.region,
    ∀ y₁ ∈ coefficientWindowLabels (P C.seedIndex).seed C.window,
    ∀ y₂ ∈ coefficientWindowLabels (P C.seedIndex).seed C.window,
    let w := populationSeedRootLabelValue (P C.seedIndex).seed a z
    ‖(y₁ - w, y₂ - w)‖ < r →
      |populationSeedPairDeficit (P C.seedIndex).seed t (y₁, y₂) -
        populationSeedRootQuadratic (P C.seedIndex).seed a z t (y₁ - w, y₂ - w)| ≤
          η * ‖(y₁ - w, y₂ - w)‖ ^ 2

omit [SigmaFinite lambda] in
/-- The original pointwise geometric expansion gives its exact scalar-window form
at the actual inverse of a retained population root. -/
theorem OriginalPopulationCoefficientCore.uniform_distance_remainder_at_root
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {z : Z} (hz : z ∈ C.roots)
    (hpoint : HasUniformOriginalSeedDistanceRemainder (P C.seedIndex).seed
      (populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z, C.roots_subset_piece hz⟩)) :
    ∀ η > 0, ∃ r > 0, C.RemainderBound z η r := by
  let S := (P C.seedIndex).seed
  let w := populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z, C.roots_subset_piece hz⟩
  let shift : ℝ × ℝ → ℝ × ℝ := fun t ↦ (t.1 - S.level, t.2 - S.level)
  have hcenter : populationSeedRootLabelValue S a z = w.val :=
    populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
      ⟨z, C.roots_subset_piece hz⟩
  have hcal := C.calibrated_label_interval hF hcomplete hu ha hinj hz
  rw [hcenter] at hcal
  have hT : IsCompact (shift '' C.window.region) :=
    C.window.isCompact_region.image (by fun_prop)
  have hactive : ∀ t ∈ shift '' C.window.region,
      t.1 < t.2 ∧ t.1 ∈ interior (S.calibrationTimes w) ∧
        t.2 ∈ interior (S.calibrationTimes w) := by
    rintro _ ⟨t, ht, rfl⟩
    have hp := C.window.region_subset ht
    exact ⟨sub_lt_sub_right hp.2.2 _,
      hcal ⟨sub_le_sub_right hp.1.1 _, sub_le_sub_right hp.1.2 _⟩,
      hcal ⟨sub_le_sub_right hp.2.1.1 _, sub_le_sub_right hp.2.1.2 _⟩⟩
  intro η hη
  obtain ⟨r, hr, hb⟩ := hpoint (shift '' C.window.region) hT hactive η hη
  refine ⟨r, hr, ?_⟩
  intro t ht y₁ hy₁ y₂ hy₂
  dsimp only
  rw [hcenter]
  intro hsmall
  let ξ : S.covector.ker × S.covector.ker := (y₁ - w.val, y₂ - w.val)
  have hp := C.window.region_subset ht
  have hallowed (y : S.covector.ker) (hy : y ∈ coefficientWindowLabels S C.window) :
      y - w.val ∈ S.distanceExpansionLabels w (shift t).1 (shift t).2 := by
    change w.val + (y - w.val) ∈ S.labels ∧
      (shift t).1 ∈ S.calibrationTimes (w.val + (y - w.val)) ∧
      (shift t).2 ∈ S.calibrationTimes (w.val + (y - w.val))
    rw [add_sub_cancel]
    exact ⟨hy.1, hy.2 ⟨sub_le_sub_right hp.1.1 _, sub_le_sub_right hp.1.2 _⟩,
      hy.2 ⟨sub_le_sub_right hp.2.1.1 _, sub_le_sub_right hp.2.1.2 _⟩⟩
  have hbound := hb (shift t) (mem_image_of_mem shift ht) ξ hsmall
    ⟨hallowed y₁ hy₁, hallowed y₂ hy₂⟩
  have hcoefficient := populationSeedRootQuadratic_at_label hF hcomplete hu ha hinj S w t ξ
  rw [populationSeedPieceLabel_root P a κ lambda C.seedIndex
    ⟨z, C.roots_subset_piece hz⟩] at hcoefficient
  rw [hcoefficient]
  simpa only [populationSeedPairDeficit, ξ, shift, w, S, add_sub_cancel, Real.norm_eq_abs]
    using hbound

variable [T2Space Z] [BorelSpace Z]

/-- The actual same-piece Haar expansion supplies the original root-law pointwise
remainders; no uniform radius or comparison selection is assumed. -/
theorem OriginalPopulationCoefficientCore.ae_uniform_distance_remainder
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) :
    ∀ᵐ z ∂lambda.restrict C.roots, ∀ η > 0, ∃ r > 0, C.RemainderBound z η r := by
  filter_upwards [ae_restrict_of_ae
    (ae_populationSeedPieceLabel_uniform_distance hF hcomplete hu ha hinj hκ),
    ae_restrict_mem C.roots_compact.measurableSet] with z hz hzC
  exact C.uniform_distance_remainder_at_root hF hcomplete hu ha hinj hzC
    (hz C.seedIndex (C.roots_subset_piece hzC))

variable [PolishSpace Z] [IsFiniteMeasure lambda]

/-- The actual population root law has a large compact subcore with one original
distance remainder radius for all retained roots, scalar pairs and allowed labels. -/
theorem OriginalPopulationCoefficientCore.exists_uniform_distance_remainder_core
    {δ ε : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hε : ε ≠ 0) :
    ∃ K ⊆ C.roots, IsCompact K ∧ lambda (C.roots \ K) < ε ∧
      ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) K ∧
      ∀ η > 0, ∃ r > 0, ∀ z ∈ K, C.RemainderBound z η r := by
  obtain ⟨H, hsubH, hH, hmassH, hcenter, _⟩ :=
    C.exists_continuous_label_core hF hcomplete hu ha hinj (ENNReal.half_pos hε).ne'
  let center := populationSeedRootLabelValue (P C.seedIndex).seed a
  let L := coefficientWindowLabels (P C.seedIndex).seed C.window
  have hp := ae_restrict_of_ae_restrict_of_subset hsubH
    (C.ae_uniform_distance_remainder hF hcomplete hu ha hinj hκ)
  have hq : ∀ t ∈ C.window.region, ∀ y₁ ∈ L, ∀ y₂ ∈ L,
      ContinuousOn (fun z ↦ populationSeedRootQuadratic (P C.seedIndex).seed a z t
        (y₁ - center z, y₂ - center z)) H := fun t ht y₁ _ y₂ _ ↦
    (C.continuousOn_absolute_quadratic center ht y₁ y₂).mono hsubH
  obtain ⟨K, hsubK, hK, hmassK, hbound⟩ :=
    exists_compact_uniform_fixedEndpoint_quadratic_remainder hH (measure_ne_top _ _)
      center hcenter L C.window.region (populationSeedPairDeficit (P C.seedIndex).seed)
      (populationSeedRootQuadratic (P C.seedIndex).seed a) hq hp (ENNReal.half_pos hε).ne'
  refine ⟨K, hsubK.trans hsubH, hK, ?_, hcenter.mono hsubK, hbound⟩
  have hdiff : C.roots \ K ⊆ (C.roots \ H) ∪ (H \ K) := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hzH, hz.2⟩
    · exact Or.inl ⟨hz.1, hzH⟩
  exact ((measure_mono hdiff).trans (measure_union_le _ _)).trans_lt
    (by simpa only [ENNReal.add_halves] using ENNReal.add_lt_add hmassH hmassK)

/-- Finite original coefficient cores admit simultaneous actual-distance refinements
with a single radius for all retained pieces and arbitrarily small total root loss. -/
theorem OriginalPopulationCoefficientCore.exists_finite_uniform_distance_refinement
    {N : ℕ} {δ ε : ℝ≥0∞}
    (C : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hε : ε ≠ 0) :
    ∃ K : Fin N → Set Z,
      lambda ((⋃ i, (C i).roots) \ ⋃ i, K i) < ε ∧
      (∀ i, K i ⊆ (C i).roots ∧ IsCompact (K i) ∧
        ContinuousOn (populationSeedRootLabelValue (P (C i).seedIndex).seed a) (K i)) ∧
      ∀ η > 0, ∃ r > 0, ∀ i, ∀ z ∈ K i, (C i).RemainderBound z η r := by
  classical
  obtain ⟨τ, hτ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Fin N)
  choose K hsub hK hmass hcont hbound using fun i ↦
    (C i).exists_uniform_distance_remainder_core hF hcomplete hu ha hinj hκ (hτ i).ne'
  refine ⟨K, ?_, fun i ↦ ⟨hsub i, hK i, hcont i⟩, ?_⟩
  · have hdiff : (⋃ i, (C i).roots) \ ⋃ i, K i ⊆ ⋃ i, (C i).roots \ K i := by
      rintro z ⟨hz, hnot⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨i, hi, fun hki ↦ hnot (mem_iUnion.mpr ⟨i, hki⟩)⟩
    exact ((measure_mono hdiff).trans (measure_iUnion_le _)).trans_lt
      ((ENNReal.tsum_le_tsum fun i ↦ (hmass i).le).trans_lt hsum)
  · intro η hη
    choose r hr hri using fun i ↦ hbound i η hη
    obtain ⟨R, hR, hRle⟩ := (isCompact_univ : IsCompact (univ : Set (Fin N))).exists_forall_le'
      (f := r) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hr i)
    refine ⟨R, hR, fun i z hz t ht y₁ hy₁ y₂ hy₂ hsmall ↦ ?_⟩
    exact hri i z hz t ht y₁ hy₁ y₂ hy₂ (hsmall.trans_le (hRle i (mem_univ i)))

end OTSelector.Reconstruction
