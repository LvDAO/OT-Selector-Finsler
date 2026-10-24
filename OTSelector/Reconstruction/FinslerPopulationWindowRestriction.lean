import OTSelector.Probability.ConditionalWindowRestriction
import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw

/-!
# Original conditional laws on complete calibrated windows

Each full geometric window carries the restriction of the original conditional
law, on the same population label marginal and the same fixed Haar family. The
physical density keeps its original curve, volume factor and Jacobian. Recovered
clock sections include the readout equations, so their time intervals are exact.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The complete physical window, before assigning disjoint atlas pieces. -/
def populationFullWindow (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) : Set M :=
  (P j).toManifold '' (P j).domain

/-- The exact physical density of the complete geometric window. -/
def populationFullWindowDensity (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ) : Z × ℝ → ℝ≥0∞ :=
  Function.extend
    (fun z : (P j).domain ↦ (a ((P j).toManifold z), u ((P j).toManifold z)))
    (fun z : (P j).domain ↦
      (ENNReal.ofReal (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
        ENNReal.ofReal (ρ ((P j).toManifold z) * v j ((P j).readout z))) *
          ((populationFullWindow P j).indicator (fun _ : M ↦ (1 : ℝ≥0∞)))
            ((P j).toManifold z)) (fun _ ↦ 0)

/-- The original family-time interval of a complete window. -/
def populationWindowTimeInterval (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) : Set ℝ :=
  Ioo ((P j).left : ℝ) (P j).right ∩ ball (P j).center.1 ((P j).seed.radius (P j).center)

/-- Full-window restrictions use one common original label law, with one exceptional
null set for every window in the countable atlas. -/
structure PopulationFullWindowRestrictionLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → Z) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure Z) (η : Measure M) [IsFiniteMeasure η]
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (b : Z × ℝ → M) : Prop where
  label_law : η.map a = lambda
  reference_finite : ∀ j, IsFiniteMeasure (populationWindowLabelReference P a κ j)
  density_measurable : ∀ j, Measurable (populationFullWindowDensity P a ρ v j)
  window_law : ∀ j,
    (η.restrict (populationFullWindow P j)).map (fun x ↦ (a x, u x)) =
      ((populationWindowLabelReference P a κ j).prod (volume : Measure ℝ)).withDensity
        (populationFullWindowDensity P a ρ v j)
  conditional_restriction : ∀ᵐ z ∂lambda, ∀ j,
    (populationWindowLabelReference P a κ j).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
      (condDistrib u a η z).restrict
          (labelClockWindowSection a u b (populationFullWindow P j) z) =
        (volume : Measure ℝ).withDensity (fun t ↦
          (populationWindowLabelReference P a κ j).rnDeriv lambda z *
            populationFullWindowDensity P a ρ v j (z, t))

/-- Original joint absolute continuity gives the physical law on any further actual
windows; they need not belong to the atlas used to establish absolute continuity. -/
theorem populationFullWindowRestrictionLaw_of_joint [MeasurableEq Z]
    (P : ℕ → F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFullWindowMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instFullWindowOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : ∀ j, Measure (P j).seed.covector.ker) (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hprod : ∀ j, tubeParameterMeasure (P j).seed.normalization m =
      (volume : Measure ℝ).prod (κ j))
    (ωM : Measure M) (ρ : M → ℝ)
    [IsFiniteMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)))]
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (v : ℕ → E → ℝ) (hv : ∀ j, Measurable (v j))
    (hvolume : ∀ j, let χ := extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v j y)))
    (lambda : Measure Z)
    (hlabel : (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).map a = lambda)
    (hjoint : (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).map (fun x ↦ (a x, u x)) ≪
      lambda.prod volume)
    {b : Z × ℝ → M} (hb : Measurable b)
    (hinv : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)), b (a x, u x) = x) :
    PopulationFullWindowRestrictionLaw P a κ lambda
      (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) ρ v b := by
  let _instFullWindowMetric : MetricSpace M := F.metricSpace
  let η := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))
  have hdata (j : ℕ) := by
    let _instFullWindowHaar : (κ j).IsAddHaarMeasure := hκ j
    exact (P j).map_labelClock_restrict_eq_withDensity_populationDensity hF hcomplete hu
      ha hinj horder m (κ j) (hprod j) ωM hρ hρ0 (hv j) (hvolume j)
      ((P j).measurableSet_image hF hcomplete hu) (Subset.refl _)
  have hAC : η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume := by
    rw [hlabel]
    exact hjoint
  refine ⟨hlabel, fun j ↦ (hdata j).1, fun j ↦ (hdata j).2.1,
    fun j ↦ (hdata j).2.2, ?_⟩
  apply ae_all_iff.mpr
  intro j
  let _instFullWindowReference :
      IsFiniteMeasure (populationWindowLabelReference P a κ j) := (hdata j).1
  have h := ae_condDistrib_restrict_windowSection η ha hu.continuous.measurable hb hinv hAC
    ((P j).measurableSet_image hF hcomplete hu)
    (populationWindowLabelReference P a κ j) (hdata j).2.1 (hdata j).2.2
  rw [hlabel] at h
  exact h

/-- The original constructed law yields its restriction to every full actual window. -/
theorem populationFullWindowRestrictionLaw_of_atlas [MeasurableEq Z]
    (P : ℕ → F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFullWindowMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instFullWindowOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : ∀ j, Measure (P j).seed.covector.ker) (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hprod : ∀ j, tubeParameterMeasure (P j).seed.normalization m =
      (volume : Measure ℝ).prod (κ j))
    (ωM : Measure M) (ρ : M → ℝ)
    [IsFiniteMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)))]
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (v : ℕ → E → ℝ) (hv : ∀ j, Measurable (v j))
    (hvolume : ∀ j, let χ := extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v j y)))
    (lambda : Measure Z)
    (hlaw : PopulationConditionalWindowLaw P a κ lambda
      (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) ρ v)
    {b : Z × ℝ → M} (hb : Measurable b)
    (hinv : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)), b (a x, u x) = x) :
    PopulationFullWindowRestrictionLaw P a κ lambda
      (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) ρ v b :=
  populationFullWindowRestrictionLaw_of_joint P hF hcomplete hu ha hinj horder m κ hκ
    hprod ωM ρ hρ hρ0 v hv hvolume lambda hlaw.label_law hlaw.joint_absolutelyContinuous hb hinv

omit [MeasurableSpace.CountablySeparated Z] in
/-- The physical densities in overlapping windows represent the same original
conditional measure. Their fixed label-reference factors are retained in the equality. -/
theorem PopulationFullWindowRestrictionLaw.density_eq_on_overlap [MeasurableEq Z]
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    {b : Z × ℝ → M} (hlaw : PopulationFullWindowRestrictionLaw P a κ lambda η ρ v b)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowOverlapMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (hb : Measurable b) :
    ∀ᵐ z ∂lambda, ∀ i j,
      (fun t ↦ (populationWindowLabelReference P a κ i).rnDeriv lambda z *
        populationFullWindowDensity P a ρ v i (z, t)) =ᵐ[
          volume.restrict (labelClockWindowSection a u b (populationFullWindow P i) z ∩
            labelClockWindowSection a u b (populationFullWindow P j) z)]
      (fun t ↦ (populationWindowLabelReference P a κ j).rnDeriv lambda z *
        populationFullWindowDensity P a ρ v j (z, t)) := by
  let _instWindowOverlapMetric : MetricSpace M := F.metricSpace
  filter_upwards [hlaw.conditional_restriction] with z hz
  intro i j
  have hsection (k : ℕ) :
      MeasurableSet (labelClockWindowSection a u b (populationFullWindow P k) z) :=
    (measurableSet_labelClockWindowRegion ha hu.continuous.measurable hb
      ((P k).measurableSet_image hF hcomplete hu)).preimage measurable_prodMk_left
  exact density_eq_ae_on_overlap_of_restrict_eq (condDistrib u a η z)
    (hsection i) (hsection j)
    (measurable_const.mul ((hlaw.density_measurable i).comp measurable_prodMk_left))
    (measurable_const.mul ((hlaw.density_measurable j).comp measurable_prodMk_left))
    (hz i).2 (hz j).2

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] in
/-- The full-window density keeps the original potential offset and physical curve time. -/
theorem populationFullWindowDensity_apply_clock (P : ℕ → F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFullDensityMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instFullDensityOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ) (z : (P j).domain) :
    populationFullWindowDensity P a ρ v j
        (a ((P j).seed.curve z.val.2 0), (P j).seed.level + z.val.1) =
      ENNReal.ofReal (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
        ENNReal.ofReal (ρ ((P j).seed.curve z.val.2 z.val.1) * v j ((P j).readout z)) := by
  have hreg (y : (P j).domain) : (P j).toManifold y ∈ F.potentialRegularDomain u :=
    hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
      ((P j).mapsTo_calibratedInterior hF hu y.property)
  have hq : Function.Injective (fun y : (P j).domain ↦
      (a ((P j).toManifold y), u ((P j).toManifold y))) := by
    intro x y h
    have hxy := congrArg Subtype.val (hinj (a₁ := ⟨_, hreg x⟩) (a₂ := ⟨_, hreg y⟩) h)
    exact Subtype.ext ((P j).injOn_toManifold hF hcomplete hu x.property y.property hxy)
  have hlabel := (P j).label_toManifold_eq_initial hF hcomplete hu horder z.property
  have hclock : u ((P j).toManifold z) = (P j).seed.level + z.val.1 :=
    (hF.calibrated_window_of_complete_unit_endpoints hu
      ((P j).seed.complete z.val.2 z.property.2.2.1)
      ((P j).seed.unit z.val.2 z.property.2.2.1)
      z.property.2.2.2.1 z.property.2.2.2.2).1 z.val.1
        ⟨z.property.2.1.1.le, z.property.2.1.2.le⟩
  rw [← hlabel, ← hclock]
  unfold populationFullWindowDensity
  rw [hq.extend_apply]
  have hz : (P j).toManifold z ∈ populationFullWindow P j := ⟨z, z.property, rfl⟩
  rw [indicator_of_mem hz, mul_one]
  rfl

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] in
/-- The recovered full window has exactly its original time interval on each of its seed labels. -/
theorem populationFullWindowSection_eq_clockInterval (P : ℕ → F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFullSectionMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (horder : let _instFullSectionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {b : Z × ℝ → M}
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (j : ℕ) {w : (P j).seed.covector.ker}
    (hw : w ∈ (P j).labels ∩ ball (P j).center.2 ((P j).seed.radius (P j).center)) :
    labelClockWindowSection a u b (populationFullWindow P j) (a ((P j).seed.curve w 0)) =
      (fun t : ℝ ↦ (P j).seed.level + t) '' populationWindowTimeInterval P j := by
  have hregion := labelClockWindowRegion_eq_image (C := populationFullWindow P j) (by
    rintro x ⟨z, hz, rfl⟩
    exact hinv _ (hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
      ((P j).mapsTo_calibratedInterior hF hu hz)))
  have hclock (z : ℝ × (P j).seed.covector.ker) (hz : z ∈ (P j).domain) :
      u ((P j).toManifold z) = (P j).seed.level + z.1 :=
    (hF.calibrated_window_of_complete_unit_endpoints hu
      ((P j).seed.complete z.2 hz.2.2.1) ((P j).seed.unit z.2 hz.2.2.1)
      hz.2.2.2.1 hz.2.2.2.2).1 z.1 ⟨hz.2.1.1.le, hz.2.1.2.le⟩
  unfold labelClockWindowSection
  rw [hregion]
  ext s
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, heq⟩
    refine ⟨z.1, ((Set.ext_iff.mp (P j).domain_eq_prod z).mp hz).1, ?_⟩
    exact (hclock z hz).symm.trans (congrArg Prod.snd heq)
  · rintro ⟨t, ht, rfl⟩
    have hz : (t, w) ∈ (P j).domain :=
      (Set.ext_iff.mp (P j).domain_eq_prod (t, w)).mpr ⟨ht, hw⟩
    exact ⟨(P j).toManifold (t, w), ⟨(t, w), hz, rfl⟩,
      Prod.ext ((P j).label_toManifold_eq_initial hF hcomplete hu horder hz) (hclock _ hz)⟩

end OTSelector.Reconstruction
