import OTSelector.Reconstruction.FinslerPopulationWindowRestriction
import OTSelector.Probability.ConditionalClockShiftNormalization

/-!
# The original restricted conditional law in actual family time

The complete geometric window has the original interval and potential offset.
Subtracting this offset gives its exact physical density in family time. The
finite label Radon--Nikodym factor remains constant along that same curve.
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

/-- The physical Jacobian density along one actual seed curve, before changing label reference. -/
def populationWindowPhysicalDensity (P : ℕ → F.CalibratedSeedWindow u)
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ) (w : (P j).seed.covector.ker) (t : ℝ) : ℝ :=
  parameterizedJacobian (P j).readout (P j).seed.normalization (t, w) *
    (ρ ((P j).seed.curve w t) * v j ((P j).readout (t, w)))

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] in
/-- The full-window section is exactly its interval indicator times the physical density. -/
theorem populationFullWindowDensity_clock_section (P : ℕ → F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPhysicalSectionMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instPhysicalSectionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ) {w : (P j).seed.covector.ker}
    (hw : w ∈ (P j).labels ∩ ball (P j).center.2 ((P j).seed.radius (P j).center)) :
    (fun t ↦ populationFullWindowDensity P a ρ v j
      (a ((P j).seed.curve w 0), t + (P j).seed.level)) =
        (populationWindowTimeInterval P j).indicator
          (fun t ↦ ENNReal.ofReal (populationWindowPhysicalDensity P ρ v j w t)) := by
  classical
  funext t
  by_cases ht : t ∈ populationWindowTimeInterval P j
  · have hz : (t, w) ∈ (P j).domain :=
      (Set.ext_iff.mp (P j).domain_eq_prod (t, w)).mpr ⟨ht, hw⟩
    rw [indicator_of_mem ht]
    have h := populationFullWindowDensity_apply_clock P hF hcomplete hu hinj horder ρ v j ⟨_, hz⟩
    rw [add_comm t]
    rw [h]
    exact (ENNReal.ofReal_mul (show 0 ≤ parameterizedJacobian (P j).readout
      (P j).seed.normalization (t, w) from abs_nonneg _)).symm
  · rw [indicator_of_notMem ht]
    unfold populationFullWindowDensity
    apply Function.extend_apply'
    rintro ⟨z, heq⟩
    have hclock : u ((P j).toManifold z) = (P j).seed.level + z.val.1 :=
      (hF.calibrated_window_of_complete_unit_endpoints hu
        ((P j).seed.complete z.val.2 z.property.2.2.1)
        ((P j).seed.unit z.val.2 z.property.2.2.1)
        z.property.2.2.2.1 z.property.2.2.2.2).1 z.val.1
          ⟨z.property.2.1.1.le, z.property.2.1.2.le⟩
    have htime : z.val.1 = t := by
      have h := hclock.symm.trans (congrArg Prod.snd heq)
      linarith
    apply ht
    rw [← htime]
    exact ((Set.ext_iff.mp (P j).domain_eq_prod z.val).mp z.property).1

omit [BorelSpace E] [BorelSpace M] [MeasurableSpace.CountablySeparated Z] in
/-- The full original conditional restriction, in the original family clock, has
the physical density times one finite label-reference factor. -/
theorem PopulationFullWindowRestrictionLaw.clockShift_eq_restrict_ofReal
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    {b : Z × ℝ → M} (hlaw : PopulationFullWindowRestrictionLaw P a κ lambda η ρ v b)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowShiftMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instWindowShiftOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∀ᵐ z ∂lambda, ∀ j, (populationWindowLabelReference P a κ j).rnDeriv lambda z <
        (∞ : ℝ≥0∞) ∧
      ∀ w ∈ (P j).labels ∩ ball (P j).center.2 ((P j).seed.radius (P j).center),
        a ((P j).seed.curve w 0) = z →
        ((condDistrib u a η z).restrict
          (labelClockWindowSection a u b (populationFullWindow P j) z)).map
            (fun s : ℝ ↦ s - (P j).seed.level) =
          (volume.restrict (populationWindowTimeInterval P j)).withDensity
            (fun t ↦ ENNReal.ofReal
              (((populationWindowLabelReference P a κ j).rnDeriv lambda z).toReal *
                populationWindowPhysicalDensity P ρ v j w t)) := by
  filter_upwards [hlaw.conditional_restriction] with z hz
  intro j
  refine ⟨(hz j).1, ?_⟩
  intro w hw hwz
  rw [(hz j).2, map_withDensity_sub_clock]
  have hI : MeasurableSet (populationWindowTimeInterval P j) :=
    isOpen_Ioo.measurableSet.inter isOpen_ball.measurableSet
  rw [← withDensity_indicator hI]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hsection := congrFun
    (populationFullWindowDensity_clock_section P hF hcomplete hu hinj horder ρ v j hw) t
  rw [hwz] at hsection
  dsimp only
  rw [hsection]
  by_cases ht : t ∈ populationWindowTimeInterval P j
  · simp only [indicator_of_mem ht]
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hz j).1.ne]
  · simp only [indicator_of_notMem ht, mul_zero]

omit [BorelSpace E] [BorelSpace M] [MeasurableSpace.CountablySeparated Z] in
/-- Every subwindow uses the same original conditional measure in any fixed clock.
The physical curve is evaluated at its own seed time, retaining its potential offset. -/
theorem PopulationFullWindowRestrictionLaw.clockShift_restrict_eq_ofReal
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    {b : Z × ℝ → M} (hlaw : PopulationFullWindowRestrictionLaw P a κ lambda η ρ v b)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFixedClockMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instFixedClockOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x) (u₀ : ℝ) :
    ∀ᵐ z ∂lambda, ∀ j, (populationWindowLabelReference P a κ j).rnDeriv lambda z <
        (∞ : ℝ≥0∞) ∧
      ∀ w ∈ (P j).labels ∩ ball (P j).center.2 ((P j).seed.radius (P j).center),
        a ((P j).seed.curve w 0) = z →
        ∀ K : Set ℝ, MeasurableSet K →
          (∀ q ∈ K, q + u₀ - (P j).seed.level ∈ populationWindowTimeInterval P j) →
          ((condDistrib u a η z).map (fun s : ℝ ↦ s - u₀)).restrict K =
            (volume.restrict K).withDensity (fun q ↦ ENNReal.ofReal
              (((populationWindowLabelReference P a κ j).rnDeriv lambda z).toReal *
                populationWindowPhysicalDensity P ρ v j w (q + u₀ - (P j).seed.level))) := by
  filter_upwards [hlaw.conditional_restriction] with z hz
  intro j
  refine ⟨(hz j).1, ?_⟩
  intro w hw hwz K hK hKI
  have hsection := populationFullWindowSection_eq_clockInterval P hF hcomplete hu
    horder hinv j hw
  rw [hwz] at hsection
  have hsub : (fun s : ℝ ↦ s - u₀) ⁻¹' K ⊆
      labelClockWindowSection a u b (populationFullWindow P j) z := by
    intro s hs
    rw [hsection]
    refine ⟨s - (P j).seed.level, ?_, by ring⟩
    simpa only [sub_add_cancel] using hKI (s - u₀) hs
  have hshift : Measurable (fun s : ℝ ↦ s - u₀) := measurable_id.sub_const u₀
  rw [Measure.restrict_map hshift hK,
    ← Measure.restrict_restrict_of_subset hsub, (hz j).2,
    ← Measure.restrict_map hshift hK,
    map_withDensity_sub_clock, restrict_withDensity hK]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hK] with q hq
  have hprofile := congrFun
    (populationFullWindowDensity_clock_section P hF hcomplete hu hinj horder ρ v j hw)
      (q + u₀ - (P j).seed.level)
  rw [hwz, sub_add_cancel, indicator_of_mem (hKI q hq)] at hprofile
  rw [hprofile, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (hz j).1.ne]

end OTSelector.Reconstruction
