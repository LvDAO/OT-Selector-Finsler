import OTSelector.Reconstruction.FinslerSeedLabelReference
import OTSelector.Reconstruction.FinslerPopulationWindowClock
import OTSelector.Geometry.Finsler.SeedCalibrationSpan

/-!
# Physical conditional density on a whole active seed chart

The rational endpoint screens are removed by a countable union at a fixed original
chart center. The readout, Haar measure and label Radon--Nikodym factor are fixed
throughout this union. The resulting law reaches the actual calibrated endpoints.
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

/-- The original chart readout at one fixed center of the complete seed. -/
def populationSeedChartReadout (S : F.CalibratedLevelSeedPatch u)
    (c : S.centers) (z : ℝ × S.covector.ker) : E :=
  extChartAt 𝓘(ℝ, E) (S.curve c.val.2 c.val.1) (S.curve z.2 z.1)

/-- The original physical density in the fixed chart, independent of endpoint screens. -/
def populationSeedChartDensity (S : F.CalibratedLevelSeedPatch u)
    (ρ : M → ℝ) (v : M → E → ℝ) (c : S.centers) (w : S.covector.ker) (t : ℝ) : ℝ :=
  parameterizedJacobian (populationSeedChartReadout S c) S.normalization (t, w) *
    (ρ (S.curve w t) * v (S.curve c.val.2 c.val.1) (populationSeedChartReadout S c (t, w)))

/-- One original conditional law on the whole active part of every chart of a
fixed seed, expressed in the chosen common potential clock. -/
def PopulationSeedChartDensityLaw (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (κ : Measure S.covector.ker) (lambda : Measure Z) (η : Measure M)
    [IsFiniteMeasure η] (ρ : M → ℝ) (v : M → E → ℝ) (u₀ : ℝ) : Prop :=
  ∀ᵐ z ∂lambda, (populationSeedLabelReference S a κ).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
    ∀ (c : S.centers) (w : S.covector.ker), w ∈ S.labels → a (S.curve w 0) = z →
      w ∈ ball c.val.2 (S.radius c) →
      let U := (fun q : ℝ ↦ q + u₀ - S.level) ⁻¹'
        (interior (S.calibrationTimes w) ∩ ball c.val.1 (S.radius c))
      ((condDistrib u a η z).map (fun s : ℝ ↦ s - u₀)).restrict U =
        (volume.restrict U).withDensity (fun q ↦ ENNReal.ofReal
          (((populationSeedLabelReference S a κ).rnDeriv lambda z).toReal *
            populationSeedChartDensity S ρ v c w (q + u₀ - S.level)))

/-- The entire active part of a fixed original chart has the same exact conditional
density. The countable rational endpoint screens have been removed from the law. -/
theorem ae_populationSeedChart_conditional_density [MeasurableEq Z]
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedDensityMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instSeedDensityOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure]
    (hprod : tubeParameterMeasure S.normalization m = (volume : Measure ℝ).prod κ)
    (ωM : Measure M) (ρ : M → ℝ)
    [IsFiniteMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)))]
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (v : M → E → ℝ) (hv : ∀ old, Measurable (v old))
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    (lambda : Measure Z)
    (hlabel : (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).map a = lambda)
    (hjoint : (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).map (fun x ↦ (a x, u x)) ≪
      lambda.prod volume)
    {b : Z × ℝ → M} (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hreg : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)),
      x ∈ F.potentialRegularDomain u) (u₀ : ℝ) :
    PopulationSeedChartDensityLaw S a κ lambda
      (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) ρ v u₀ := by
  unfold PopulationSeedChartDensityLaw
  have hLabelFinite : IsFiniteMeasure lambda := hlabel ▸ inferInstance
  have hbinv : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)), b (a x, u x) = x :=
    hreg.mono (fun x hx ↦ hinv x hx)
  have hseed : SigmaFinite (populationSeedLabelReference S a κ) :=
    sigmaFinite_labelReferenceOn κ S.labels_measurable
      (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj)
  have hlocal (k : S.RationalWindowIndex) := by
    let P := S.rationalWindow k
    let vP := v (P.toManifold P.center)
    have hfull := populationFullWindowRestrictionLaw_of_joint (fun _ ↦ P) hF hcomplete hu
      ha hinj horder m (fun _ ↦ κ) (fun _ ↦ inferInstance) (fun _ ↦ hprod)
      ωM ρ hρ hρ0 (fun _ ↦ vP) (fun _ ↦ hv _) (fun _ ↦ hvolume _) lambda
      hlabel hjoint hb hbinv
    exact (ae_populationWindow_rnDeriv_eq_seed P hF hcomplete hu ha hinj κ lambda).and
      (hfull.clockShift_restrict_eq_ofReal hF hcomplete hu hinj horder hinv u₀)
  have hall := ae_all_iff.mpr hlocal
  filter_upwards [hall, (populationSeedLabelReference S a κ).rnDeriv_lt_top lambda]
    with z hz hzfinite
  refine ⟨hzfinite, ?_⟩
  intro c w hw hwz hwball
  let I : ({l : ℚ // l < 0} × {r : ℚ // 0 < r}) → Set ℝ :=
    fun lr ↦ {q | (q + u₀ - S.level, w) ∈ (S.rationalWindow (lr, c)).domain}
  have hI (lr : {l : ℚ // l < 0} × {r : ℚ // 0 < r}) : MeasurableSet (I lr) :=
    ((S.rationalWindow (lr, c)).measurableSet_domain hu).preimage
      (((measurable_id.add_const u₀).sub_const (S.level : ℝ)).prodMk measurable_const)
  have hcover : (⋃ lr, I lr) = (fun q : ℝ ↦ q + u₀ - S.level) ⁻¹'
      (interior (S.calibrationTimes w) ∩ ball c.val.1 (S.radius c)) := by
    rw [← S.iUnion_rationalWindow_fixedCenter_timeDomain hF hu c hw hwball,
      preimage_iUnion]
    rfl
  apply restrict_eq_withDensity_of_countable_cover _ volume hI hcover
  intro lr
  let P := S.rationalWindow (lr, c)
  by_cases hwL : w ∈ P.labels ∩ ball P.center.2 (P.seed.radius P.center)
  · have hdensity := ((hz (lr, c)).2 0).2 w hwL hwz (I lr) (hI lr) (by
      intro q hq
      exact ((Set.ext_iff.mp P.domain_eq_prod (q + u₀ - S.level, w)).mp hq).1)
    have hRN := (hz (lr, c)).1.2 w hwL hwz
    rw [hRN] at hdensity
    exact hdensity
  · have hempty : I lr = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact hwL (((Set.ext_iff.mp P.domain_eq_prod (q + u₀ - S.level, w)).mp hq).2)
    simp [hempty]

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [BorelSpace M] [MeasurableSpace.CountablySeparated Z] in
/-- Any measurable subinterval of the whole active chart retains the same original
conditional law and the same full-seed label factor, including endpoint neighborhoods. -/
theorem PopulationSeedChartDensityLaw.restrict
    {S : F.CalibratedLevelSeedPatch u} {a : M → Z} {κ : Measure S.covector.ker}
    {lambda : Measure Z} {η : Measure M} [IsFiniteMeasure η]
    {ρ : M → ℝ} {v : M → E → ℝ} {u₀ : ℝ}
    (hlaw : PopulationSeedChartDensityLaw S a κ lambda η ρ v u₀) :
    ∀ᵐ z ∂lambda, (populationSeedLabelReference S a κ).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
      ∀ (c : S.centers) (w : S.covector.ker), w ∈ S.labels → a (S.curve w 0) = z →
        w ∈ ball c.val.2 (S.radius c) →
        ∀ K : Set ℝ, MeasurableSet K →
          (∀ q ∈ K, q + u₀ - S.level ∈
            interior (S.calibrationTimes w) ∩ ball c.val.1 (S.radius c)) →
          ((condDistrib u a η z).map (fun s : ℝ ↦ s - u₀)).restrict K =
            (volume.restrict K).withDensity (fun q ↦ ENNReal.ofReal
              (((populationSeedLabelReference S a κ).rnDeriv lambda z).toReal *
                populationSeedChartDensity S ρ v c w (q + u₀ - S.level))) := by
  filter_upwards [hlaw] with z hz
  refine ⟨hz.1, ?_⟩
  intro c w hw hwz hwball K hK hKU
  have h := congrArg (fun μ : Measure ℝ ↦ μ.restrict K) (hz.2 c w hw hwz hwball)
  have hsub : K ⊆ (fun q : ℝ ↦ q + u₀ - S.level) ⁻¹'
      (interior (S.calibrationTimes w) ∩ ball c.val.1 (S.radius c)) := hKU
  rw [Measure.restrict_restrict_of_subset hsub, restrict_withDensity hK,
    Measure.restrict_restrict_of_subset hsub] at h
  exact h

end OTSelector.Reconstruction
