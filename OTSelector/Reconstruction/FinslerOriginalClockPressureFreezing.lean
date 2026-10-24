import OTSelector.Reconstruction.FinslerOriginalClockCoefficientPressureStability
import OTSelector.Reconstruction.FinslerConcreteUpperClassGeometry

/-! One finite original relative coefficient cover also controls every original
physical clock-pair probe. The construction precedes all choices of clock bins
and normalized class laws. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {lambda : Measure (ℚ → M)} [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The original manifold geometry produces one finite relative cover with
uniform physical probe oscillation on the whole retained scalar pair window.
No root regularity or probe oscillation callback remains; clock bins and
class laws may be chosen afterwards. -/
theorem PopulationLocalPressureCore.exists_original_clock_pressure_freezing_cover
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ T : (D.haar.continuous.coefficient i).RelativeRootCover ε,
      ∀ z₀ (hz₀ : z₀ ∈ T.centers),
      ∀ z (hz : z ∈ (D.haar.continuous.coefficient i).roots ∩ T.neighborhood z₀),
        ∀ p ∈ (D.haar.continuous.coefficient i).window.region,
          |originalReferenceClockProbe (D.haar.continuous.coefficient i) z hz.1 f p -
            originalReferenceClockProbe (D.haar.continuous.coefficient i) z₀ (T.subset hz₀) f p| ≤ η := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  letI : MetricSpace (ℚ → M) := TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  letI : UniformSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  obtain ⟨U,hU,hgeometry⟩ := D.exists_original_pair_geometry_neighborhoods hF hcomplete hu ha hinj
    i f f.continuous hε hη (by norm_num : (0 : ℝ) < 1)
  obtain ⟨radius,hradius,hfreeze⟩ := exists_uniform_relative_matrixQuadratic
    (C.roots_compact.prod C.window.isCompact_region) C.coefficient_continuous
    (fun q hq ↦ C.coefficient_posDef q.1 hq.1 q.2 hq.2) hε
  let V : (ℚ → M) → Set (ℚ → M) := fun z₀ ↦ U z₀ ∩ Metric.ball z₀ radius
  have hopen (z₀ : ℚ → M) : IsOpen (V z₀) := (hU z₀).1.inter Metric.isOpen_ball
  have hmem (z₀ : ℚ → M) : z₀ ∈ V z₀ := ⟨(hU z₀).2,Metric.mem_ball_self hradius⟩
  have hcover : C.roots ⊆ ⋃ z₀ ∈ C.roots, V z₀ := fun z hz ↦
    mem_iUnion_of_mem z (mem_iUnion_of_mem hz (hmem z))
  obtain ⟨centers,hsub,hfinite,hcovers⟩ := C.roots_compact.elim_finite_subcover_image
    (fun z _ ↦ hopen z) hcover
  obtain ⟨lower,hlower,hlowerBound⟩ := C.exists_quadratic_lower_bound
  let T : C.RelativeRootCover ε := {
    lowerBound := lower
    lowerBound_pos := hlower
    quadratic_lower_bound := hlowerBound
    centers := centers
    finite := hfinite
    subset := hsub
    neighborhood := V
    covers := hcovers
    open_neighborhood := fun z _ ↦ hopen z
    center_mem := fun z _ ↦ hmem z
    relative := by
      intro z₀ hz₀ z hz p hp w
      apply hfreeze (z,p) ⟨hz.1,hp⟩ (z₀,p) ⟨hsub hz₀,hp⟩
      simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg),Metric.mem_ball] using hz.2.2 }
  refine ⟨T,?_⟩
  intro z₀ hz₀ z hz p hp
  have hphysical := (hgeometry z₀ (T.subset hz₀) z ⟨hz.1,hz.2.1⟩ z ⟨hz.1,hz.2.1⟩).2.2
    p.1 hp.1.1 p.2 hp.1.2
  have heq (w : ℚ → M) (hw : w ∈ C.roots) :
      originalReferenceClockProbe C w hw f p =
        f (D.corePoint i (w,p.1),D.corePoint i (w,p.2)) := by
    dsimp only [originalReferenceClockProbe,PopulationLocalPressureCore.corePoint]
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
      ⟨w,C.roots_subset_piece hw⟩]
  rw [← heq z hz.1,← heq z₀ (T.subset hz₀)] at hphysical
  exact hphysical


/-- A single finite cover produced from the actual manifold controls every
subsequent finite clock-bin pressure model. Both thermodynamic limits and their
quantitative comparison are derived internally from the same original joint
class law; there is no pressure or probe-regularity callback. -/
theorem PopulationLocalPressureCore.exists_original_clock_pressure_stability_cover
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    let C := D.haar.continuous.coefficient i
    ∃ T : C.RelativeRootCover ε,
      ∀ z₀ (hz₀ : z₀ ∈ T.centers), ∀ z (hz : z ∈ C.roots ∩ T.neighborhood z₀),
      ∀ {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
        (P₀ : Fin Q.count → Fin Q.count → ℝ)
        (hP₀ : ∀ j k, 0 ≤ P₀ j k)
        (_hzero : ∀ j k, ¬C.clockClassAllowed Q j k → P₀ j k = 0)
        (hmass : 0 < ∑ j, ∑ k, P₀ j k)
        (_hq : 4 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker),
        let π := clockClassJointProbability P₀ hP₀ hmass
        let α := π.map measurable_fst.aemeasurable
        let β := π.map measurable_snd.aemeasurable
        let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
        ∃ p pref : ℝ → ℝ,
          (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q)
            (α : Measure _) (β : Measure _) (C.clockClassKinetic Q z)
            (C.clockClassProbe Q z hz.1 f) R t) atTop (𝓝 (p t))) ∧
          (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q)
            (α : Measure _) (β : Measure _) (C.clockClassKinetic Q z₀)
            (C.clockClassProbe Q z₀ (T.subset hz₀) f) R t) atTop (𝓝 (pref t))) ∧
          ∀ t, |p t - pref t| ≤ ε * (pref t + |t| * ‖f‖) + |t| * η := by
  obtain ⟨T,hT⟩ := D.exists_original_clock_pressure_freezing_cover
    hF hcomplete hu ha hinj i f hε hη
  refine ⟨T,?_⟩
  intro z₀ hz₀ z hz range width Q P₀ hP₀ hzero hmass hq
  exact (D.haar.continuous.coefficient i).exists_clockClassPressure_relative_stability
    Q hε.le hε1 hη.le T hz₀ hz f (hT z₀ hz₀ z hz) P₀ hP₀ hzero hmass hq

end OTSelector.Reconstruction
