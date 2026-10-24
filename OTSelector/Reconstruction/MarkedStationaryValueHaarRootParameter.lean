import OTSelector.Reconstruction.MarkedStationaryValueHaarRootPhysicalScene

/-! Continuity in the physical multidimensional reroot parameter for each
actual locally finite diffuse scene. Compact tests use one actual compact
support for every parameter in a fixed compact neighborhood. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The actual endpoint translation is jointly continuous before integration. -/
theorem continuous_physicalSceneEdgeReroot_uncurry :
    Continuous (fun p : (ι → ℝ) × (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦
      physicalSceneEdgeReroot p.1 p.2) := by
  change Continuous (fun p : (ι → ℝ) × (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦
    ((p.2.1.1 - p.1, p.2.1.2), (p.2.2.1 - p.1, p.2.2.2)))
  exact ((continuous_snd.fst.fst.sub continuous_fst).prodMk continuous_snd.fst.snd).prodMk
    ((continuous_snd.snd.fst.sub continuous_fst).prodMk continuous_snd.snd.snd)

omit [Fintype ι] in
@[simp]
theorem physicalSceneEdgeReroot_neg_cancel (v : ι → ℝ)
    (e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :
    physicalSceneEdgeReroot (-v) (physicalSceneEdgeReroot v e) = e := by
  change (((e.1.1 - v) - -v, e.1.2), ((e.2.1 - v) - -v, e.2.2)) = e
  simp only [sub_neg_eq_add, sub_add_cancel]

/-- Integrating a compact test after translating the actual measure varies
continuously with the root parameter. No moment or global mass bound is needed. -/
theorem continuous_integral_physicalSceneEdgeReroot
    (μ : LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (f : C_c((((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)), ℝ)) :
    Continuous (fun v : ι → ℝ ↦ ∫ e, f (physicalSceneEdgeReroot v e) ∂(μ : Measure _)) := by
  apply continuous_iff_continuousAt.mpr
  intro v₀
  let U : Set (ι → ℝ) := Metric.closedBall v₀ 1
  let pull : (ι → ℝ) × (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) →
      (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) := fun p ↦ physicalSceneEdgeReroot (-p.1) p.2
  have hpull : Continuous pull := continuous_physicalSceneEdgeReroot_uncurry.comp
    (continuous_fst.neg.prodMk continuous_snd)
  let K := pull '' (U ×ˢ tsupport f)
  have hU : IsCompact U := isCompact_closedBall v₀ 1
  have hK : IsCompact K := (hU.prod f.hasCompactSupport).image hpull
  have hfs : ∀ v e, v ∈ U → e ∉ K → f (physicalSceneEdgeReroot v e) = 0 := by
    intro v e hv he
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply he
    exact ⟨(v, physicalSceneEdgeReroot v e), ⟨hv, hmem⟩,
      physicalSceneEdgeReroot_neg_cancel v e⟩
  have hc : ContinuousOn (fun v : ι → ℝ ↦
      ∫ e, f (physicalSceneEdgeReroot v e) ∂(μ : Measure _)) U :=
    continuousOn_integral_of_compact_support
      (f := fun v e ↦ f (physicalSceneEdgeReroot v e)) (μ := (μ : Measure _)) hK
      (f.continuous.comp continuous_physicalSceneEdgeReroot_uncurry).continuousOn hfs
  exact hc.continuousAt (Metric.closedBall_mem_nhds _ (by norm_num))

/-- The actual physical reroot is continuous in its root parameter for each
fixed diffuse locally finite plan. -/
theorem continuous_physicalSceneReroot_localMeasure
    (μ : LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :
    Continuous (fun v : ι → ℝ ↦ localFiniteMapHomeomorph (physicalSceneEdgeReroot v) μ) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  change Continuous (fun v ↦ LocalFiniteMeasure.testIntegral
    (localFiniteMapHomeomorph (physicalSceneEdgeReroot v) μ) f)
  have heq : (fun v ↦ LocalFiniteMeasure.testIntegral
      (localFiniteMapHomeomorph (physicalSceneEdgeReroot v) μ) f) =
      (fun v ↦ ∫ e, f (physicalSceneEdgeReroot v e) ∂(μ : Measure _)) := by
    funext v
    exact integral_map (physicalSceneEdgeReroot v).continuous.measurable.aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  rw [heq]
  exact continuous_integral_physicalSceneEdgeReroot μ f

/-- Spatial parameter continuity holds for both actual original plans. -/
theorem continuous_physicalSceneReroot_parameter
    (scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :
    Continuous (fun v : ι → ℝ ↦ physicalSceneReroot v scene) :=
  (continuous_physicalSceneReroot_localMeasure scene.1).prodMk
    (continuous_physicalSceneReroot_localMeasure scene.2)

end OTSelector.Reconstruction
