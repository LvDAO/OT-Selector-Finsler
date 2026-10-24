import OTSelector.Probability.StationaryKoopmanStrongContinuity
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalJointSceneReroot

/-! The complete original marked scene has a strongly continuous actual
Koopman action, including both plan coordinates and immutable input colors. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

local instance originalCurrentFaceInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace
local instance originalCurrentFacePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace
local instance originalCurrentFaceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- The full original colored input measure varies vaguely continuously in
the physical root; clocks and the immutable color remain fixed. -/
theorem continuous_legalColoredInputPointReroot_localMeasure (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) :
    Continuous (fun v : Fin q → ℝ ↦
      localFiniteMapHomeomorph (legalColoredInputPointReroot q v) μ) := by
  have hpoint : Continuous (fun p : (Fin q → ℝ) × LegalColoredInputPoint q ↦
      legalColoredInputPointReroot q p.1 p.2) := by
    change Continuous (fun p : (Fin q → ℝ) × LegalColoredInputPoint q ↦
      ((p.2.1.1 - p.1, p.2.1.2), p.2.2))
    fun_prop
  have hcancel (v : Fin q → ℝ) (x : LegalColoredInputPoint q) :
      legalColoredInputPointReroot q (-v) (legalColoredInputPointReroot q v x) = x := by
    change (((x.1.1 - v) - -v, x.1.2), x.2) = x
    simp only [sub_neg_eq_add, sub_add_cancel]
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  change Continuous (fun v ↦ LocalFiniteMeasure.testIntegral
    (localFiniteMapHomeomorph (legalColoredInputPointReroot q v) μ) f)
  have heq : (fun v ↦ LocalFiniteMeasure.testIntegral
      (localFiniteMapHomeomorph (legalColoredInputPointReroot q v) μ) f) =
      (fun v ↦ ∫ x, f (legalColoredInputPointReroot q v x) ∂(μ : Measure _)) := by
    funext v
    exact integral_map (legalColoredInputPointReroot q v).continuous.measurable.aemeasurable
      f.continuous.aestronglyMeasurable
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro v₀
  let U : Set (Fin q → ℝ) := Metric.closedBall v₀ 1
  let pull : (Fin q → ℝ) × LegalColoredInputPoint q → LegalColoredInputPoint q :=
    fun p ↦ legalColoredInputPointReroot q (-p.1) p.2
  let K := pull '' (U ×ˢ tsupport f)
  have hpull : Continuous pull := hpoint.comp (continuous_fst.neg.prodMk continuous_snd)
  have hK : IsCompact K := ((isCompact_closedBall v₀ 1).prod f.hasCompactSupport).image hpull
  have hzero : ∀ v x, v ∈ U → x ∉ K → f (legalColoredInputPointReroot q v x) = 0 := by
    intro v x hv hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx ⟨(v, legalColoredInputPointReroot q v x), ⟨hv, hmem⟩, hcancel v x⟩
  have hc : ContinuousOn (fun v : Fin q → ℝ ↦
      ∫ x, f (legalColoredInputPointReroot q v x) ∂(μ : Measure _)) U :=
    continuousOn_integral_of_compact_support hK (f.continuous.comp hpoint).continuousOn hzero
  exact hc.continuousAt (Metric.closedBall_mem_nhds _ (by norm_num))

/-- The actual joint plan/input scene is continuous in its physical reroot
parameter, including its original colored input coordinate. -/
theorem continuous_legalMarkedInputSceneReroot_parameter (q : ℕ)
    (s : LegalMarkedOptimalInputScene q) :
    Continuous (fun v : Fin q → ℝ ↦ legalMarkedInputSceneReroot q v s) :=
  (continuous_physicalSceneReroot_parameter s.1).prodMk
    (continuous_legalColoredInputPointReroot_localMeasure q s.2)

/-- Zero physical rerooting is the identity on the same complete scene. -/
theorem legalMarkedInputSceneReroot_zero (q : ℕ) :
    legalMarkedInputSceneReroot q 0 = id := by
  have he : physicalSceneEdgeReroot (0 : Fin q → ℝ) = Homeomorph.refl _ := by
    apply Homeomorph.ext
    intro e
    change ((e.1.1 - 0, e.1.2), (e.2.1 - 0, e.2.2)) = e
    simp
  have hc : legalColoredInputPointReroot q 0 = Homeomorph.refl _ := by
    apply Homeomorph.ext
    intro x
    change ((x.1.1 - 0, x.1.2), x.2) = x
    simp
  have hm (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :
      localFiniteMapHomeomorph (Homeomorph.refl _) μ = μ := by
    apply Subtype.ext
    exact Measure.map_id
  have hmcol (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) :
      localFiniteMapHomeomorph (Homeomorph.refl _) μ = μ := by
    apply Subtype.ext
    exact Measure.map_id
  funext s
  simp only [legalMarkedInputSceneReroot, physicalSceneReroot, he, hc, hm, hmcol, id_eq]

/-- Every scalar L² observable under the SAME actual stationary matching law
has a strongly continuous physical-translation orbit. Continuity is produced
on the whole L² space by dense bounded continuous readouts and isometries. -/
theorem LegalWeightedStationaryPoissonMatching.continuous_sceneL2Koopman
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (f : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) :
    Continuous (fun v : Fin q → ℝ ↦
      Lp.compMeasurePreserving (legalMarkedInputSceneReroot q v) (Q.stationary v) f) := by
  exact continuous_compMeasurePreserving_of_continuous_scene
    (Q.law : Measure _) (legalMarkedInputSceneReroot q) Q.stationary
    (continuous_legalMarkedInputSceneReroot_parameter q) f

end OTSelector.Reconstruction
