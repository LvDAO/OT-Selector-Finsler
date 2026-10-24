import OTSelector.MeasureTheory.ParameterizedRestriction
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoCycleDefect
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootParameter
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftMatching

/-! # Jointly measurable relative rerooting of the whole original scene -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
local instance originalJointSceneRerootColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- Parameter-dependent homeomorphic pushforward is Borel on the actual
locally finite measure, including when the parameter is selected from it. -/
theorem measurable_localFiniteMapHomeomorph_joint
    {X Ω : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]
    (e : Ω → X ≃ₜ X) (he : Measurable (fun p : Ω × X ↦ e p.1 p.2)) :
    Measurable (fun p : Ω × LocalFiniteMeasure X ↦ localFiniteMapHomeomorph (e p.1) p.2) := by
  let κ : Kernel (Ω × LocalFiniteMeasure X) X :=
    localFiniteMeasureKernel.comap Prod.snd measurable_snd
  apply measurable_localFiniteMeasure_of_measurable_measure
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hm := κ.measurable_kernel_prodMk_left
    ((he.comp (measurable_fst.fst.prodMk measurable_snd)) hA)
  convert hm using 1
  funext p
  exact Measure.map_apply (e p.1).measurable hA

/-- Moving the root and observing its original colored input are jointly Borel. -/
theorem measurable_legalMarkedInputSceneReroot_joint (q : ℕ) :
    Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      legalMarkedInputSceneReroot q p.1 p.2) := by
  have he : Measurable (fun p : (Fin q → ℝ) × LocalFiniteMeasure (LegalMarkedPhysicalEdge q) ↦
      localFiniteMapHomeomorph (physicalSceneEdgeReroot p.1) p.2) :=
    measurable_localFiniteMapHomeomorph_joint
    (fun v : Fin q → ℝ ↦ physicalSceneEdgeReroot v)
    continuous_physicalSceneEdgeReroot_uncurry.measurable
  have hc : Measurable (fun p : (Fin q → ℝ) × LegalColoredInputPoint q ↦
      legalColoredInputPointReroot q p.1 p.2) := by
    change Measurable (fun p : (Fin q → ℝ) × LegalColoredInputPoint q ↦
      ((p.2.1.1 - p.1, p.2.1.2), p.2.2))
    fun_prop
  have hmcol : Measurable (fun p : (Fin q → ℝ) × LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      localFiniteMapHomeomorph (legalColoredInputPointReroot q p.1) p.2) :=
    measurable_localFiniteMapHomeomorph_joint
      (fun v : Fin q → ℝ ↦ legalColoredInputPointReroot q v) hc
  have h1 : Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      localFiniteMapHomeomorph (physicalSceneEdgeReroot p.1) p.2.1.1) := by
    change Measurable ((fun p : (Fin q → ℝ) × LocalFiniteMeasure (LegalMarkedPhysicalEdge q) ↦
      localFiniteMapHomeomorph (physicalSceneEdgeReroot p.1) p.2) ∘
        (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦ (p.1, p.2.1.1)))
    exact he.comp (measurable_fst.prodMk measurable_snd.fst.fst)
  have h2 : Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      localFiniteMapHomeomorph (physicalSceneEdgeReroot p.1) p.2.1.2) := by
    change Measurable ((fun p : (Fin q → ℝ) × LocalFiniteMeasure (LegalMarkedPhysicalEdge q) ↦
      localFiniteMapHomeomorph (physicalSceneEdgeReroot p.1) p.2) ∘
        (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦ (p.1, p.2.1.2)))
    exact he.comp (measurable_fst.prodMk measurable_snd.fst.snd)
  have h3 : Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      localFiniteMapHomeomorph (legalColoredInputPointReroot q p.1) p.2.2) := by
    change Measurable ((fun p : (Fin q → ℝ) × LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      localFiniteMapHomeomorph (legalColoredInputPointReroot q p.1) p.2) ∘
        (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦ (p.1, p.2.2)))
    exact hmcol.comp (measurable_fst.prodMk measurable_snd.snd)
  change Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
    ((localFiniteMapHomeomorph (physicalSceneEdgeReroot p.1) p.2.1.1,
      localFiniteMapHomeomorph (physicalSceneEdgeReroot p.1) p.2.1.2),
      localFiniteMapHomeomorph (legalColoredInputPointReroot q p.1) p.2.2))
  exact (h1.prodMk h2).prodMk h3

/-- Composition is the literal iterated pushforward of the same measure. -/
theorem localFiniteMapHomeomorph_comp
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
    [LocallyCompactSpace X] [BorelSpace X]
    (e f : X ≃ₜ X) (μ : LocalFiniteMeasure X) :
    localFiniteMapHomeomorph e (localFiniteMapHomeomorph f μ) =
      localFiniteMapHomeomorph (f.trans e) μ := by
  apply Subtype.ext
  exact Measure.map_map e.measurable f.measurable

@[simp] theorem physicalSceneEdgeReroot_add (q : ℕ) (v w : Fin q → ℝ) :
    (physicalSceneEdgeReroot w).trans (physicalSceneEdgeReroot v) =
      physicalSceneEdgeReroot (v + w) := by
  apply Homeomorph.ext
  intro e
  change (((e.1.1 - w) - v, e.1.2), ((e.2.1 - w) - v, e.2.2)) =
    ((e.1.1 - (v + w), e.1.2), (e.2.1 - (v + w), e.2.2))
  simp only [sub_sub, add_comm w v]

@[simp] theorem legalColoredInputPointReroot_add (q : ℕ) (v w : Fin q → ℝ) :
    (legalColoredInputPointReroot q w).trans (legalColoredInputPointReroot q v) =
      legalColoredInputPointReroot q (v + w) := by
  apply Homeomorph.ext
  intro x
  change (((x.1.1 - w) - v, x.1.2), x.2) = ((x.1.1 - (v + w), x.1.2), x.2)
  simp only [sub_sub, add_comm w v]

/-- The root action on both original plans and both immutable colors is exact. -/
theorem legalMarkedInputSceneReroot_add (q : ℕ) (v w : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneReroot q v (legalMarkedInputSceneReroot q w s) =
      legalMarkedInputSceneReroot q (v + w) s := by
  simp only [legalMarkedInputSceneReroot, physicalSceneReroot,
    localFiniteMapHomeomorph_comp, physicalSceneEdgeReroot_add,
    legalColoredInputPointReroot_add]

/-- Rerooting relative to the translated cell sees exactly the same scene. -/
theorem legalMarkedInputSceneReroot_relative (q : ℕ) (b v : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneReroot q (b - v) (legalMarkedInputSceneReroot q v s) =
      legalMarkedInputSceneReroot q b s := by
  rw [legalMarkedInputSceneReroot_add, sub_add_cancel]

/-- Ordinary rerooting is the constant original-clock shift. -/
theorem legalMarkedInputSceneReroot_eq_clockShift (q : ℕ) (v : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneReroot q v s =
      legalMarkedInputSceneClockShift q (fun _ ↦ ContinuousMap.const ℝ (-v)) s := by
  have he : physicalSceneEdgeReroot v =
      legalClockShiftEdge q (fun _ ↦ ContinuousMap.const ℝ (-v)) := by
    apply Homeomorph.ext
    intro e
    rfl
  have hc : legalColoredInputPointReroot q v =
      legalClockShiftColoredPoint q (fun _ ↦ ContinuousMap.const ℝ (-v)) := by
    apply Homeomorph.ext
    intro e
    rfl
  simp only [legalMarkedInputSceneReroot, physicalSceneReroot,
    legalMarkedInputSceneClockShift, he, hc]

/-- Relative roots retain the full same-original-input matching property. -/
theorem IsFullOriginalInputMatching.reroot {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (v : Fin q → ℝ) :
    IsFullOriginalInputMatching q (legalMarkedInputSceneReroot q v s) := by
  rw [legalMarkedInputSceneReroot_eq_clockShift]
  exact hs.clockShift _

/-- The original clocks and physical displacement, hence the exact signed
weighted cost, are unchanged by moving the root. -/
theorem originalWeightedEdgeCost_reroot {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (v : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q) :
    originalWeightedEdgeCost kin g t (physicalSceneEdgeReroot v e) =
      originalWeightedEdgeCost kin g t e := by
  change kin e.1.2 e.2.2 ((e.2.1 - v) - (e.1.1 - v)) + t * g e.1.2 e.2.2 = _
  rw [sub_sub_sub_cancel_right]
  rfl

end OTSelector.Reconstruction
