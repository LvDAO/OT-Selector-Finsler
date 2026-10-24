import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.MarkedStationaryValuePalmMarginals

/-!
# Actual stationary scenes under original clock-dependent translations

Each original clock and immutable color chooses its spatial translation.
The point maps are homeomorphisms, move both actual plans and the actual colored
input measure, commute with the original reroot action, and preserve every
original Haar-times-clock intensity.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryClockShiftInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryClockShiftPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Translate the actual spatial point by its own original clock and leave
that clock exactly unchanged. The inverse subtracts the same clock shift. -/
def legalClockShiftPoint (q : ℕ) (b : C(ℝ, Fin q → ℝ)) :
    LegalMarkedPhysicalPoint q ≃ₜ LegalMarkedPhysicalPoint q where
  toFun p := (p.1 + b p.2, p.2)
  invFun p := (p.1 - b p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.add (b.continuous.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (b.continuous.comp continuous_snd)).prodMk continuous_snd

@[simp] theorem legalClockShiftPoint_apply (q : ℕ) (b : C(ℝ, Fin q → ℝ))
    (p : LegalMarkedPhysicalPoint q) : legalClockShiftPoint q b p = (p.1 + b p.2, p.2) := rfl

@[simp] theorem legalClockShiftPoint_symm_apply (q : ℕ) (b : C(ℝ, Fin q → ℝ))
    (p : LegalMarkedPhysicalPoint q) : (legalClockShiftPoint q b).symm p = (p.1 - b p.2, p.2) := rfl

/-- The immutable input color selects its own original continuous clock shift. -/
def legalClockShiftColoredPoint (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    LegalColoredInputPoint q ≃ₜ LegalColoredInputPoint q where
  toFun p := (legalClockShiftPoint q (b p.2) p.1, p.2)
  invFun p := ((legalClockShiftPoint q (b p.2)).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_prod_of_discrete_right.mpr (fun c ↦
    (legalClockShiftPoint q (b c)).continuous.prodMk continuous_const)
  continuous_invFun := continuous_prod_of_discrete_right.mpr (fun c ↦
    (legalClockShiftPoint q (b c)).symm.continuous.prodMk continuous_const)

@[simp] theorem legalClockShiftColoredPoint_apply (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (p : LegalColoredInputPoint q) :
    legalClockShiftColoredPoint q b p = (legalClockShiftPoint q (b p.2) p.1, p.2) := rfl

/-- The actual two endpoints use the shifts of their unchanged source and
target colors, retaining both original clocks. -/
def legalClockShiftEdge (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    LegalMarkedPhysicalEdge q ≃ₜ LegalMarkedPhysicalEdge q :=
  (legalClockShiftPoint q (b 0)).prodCongr (legalClockShiftPoint q (b 1))

/-- Original Haar space times any original scalar clock law is invariant
under a continuous clock-dependent spatial translation. -/
theorem measurePreserving_legalClockShiftPoint (q : ℕ) (b : C(ℝ, Fin q → ℝ))
    (α : Measure ℝ) [SFinite α] :
    MeasurePreserving (legalClockShiftPoint q b)
      ((volume : Measure (Fin q → ℝ)).prod α) ((volume : Measure (Fin q → ℝ)).prod α) := by
  change MeasurePreserving (fun p : LegalMarkedPhysicalPoint q ↦ (p.1 + b p.2, p.2)) _ _
  have hskew : MeasurePreserving
      (fun p : ℝ × (Fin q → ℝ) ↦ (p.1, p.2 + b p.1))
      (α.prod (volume : Measure (Fin q → ℝ))) (α.prod (volume : Measure (Fin q → ℝ))) :=
    (MeasurePreserving.id α).skew_product
      (measurable_snd.add (b.continuous.measurable.comp measurable_fst))
      (.of_forall (fun a ↦ (measurePreserving_add_right volume (b a)).map_eq))
  have hswap₁ : MeasurePreserving Prod.swap
      ((volume : Measure (Fin q → ℝ)).prod α) (α.prod (volume : Measure (Fin q → ℝ))) :=
    Measure.measurePreserving_swap
  have hswap₂ : MeasurePreserving Prod.swap
      (α.prod (volume : Measure (Fin q → ℝ))) ((volume : Measure (Fin q → ℝ)).prod α) :=
    Measure.measurePreserving_swap
  have h := hswap₂.comp (hskew.comp hswap₁)
  simpa only [Function.comp_def, Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap] using h

/-- These point shifts commute with every original spatial reroot. -/
theorem legalClockShiftPoint_commute_reroot (q : ℕ) (b : C(ℝ, Fin q → ℝ))
    (v : Fin q → ℝ) (p : LegalMarkedPhysicalPoint q) :
    legalClockShiftPoint q b (physicalScenePointReroot v p) =
      physicalScenePointReroot v (legalClockShiftPoint q b p) := by
  apply Prod.ext
  · change (p.1 - v) + b p.2 = (p.1 + b p.2) - v
    abel
  · rfl

/-- Both actual edge endpoints commute with the same original root action. -/
theorem legalClockShiftEdge_commute_reroot (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (v : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q) :
    legalClockShiftEdge q b (physicalSceneEdgeReroot v e) =
      physicalSceneEdgeReroot v (legalClockShiftEdge q b e) := by
  exact Prod.ext (legalClockShiftPoint_commute_reroot q (b 0) v e.1)
    (legalClockShiftPoint_commute_reroot q (b 1) v e.2)

/-- Every input retains its immutable original color through both actions. -/
theorem legalClockShiftColoredPoint_commute_reroot (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (v : Fin q → ℝ) (p : LegalColoredInputPoint q) :
    legalClockShiftColoredPoint q b (legalColoredInputPointReroot q v p) =
      legalColoredInputPointReroot q v (legalClockShiftColoredPoint q b p) := by
  exact Prod.ext (legalClockShiftPoint_commute_reroot q (b p.2) v p.1) rfl

private theorem localFiniteMapHomeomorph_commute_clockShift
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
    [LocallyCompactSpace X] [BorelSpace X] (e f : X ≃ₜ X)
    (hef : ∀ x, e (f x) = f (e x)) (μ : LocalFiniteMeasure X) :
    localFiniteMapHomeomorph e (localFiniteMapHomeomorph f μ) =
      localFiniteMapHomeomorph f (localFiniteMapHomeomorph e μ) := by
  apply Subtype.ext
  change ((μ : Measure X).map f).map e = ((μ : Measure X).map e).map f
  rw [Measure.map_map e.continuous.measurable f.continuous.measurable,
    Measure.map_map f.continuous.measurable e.continuous.measurable]
  congr 1
  funext x
  exact hef x

/-- Apply the actual clock shifts to both original plans and the original
joint colored input measure. No input is replaced by a new draw. -/
def legalMarkedInputSceneClockShift (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (s : LegalMarkedOptimalInputScene q) : LegalMarkedOptimalInputScene q :=
  ((localFiniteMapHomeomorph (legalClockShiftEdge q b) s.1.1,
    localFiniteMapHomeomorph (legalClockShiftEdge q b) s.1.2),
      localFiniteMapHomeomorph (legalClockShiftColoredPoint q b) s.2)

/-- Actual joint-scene clock translation is continuous in the vague carrier. -/
theorem continuous_legalMarkedInputSceneClockShift (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) : Continuous (legalMarkedInputSceneClockShift q b) :=
  (((continuous_localFiniteMapHomeomorph _).comp continuous_fst.fst).prodMk
    ((continuous_localFiniteMapHomeomorph _).comp continuous_fst.snd)).prodMk
      ((continuous_localFiniteMapHomeomorph _).comp continuous_snd)

/-- The actual full joint-scene transformation commutes with rerooting. -/
theorem legalMarkedInputSceneClockShift_commute_reroot (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (v : Fin q → ℝ) (s : LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneClockShift q b (legalMarkedInputSceneReroot q v s) =
      legalMarkedInputSceneReroot q v (legalMarkedInputSceneClockShift q b s) := by
  apply Prod.ext
  · apply Prod.ext
    · exact localFiniteMapHomeomorph_commute_clockShift _ _
        (legalClockShiftEdge_commute_reroot q b v) s.1.1
    · exact localFiniteMapHomeomorph_commute_clockShift _ _
        (legalClockShiftEdge_commute_reroot q b v) s.1.2
  · exact localFiniteMapHomeomorph_commute_clockShift _ _
      (legalClockShiftColoredPoint_commute_reroot q b v) s.2

/-- The pushed law is the distribution of this same transformed scene. -/
def legalMarkedInputClockShiftLaw (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  Q.map (continuous_legalMarkedInputSceneClockShift q b).measurable.aemeasurable

/-- Clock shifts preserve actual joint stationarity by commuting with the
original root action; stationarity of the transformed scene is produced. -/
theorem measurePreserving_legalMarkedInputClockShiftLaw_reroot (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hQ : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)))
    (v : Fin q → ℝ) :
    MeasurePreserving (legalMarkedInputSceneReroot q v)
      (legalMarkedInputClockShiftLaw q b Q : Measure (LegalMarkedOptimalInputScene q))
      (legalMarkedInputClockShiftLaw q b Q : Measure (LegalMarkedOptimalInputScene q)) := by
  refine ⟨(continuous_legalMarkedInputSceneReroot q v).measurable, ?_⟩
  change ((Q : Measure (LegalMarkedOptimalInputScene q)).map (legalMarkedInputSceneClockShift q b)).map
    (legalMarkedInputSceneReroot q v) = _
  rw [Measure.map_map (continuous_legalMarkedInputSceneReroot q v).measurable
    (continuous_legalMarkedInputSceneClockShift q b).measurable]
  have hcomm : legalMarkedInputSceneReroot q v ∘ legalMarkedInputSceneClockShift q b =
      legalMarkedInputSceneClockShift q b ∘ legalMarkedInputSceneReroot q v := by
    funext s
    exact (legalMarkedInputSceneClockShift_commute_reroot q b v s).symm
  rw [hcomm, ← Measure.map_map (continuous_legalMarkedInputSceneClockShift q b).measurable
    (continuous_legalMarkedInputSceneReroot q v).measurable, (hQ v).map_eq]
  rfl

/-- Original strict clock legality is fixed by the actual edge shift. -/
theorem legalClockShiftEdge_forward_iff (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (e : LegalMarkedPhysicalEdge q) :
    (legalClockShiftEdge q b e).1.2 < (legalClockShiftEdge q b e).2.2 ↔ e.1.2 < e.2.2 := Iff.rfl

/-- The full actual displacement changes by exactly the target clock shift
minus the source clock shift. -/
theorem legalClockShiftEdge_displacement (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (e : LegalMarkedPhysicalEdge q) :
    (legalClockShiftEdge q b e).2.1 - (legalClockShiftEdge q b e).1.1 =
      (e.2.1 - e.1.1) + (b 1 e.2.2 - b 0 e.1.2) := by
  change (e.2.1 + b 1 e.2.2) - (e.1.1 + b 0 e.1.2) = _
  abel

/-- Both original independent Poisson colors have their literal original
colored intensity preserved by their own clock-dependent shifts. -/
theorem map_original_coloredPoissonIntensity_legalClockShift (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (α β : Measure ℝ) [SFinite α] [SFinite β] :
    (((volume : Measure (Fin q → ℝ)).prod α).map (fun p ↦ (p, (0 : Fin 2))) +
      ((volume : Measure (Fin q → ℝ)).prod β).map (fun p ↦ (p, (1 : Fin 2)))).map
        (legalClockShiftColoredPoint q b) =
      ((volume : Measure (Fin q → ℝ)).prod α).map (fun p ↦ (p, (0 : Fin 2))) +
        ((volume : Measure (Fin q → ℝ)).prod β).map (fun p ↦ (p, (1 : Fin 2))) := by
  have hc (ν : Measure ℝ) [SFinite ν] (c : Fin 2) :
      (((volume : Measure (Fin q → ℝ)).prod ν).map (fun p ↦ (p, c))).map
          (legalClockShiftColoredPoint q b) =
        ((volume : Measure (Fin q → ℝ)).prod ν).map (fun p ↦ (p, c)) := by
    have hemb : Measurable (fun p : LegalMarkedPhysicalPoint q ↦ (p, c)) := by fun_prop
    calc
      _ = ((volume : Measure (Fin q → ℝ)).prod ν).map
          (fun p ↦ (legalClockShiftPoint q (b c) p, c)) := by
        rw [Measure.map_map (legalClockShiftColoredPoint q b).continuous.measurable
          hemb]
        rfl
      _ = (((volume : Measure (Fin q → ℝ)).prod ν).map
          (legalClockShiftPoint q (b c))).map (fun p ↦ (p, c)) := by
        rw [Measure.map_map hemb (legalClockShiftPoint q (b c)).continuous.measurable]
        rfl
      _ = _ := by rw [(measurePreserving_legalClockShiftPoint q (b c) ν).map_eq]
  rw [Measure.map_add _ _ (legalClockShiftColoredPoint q b).continuous.measurable, hc α 0, hc β 1]

/-- The transformed original input test is the compact pullback test on the
same original input measure. This exact identity needs no Poisson law premise. -/
theorem legalMarkedInputSceneClockShift_testIntegral (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (s : LegalMarkedOptimalInputScene q)
    (F : C_c(LegalColoredInputPoint q, ℝ)) :
    LocalFiniteMeasure.testIntegral (legalMarkedInputSceneClockShift q b s).2 F =
      LocalFiniteMeasure.testIntegral s.2
        (F.comp (legalClockShiftColoredPoint q b).toCocompactMap) := by
  exact integral_map (legalClockShiftColoredPoint q b).continuous.measurable.aemeasurable
    F.continuous.aestronglyMeasurable

end OTSelector.Reconstruction
