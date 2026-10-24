import OTSelector.Reconstruction.FinslerPhysicalSceneTransport
import OTSelector.Geometry.FinslerDistanceLocalizationPopulation

/-!
# Local displacement energy from the original physical slack

The displacement uses the original finite seed basis.  Its observable retains
both original roots, the actual scalar pair region, the local coercivity radius,
and the two exact physical reconstruction identities.  The original uniform
source coercivity controls this masked observable by the actual distance slack,
and hence controls its energy in every actual scene allocation measure.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The original label displacement in the same basis as the retained coefficient. -/
def basisDisplacement (i : Fin D.haar.continuous.count) (p : M × M) :
    Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ :=
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  (Module.finBasis ℝ S.covector.ker).equivFun
    (populationSeedRootLabelValue S a (a p.2) - populationSeedRootLabelValue S a (a p.1))

/-- The actual local event where the original source coercivity is valid. -/
def nearDisplacementEvent (i : Fin D.haar.continuous.count) (radius : ℝ) : Set (M × M) :=
  let C := D.haar.continuous.coefficient i
  let physical := populationSeedPhysicalMap (P C.seedIndex).seed
  {p | a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧ (u p.1, u p.2) ∈ C.window.region ∧
    ‖D.basisDisplacement i p‖ < radius ∧
    physical (D.haar.sceneCoordinate i p.1) = p.1 ∧
    physical (D.haar.sceneCoordinate i p.2) = p.2}

/-- The squared original coordinate displacement, masked by its actual local event. -/
def nearDisplacementSquared (i : Fin D.haar.continuous.count) (radius : ℝ) : M × M → ℝ :=
  (D.nearDisplacementEvent i radius).indicator (fun p ↦ ‖D.basisDisplacement i p‖ ^ 2)

/-- The masked displacement observable is nonnegative on every physical edge. -/
theorem nearDisplacementSquared_nonneg
    (i : Fin D.haar.continuous.count) (radius : ℝ) (p : M × M) :
    0 ≤ D.nearDisplacementSquared i radius p :=
  indicator_nonneg (fun p _ ↦ sq_nonneg ‖D.basisDisplacement i p‖) p

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSceneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The actual fixed-basis displacement is jointly measurable in both endpoints. -/
theorem measurable_basisDisplacement (i : Fin D.haar.continuous.count) :
    Measurable (D.basisDisplacement i) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  have hw := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  exact (Module.finBasis ℝ S.covector.ker).equivFunL.continuous.measurable.comp
    ((hw.comp (ha.comp measurable_snd)).sub (hw.comp (ha.comp measurable_fst)))

/-- Every retained root, time, radius and exact reconstruction condition in the
actual local event is measurable. -/
theorem measurableSet_nearDisplacementEvent
    (i : Fin D.haar.continuous.count) (radius : ℝ) :
    MeasurableSet (D.nearDisplacementEvent i radius) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  have hroot := C.roots_compact.measurableSet
  have hclock := hu.continuous.measurable
  have hphysical := measurable_populationSeedPhysicalMap (P C.seedIndex).seed
  have hcoord := D.haar.measurable_sceneCoordinate hF hcomplete hu ha hinj i
  change MeasurableSet {p : M × M | a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧
    (u p.1, u p.2) ∈ C.window.region ∧ ‖D.basisDisplacement i p‖ < radius ∧
    populationSeedPhysicalMap (P C.seedIndex).seed (D.haar.sceneCoordinate i p.1) = p.1 ∧
    populationSeedPhysicalMap (P C.seedIndex).seed (D.haar.sceneCoordinate i p.2) = p.2}
  exact (hroot.preimage (ha.comp measurable_fst)).inter
    ((hroot.preimage (ha.comp measurable_snd)).inter
      ((C.window.isCompact_region.measurableSet.preimage
        ((hclock.comp measurable_fst).prodMk (hclock.comp measurable_snd))).inter
        ((measurableSet_lt (D.measurable_basisDisplacement hF hcomplete hu ha hinj i).norm
          measurable_const).inter
          ((measurableSet_eq_fun ((hphysical.comp hcoord).comp measurable_fst)
            measurable_fst).inter
            (measurableSet_eq_fun ((hphysical.comp hcoord).comp measurable_snd)
              measurable_snd)))))

/-- The local squared-displacement energy is a measurable actual observable. -/
theorem measurable_nearDisplacementSquared
    (i : Fin D.haar.continuous.count) (radius : ℝ) :
    Measurable (D.nearDisplacementSquared i radius) :=
  ((D.measurable_basisDisplacement hF hcomplete hu ha hinj i).norm.pow_const 2).indicator
    (D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius)

/-- One original positive coefficient and radius control the masked displacement
on every retained core and every physical edge. -/
theorem exists_uniform_nearDisplacement_coercivity :
    ∃ q > 0, ∃ radius > 0, ∀ i : Fin D.haar.continuous.count, ∀ x y : M,
      q * D.nearDisplacementSquared i radius (x, y) ≤
        (F.lengthEDist x y).toReal - u y + u x := by
  classical
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  obtain ⟨q, hq, radius, hradius, hcoerc⟩ :=
    D.exists_uniform_source_coercivity hF hcomplete hu ha hinj
  refine ⟨q, hq, radius, hradius, fun i x y ↦ ?_⟩
  by_cases he : (x, y) ∈ D.nearDisplacementEvent i radius
  · have hmem := he
    obtain ⟨hx, hy, ht, hv, hxread, hyread⟩ := he
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let bW := Module.finBasis ℝ S.covector.ker
    let R := populationSeedRootLabelValue S a
    have hd : R (a x) + bW.equivFun.symm (D.basisDisplacement i (x, y)) = R (a y) := by
      simp only [basisDisplacement, bW, C, S, R, LinearEquiv.symm_apply_apply]
      abel
    have hxwindow := C.root_label_mem_window hF hcomplete hu ha hinj hx
    have hywindow := C.root_label_mem_window hF hcomplete hu ha hinj hy
    have hb := hcoerc i (a x) hx (u x, u y) ht (D.basisDisplacement i (x, y)) hv
      (by rw [hd]; exact hywindow)
    change q * ‖D.basisDisplacement i (x, y)‖ ^ 2 ≤
      populationSeedPairDeficit S (u x, u y)
        (R (a x), R (a x) + bW.equivFun.symm (D.basisDisplacement i (x, y))) at hb
    rw [hd] at hb
    have hxcurve : S.curve (R (a x)) (u x - S.level) = x :=
      (populationSeedPhysicalMap_at_label S ⟨R (a x), hxwindow.1⟩ (u x)).symm.trans hxread
    have hycurve : S.curve (R (a y)) (u y - S.level) = y :=
      (populationSeedPhysicalMap_at_label S ⟨R (a y), hywindow.1⟩ (u y)).symm.trans hyread
    simpa only [nearDisplacementSquared, indicator_of_mem hmem, populationSeedPairDeficit,
      hxcurve, hycurve] using hb
  · rw [nearDisplacementSquared, indicator_of_notMem he, mul_zero]
    have hl := hu.le_add_mul y x
    simp only [NNReal.coe_one, one_mul, dist_comm y x] at hl
    change 0 ≤ dist x y - u y + u x
    linarith

/-- The original local coercivity also controls the actual scaled displacement
lintegral in every allocation measure on the actual source scene law. -/
theorem exists_uniform_scene_nearDisplacement_energy :
    ∃ q > 0, ∃ radius > 0,
      (∀ i : Fin D.haar.continuous.count, ∀ x y : M,
        q * D.nearDisplacementSquared i radius (x, y) ≤
          (F.lengthEDist x y).toReal - u y + u x) ∧
      ∀ (i : Fin D.haar.continuous.count) (L : Set (ℚ → M)) (n : ℕ)
        (Y : Fin (n + 1) →
          (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ)
        (A : ((P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ) →
          Fin (n + 1) → ℝ) (scale : ℝ), 0 ≤ scale →
        let physical := populationSeedPhysicalMap
          (P (D.haar.continuous.coefficient i).seedIndex).seed
        (∫⁻ e, ENNReal.ofReal (scale * q *
          D.nearDisplacementSquared i radius (physical e.1, physical (Y e.2)))
          ∂OTSelector.Probability.semidiscreteAllocationMeasure (D.haar.sceneLaw η₀ i L) A) ≤
        ∫⁻ e, ENNReal.ofReal (scale *
          ((F.lengthEDist (physical e.1) (physical (Y e.2))).toReal -
            u (physical (Y e.2)) + u (physical e.1)))
          ∂OTSelector.Probability.semidiscreteAllocationMeasure (D.haar.sceneLaw η₀ i L) A := by
  obtain ⟨q, hq, radius, hradius, hbound⟩ :=
    D.exists_uniform_nearDisplacement_coercivity hF hcomplete hu ha hinj
  refine ⟨q, hq, radius, hradius, hbound, ?_⟩
  intro i L n Y A scale hscale
  dsimp only
  apply lintegral_mono
  intro e
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound i _ _) hscale

/-- The same original local constants control masked near displacement in an
arbitrary global physical allocation environment.  Every bound on its original
global slack energy therefore bounds this near displacement energy as well. -/
theorem exists_uniform_global_nearDisplacement_energy :
    ∃ q > 0, ∃ radius > 0,
      ∀ (μ : Measure M) (Ω : Type*) [MeasurableSpace Ω] (Penv : Measure Ω) (n : ℕ)
        (i : Fin D.haar.continuous.count) (Y : Ω → Fin (n + 1) → M)
        (A : Ω → M → Fin (n + 1) → ℝ) (scale : ℝ), 0 ≤ scale →
        let nearEnergy := (∫⁻ env, ∫⁻ e, ENNReal.ofReal (scale * q *
          D.nearDisplacementSquared i radius (e.1, Y env e.2))
          ∂OTSelector.Probability.semidiscreteAllocationMeasure μ (A env) ∂Penv)
        let slackEnergy := (∫⁻ env, ∫⁻ e, ENNReal.ofReal (scale *
          ((F.lengthEDist e.1 (Y env e.2)).toReal - u (Y env e.2) + u e.1))
          ∂OTSelector.Probability.semidiscreteAllocationMeasure μ (A env) ∂Penv)
        nearEnergy ≤ slackEnergy ∧
          ∀ C : ℝ, slackEnergy ≤ ENNReal.ofReal C → nearEnergy ≤ ENNReal.ofReal C := by
  obtain ⟨q, hq, radius, hradius, hbound⟩ :=
    D.exists_uniform_nearDisplacement_coercivity hF hcomplete hu ha hinj
  refine ⟨q, hq, radius, hradius, ?_⟩
  intro μ Ω _ Penv n i Y A scale hscale
  have henergy :
      (∫⁻ env, ∫⁻ e, ENNReal.ofReal (scale * q *
        D.nearDisplacementSquared i radius (e.1, Y env e.2))
        ∂OTSelector.Probability.semidiscreteAllocationMeasure μ (A env) ∂Penv) ≤
      ∫⁻ env, ∫⁻ e, ENNReal.ofReal (scale *
        ((F.lengthEDist e.1 (Y env e.2)).toReal - u (Y env e.2) + u e.1))
        ∂OTSelector.Probability.semidiscreteAllocationMeasure μ (A env) ∂Penv := by
    apply lintegral_mono
    intro env
    apply lintegral_mono
    intro e
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound i e.1 (Y env e.2)) hscale
  exact ⟨henergy, fun _ hC ↦ henergy.trans hC⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
