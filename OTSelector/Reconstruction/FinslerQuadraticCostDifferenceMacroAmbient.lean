import OTSelector.Reconstruction.FinslerQuadraticCostDifferenceCoreAmbient
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalFullSupportCycle

/-! Original macro-tag rigidity on the actual strict clock domain. Spatial
volume times clock Lebesgue measure is the reference supplied by the original
full-source AC proof. Coefficient positivity, atomlessness and the original
macro/frozen cost identity are derived from the same original core. -/

open Set Function MeasureTheory ProbabilityTheory Manifold Module
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction.OriginalPopulationCoefficientCore
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}
  (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

local notation "Point" => ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)

/-- Ambient source-volume AC gives atomless ORIGINAL macro-cost differences
on every common strict legal source set. Only the actual core supplies the
matrix positivity; the conditional clock density is not a premise. -/
theorem nullSingletonClass_map_originalMacroCost_strictClock_sub
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {w : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ}
    (hw : w ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots)
    {ρ : Measure Point}
    (hρ : ρ ≪ (volume : Measure (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)).prod
      (volume : Measure ℝ))
    {y z : Point} (hyz : y.1 ≠ z.1) :
    NullSingletonClass ((ρ.restrict
      (commonLegalSource (physicalSceneStrictClockRegion C.window) y z)).map
      (fun x ↦ physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w x y -
        physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w x z)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨root, hroot, rfl⟩ := hw
  have hcost : C.frozenQuadraticCost root =
      physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex
        (physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex root) := by
    funext x y
    exact C.frozenQuadraticCost_eq_originalMacroCost hF hcomplete hu ha hinj hroot x y
  rw [← hcost]
  apply nullSingletonClass_map_marked_matrixQuadratic_sub volume volume hρ
    (fun s t ↦ populationSeedRootCoefficient (P C.seedIndex).seed a
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (root, s, t))
    ((measurable_populationSeedRootCoefficient (P C.seedIndex).seed hF hcomplete hu ha hinj _).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
    ((measurable_populationSeedRootCoefficient (P C.seedIndex).seed hF hcomplete hu ha hinj _).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))) hyz
    (measurableSet_commonLegalSource (isOpen_physicalSceneStrictClockRegion C.window).measurableSet y z)
  intro x hx
  exact ⟨C.coefficient_posDef root hroot _
      (clocks_mem_region_of_mem_physicalSceneStrictClockRegion C.window hx.1),
    C.coefficient_posDef root hroot _
      (clocks_mem_region_of_mem_physicalSceneStrictClockRegion C.window hx.2)⟩

/-- The SAME original macro cost forces equality of the actual ambient plans
on its strict original clock window, using ambient volume AC of their common
source. No original-conditional-clock domination is assumed. -/
theorem ambient_originalMacro_plans_eq_strictClock
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {w : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ}
    (hw : w ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots)
    {ρ : Measure Point}
    (hρ : ρ ≪ (volume : Measure (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)).prod
      (volume : Measure ℝ))
    {T : Set Point} (hT : T.Countable) (hTinj : InjOn Prod.fst T)
    (θ : Measure Point) (hθ : ∀ᵐ y ∂θ, y ∈ T)
    (π₀ π₁ : Measure (Point × Point))
    (hsource₀ : π₀.map Prod.fst = ρ) (hsource₁ : π₁.map Prod.fst = ρ)
    (htarget₀ : π₀.map Prod.snd = θ) (htarget₁ : π₁.map Prod.snd = θ)
    (hlegal₀ : ∀ᵐ p ∂π₀, p ∈ physicalSceneStrictClockRegion C.window)
    (hlegal₁ : ∀ᵐ p ∂π₁, p ∈ physicalSceneStrictClockRegion C.window)
    (hcycle : IsTwoCycleMonotoneOn
      (physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w)
      (physicalSceneStrictClockRegion C.window)
      ((((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) ∩ physicalSceneStrictClockRegion C.window)) :
    π₀ = π₁ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨z, hz, rfl⟩ := hw
  have hcost : C.frozenQuadraticCost z =
      physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex
        (physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex z) := by
    funext x y
    exact C.frozenQuadraticCost_eq_originalMacroCost hF hcomplete hu ha hinj hz x y
  apply C.ambient_frozenQuadratic_plans_eq hF hcomplete hu ha hinj hz volume volume hρ
    hT hTinj θ hθ π₀ π₁ hsource₀ hsource₁ htarget₀ htarget₁
    (physicalSceneStrictClockRegion C.window)
    (isOpen_physicalSceneStrictClockRegion C.window).measurableSet
    (fun p hp ↦ clocks_mem_region_of_mem_physicalSceneStrictClockRegion C.window hp)
    hlegal₀ hlegal₁
  simpa only [hcost] using hcycle

end OTSelector.Reconstruction.OriginalPopulationCoefficientCore
