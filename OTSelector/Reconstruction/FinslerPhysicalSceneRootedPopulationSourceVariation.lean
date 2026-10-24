import OTSelector.Reconstruction.FinslerCoefficientCoreFrozenLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneCoordinates
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-! Original finite cell laws give simultaneous setwise source upper bounds after any actual observation. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- A raw finite-law variation bound controls every measurable set at once. -/
theorem measure_apply_le_add_totalVariation
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Set X} (hs : MeasurableSet s) :
    μ s ≤ ν s + (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ := by
  let v := (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation
  have hn := SignedMeasure.norm_le_totalVariation (μ.toSignedMeasure - ν.toSignedMeasure) s
  rw [Measure.toSignedMeasure_sub_apply hs] at hn
  have hv : (v s).toReal ≤ (v univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top v univ) (measure_mono (subset_univ s))
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ s)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top ν s, measure_ne_top v univ⟩)).mp
  rw [ENNReal.toReal_add (measure_ne_top ν s) (measure_ne_top v univ)]
  dsimp only [measureReal_def] at hn
  have habs : (μ s).toReal - (ν s).toReal ≤ ‖(μ s).toReal - (ν s).toReal‖ :=
    le_abs_self _
  linarith

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

/-- The actual original physical source restriction has a setwise upper bound
by its unchanged frozen clock law. The same raw variation error applies to ALL
measurable source sets, including after an arbitrary actual coordinate/root map. -/
theorem original_source_cell_observation_le_frozen_add
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (z₀ : ℚ → M) (tolerance : ℝ)
    (hcell : D.FrozenCellVariationBound hF hcomplete hu ha hinj i L hL hsub z₀ tolerance)
    {X : Type*} [MeasurableSpace X]
    (T : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ → X)
    (hT : Measurable T) (s : Set X) (hs : MeasurableSet s) :
    ((η₀.restrict (a ⁻¹' L)).map (fun x ↦ T (D.haar.sceneCoordinate i x))) s ≤
      (((D.rootIntensity i z₀).toNNReal •
        ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
          (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L)).prod
            (condDistrib u a η₀ z₀)).map T) s +
        ENNReal.ofReal (2 * tolerance * D.rootIntensity i z₀) *
          (κ (D.haar.continuous.coefficient i).seedIndex)
            (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L) := by
  let _inst : MetricSpace M := F.metricSpace
  let C := D.haar.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let spatial := (κ C.seedIndex).restrict (R '' L)
  let density := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  let clock := populationSeedCoordinateClockKernel (P C.seedIndex).seed a ha (condDistrib u a η₀)
  let actual := spatial.withDensity density ⊗ₘ clock
  let frozen := (D.rootIntensity i z₀).toNNReal • spatial.prod (condDistrib u a η₀ z₀)
  have _instSpatial := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  have _instIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  have hjoint : (η₀.restrict (a ⁻¹' L)).map (D.haar.sceneCoordinate i) = actual :=
    (D.haar.cell_joint_laws hF hcomplete hu ha hinj i hL hsub).1
  have hv : (actual.toSignedMeasure - frozen.toSignedMeasure).totalVariation univ ≤
      ENNReal.ofReal (2 * tolerance * D.rootIntensity i z₀) * (κ C.seedIndex) (R '' L) := by
    have hh := hcell (0 : Fin 2)
    simpa only [populationTwoColorClockKernel, ite_eq_left rfl, ite_true] using hh
  have hbound := (measure_apply_le_add_totalVariation actual frozen (hT hs)).trans
    (add_le_add le_rfl hv)
  rw [Measure.map_apply hT hs] at ⊢
  rw [← hjoint, Measure.map_apply (D.haar.measurable_sceneCoordinate hF hcomplete hu ha hinj i)
    (hT hs)] at hbound
  have hobs : Measurable (fun x : M ↦ T (D.haar.sceneCoordinate i x)) := by
    have hh := hT.comp (D.haar.measurable_sceneCoordinate hF hcomplete hu ha hinj i)
    simpa only [Function.comp_def] using hh
  rw [Measure.map_apply hobs hs]
  exact hbound
end PopulationLocalPressureCore
end OTSelector.Reconstruction
