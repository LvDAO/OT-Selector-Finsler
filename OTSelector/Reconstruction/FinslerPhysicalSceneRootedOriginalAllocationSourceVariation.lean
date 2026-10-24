import OTSelector.Reconstruction.FinslerPhysicalSceneRootedPopulationSourceVariation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMarginals

/-! The same global allocation retains its exact source law after physical restriction and rooting. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

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

/-- Every actual globally feasible allocation has the same raw source bound
after restricting its original physical rows, scaling and rooting. No new
conditional columns or independently rebuilt cell optimizer is introduced. -/
theorem original_allocation_rooted_cell_source_le_frozen_add
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (z₀ : ℚ → M) (tolerance : ℝ)
    (hcell : D.FrozenCellVariationBound hF hcomplete hu ha hinj i L hL hsub z₀ tolerance)
    {ι : Type*} [Fintype ι] {n : ℕ}
    (allocation : M → Fin (n + 1) → ℝ) {weights : Fin (n + 1) → ℝ}
    (hfeas : IsSemidiscreteAllocation η₀ weights allocation) (Y : Fin (n + 1) → M)
    (spatial : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker → (ι → ℝ))
    (hspatial : Measurable spatial) (N : ℝ) (root : ι → ℝ)
    (s : Set ((ι → ℝ) × ℝ)) (hs : MeasurableSet s) :
    let coord := fun x : M ↦ spatial (D.haar.sceneCoordinate i x).1
    let obs := fun p : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ ↦
      (spatial p.1 - root, p.2)
    ((physicalSceneRootedPlan
      (physicalSceneAllocationPlan (η₀.restrict (a ⁻¹' L)) allocation Y) coord u N root).fst) s ≤
      ENNReal.ofReal N *
        ((((D.rootIntensity i z₀).toNNReal •
          ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
            (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L)).prod
              (condDistrib u a η₀ z₀)).map obs) s) +
        ENNReal.ofReal N * (ENNReal.ofReal (2 * tolerance * D.rootIntensity i z₀) *
          (κ (D.haar.continuous.coefficient i).seedIndex)
            (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L)) := by
  let _inst : MetricSpace M := F.metricSpace
  intro coord obs
  have hc := D.haar.measurable_sceneCoordinate hF hcomplete hu ha hinj i
  have hcoord : Measurable coord := by
    have hh := hspatial.comp (measurable_fst.comp hc)
    simpa only [Function.comp_def] using hh
  have hobs : Measurable obs := (hspatial.comp measurable_fst |>.sub measurable_const).prodMk measurable_snd
  have hraw := D.original_source_cell_observation_le_frozen_add hF hcomplete hu ha hinj i
    hL hsub z₀ tolerance hcell obs hobs s hs
  have hmarg := (physicalSceneRootedPlan_source_restrict_marginals hfeas Y (a ⁻¹' L)
    coord hcoord u hu.continuous.measurable N root).1
  rw [hmarg, Measure.smul_apply]
  have hb := mul_le_mul_right hraw (ENNReal.ofReal N)
  simpa only [smul_eq_mul, mul_add, obs, coord, PopulationHaarPressureCore.sceneCoordinate] using hb
end PopulationLocalPressureCore
end OTSelector.Reconstruction
