import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals

/-!
# Null clock levels from the unchanged original physical density

The original joint label-clock density has Lebesgue clock reference. Every
actual level set is null before any allocation or sample is chosen.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  [SigmaFinite lambda] {η : Measure M} [IsFiniteMeasure η]
  {ρ : M → ℝ} {v : ℕ → E → ℝ}

/-- Every original clock level is null by the actual joint physical density. -/
theorem PopulationConditionalWindowLaw.original_clock_level_null
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (ha : Measurable a) (hu : Measurable u) (q : ℝ) :
    η (u ⁻¹' {q}) = 0 := by
  have hz : (lambda.prod (volume : Measure ℝ)) (univ ×ˢ {q}) = 0 := by
    rw [Measure.prod_prod]
    simp
  have h := hlaw.joint_absolutelyContinuous hz
  rw [Measure.map_apply (ha.prodMk hu)
    (MeasurableSet.univ.prod (measurableSet_singleton q))] at h
  have heq : (fun x ↦ (a x, u x)) ⁻¹' (univ ×ˢ {q}) = u ⁻¹' {q} := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, true_and]
  rwa [heq] at h

/-- The unchanged original scalar law is atomless; this is not inferred from
finite sampled target clocks. -/
theorem PopulationConditionalWindowLaw.nullSingletonClass_original_clock
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (ha : Measurable a) (hu : Measurable u) : NullSingletonClass (η.map u) := by
  constructor
  intro q
  rw [Measure.map_apply hu (measurableSet_singleton q)]
  exact hlaw.original_clock_level_null ha hu q

end OTSelector.Reconstruction
