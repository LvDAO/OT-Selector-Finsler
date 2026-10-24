import OTSelector.Reconstruction.FinslerOriginalConcretePalmSampleLaw
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# The finite scene cloud cannot have an atomless population marginal

The scene lane samples a uniformly chosen slot of a fixed finite cloud. At level
`n = 0` the slot space is a singleton, so its source and target laws are Dirac
measures. They cannot equal a population measure whose pushforward under a
measurable potential has null singletons.

Consequently the all-level population marginal hypotheses for `sceneCloudX` and
`sceneCloudY` in the V18 interface are incompatible with that atomlessness
hypothesis. This obstruction concerns that finite scene lane; it does not concern
the iid product sampling model of the mathematical theorem.
-/

open MeasureTheory

namespace OTSelector.Reconstruction

variable {M : Type*} [MeasurableSpace M]

/-- A measure with an atomless measurable readout cannot be a Dirac measure. -/
theorem measure_ne_dirac_of_atomless_map (μ : Measure M) (u : M → ℝ)
    (hu : Measurable u) [NullSingletonClass (μ.map u)] (x : M) :
    μ ≠ Measure.dirac x := by
  intro h
  have hzero : (μ.map u) {u x} = 0 := measure_singleton _
  rw [h, Measure.map_dirac' hu] at hzero
  simp at hzero

namespace PopulationLocalPressureCore.TaylorTiles

/-- At level zero the scene slot law is the Dirac measure on its only slot. -/
theorem sceneCloudSample_zero : sceneCloudSample 0 = Measure.dirac 0 := by
  simp [sceneCloudSample, OTSelector.empiricalMeasure]

/-- The source marginal of the singleton scene is the point mass at its cloud point. -/
theorem sceneCloudX_map_zero (pcloud : ∀ n, Fin (n + 1) → M) (i : Fin 1) :
    (sceneCloudSample 0).map ((sceneCloudX pcloud) 0 i) =
      Measure.dirac (pcloud 0 0) := by
  rw [sceneCloudSample_zero, Measure.map_dirac' (measurable_of_finite _)]
  rfl

/-- The target marginal of the singleton scene is the point mass at its cloud point. -/
theorem sceneCloudY_map_zero (qcloud : ∀ n, Fin (n + 1) → M) (i : Fin 1) :
    (sceneCloudSample 0).map ((sceneCloudY qcloud) 0 i) =
      Measure.dirac (qcloud 0 0) :=
  sceneCloudX_map_zero qcloud i

/-- The singleton source scene law differs from every population with an atomless
measurable potential. -/
theorem sceneCloudX_map_zero_ne_of_atomless_potential
    (pcloud : ∀ n, Fin (n + 1) → M) (μ : Measure M) (u : M → ℝ)
    (hu : Measurable u) [NullSingletonClass (μ.map u)] (i : Fin 1) :
    (sceneCloudSample 0).map ((sceneCloudX pcloud) 0 i) ≠ μ := by
  rw [sceneCloudX_map_zero]
  exact (measure_ne_dirac_of_atomless_map μ u hu (pcloud 0 0)).symm

/-- The source marginal hypothesis of the finite scene lane is impossible when
the population potential law is atomless; level zero already contradicts it. -/
theorem not_sceneCloudX_populationLaw_of_atomless_potential
    (pcloud : ∀ n, Fin (n + 1) → M) (μ : Measure M) (u : M → ℝ)
    (hu : Measurable u) [NullSingletonClass (μ.map u)] :
    ¬ ∀ (n : ℕ) (i : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudX pcloud) n i) = μ := by
  intro h
  exact sceneCloudX_map_zero_ne_of_atomless_potential pcloud μ u hu 0 (h 0 0)

/-- The same incompatibility holds for the target marginal hypothesis. -/
theorem not_sceneCloudY_populationLaw_of_atomless_potential
    (qcloud : ∀ n, Fin (n + 1) → M) (ν : Measure M) (u : M → ℝ)
    (hu : Measurable u) [NullSingletonClass (ν.map u)] :
    ¬ ∀ (n : ℕ) (i : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudY qcloud) n i) = ν :=
  not_sceneCloudX_populationLaw_of_atomless_potential qcloud ν u hu

end PopulationLocalPressureCore.TaylorTiles
end OTSelector.Reconstruction
