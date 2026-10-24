import OTSelector.Reconstruction.FinslerPopulationHaarPressureCore
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Actual finite Haar-core root mass recovery

The stored disjoint compact coefficient roots form the original retained
population core. Their literal original masses sum exactly, and the omitted
mass is one minus the real mass sum. Along actual core refinements, the stored
complement losses alone force these mass sums to one; no mass-recovery oracle,
positive intensity bound or boundary-null assumption is supplied.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}

section ProbabilityLabel
variable {lambda : Measure (ℚ → M)} [IsProbabilityMeasure lambda]
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Literal finite root masses, their real sum, exact omitted mass and the
actual stored loss, all for the same original Haar core and label law. -/
theorem PopulationHaarPressureCore.root_mass_partition
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) :
    let K := ⋃ i : Fin D.continuous.count, (D.continuous.coefficient i).roots
    (∑ i, lambda (D.continuous.coefficient i).roots) = lambda K ∧
      (∑ i, (lambda (D.continuous.coefficient i).roots).toReal) = (lambda K).toReal ∧
      (lambda Kᶜ).toReal = 1-(∑ i, (lambda (D.continuous.coefficient i).roots).toReal) ∧
      lambda Kᶜ < loss := by
  intro K
  let _rootMassMetric : MetricSpace M := F.metricSpace
  let _rootMassProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootMassPolish : PolishSpace M := inferInstance
  let _rootMassBorel : BorelSpace (ℚ → M) := inferInstance
  have hmeas (i : Fin D.continuous.count) : MeasurableSet (D.continuous.coefficient i).roots :=
    (D.continuous.coefficient i).roots_compact.measurableSet
  have hK : MeasurableSet K := MeasurableSet.iUnion hmeas
  have henn : (∑ i, lambda (D.continuous.coefficient i).roots) = lambda K := by
    simpa only [K,tsum_fintype] using (measure_iUnion D.continuous.disjoint hmeas).symm
  have hreal : (∑ i, (lambda (D.continuous.coefficient i).roots).toReal) = (lambda K).toReal := by
    rw [← henn,ENNReal.toReal_sum (fun i _ ↦ measure_ne_top lambda _)]
  have hcomp : (lambda Kᶜ).toReal = 1-(lambda K).toReal := by
    have hh := congrArg ENNReal.toReal (measure_add_measure_compl (μ := lambda) hK)
    rw [ENNReal.toReal_add (measure_ne_top lambda _) (measure_ne_top lambda _),
      measure_univ,ENNReal.toReal_one] at hh
    linarith
  refine ⟨henn,hreal,hcomp.trans (by rw [hreal]),?_⟩
  change lambda (⋃ i, (D.continuous.coefficient i).roots)ᶜ < loss
  rw [D.continuous.union_eq]
  exact D.continuous.population.complement_small

omit [T2Space M] [PreconnectedSpace M] [BorelSpace M] [IsProbabilityMeasure lambda] in
/-- The actual omitted label mass tends to zero directly from each core's
stored complement loss, while all selected-core parameters and counts may vary. -/
theorem populationHaarPressureCore_root_complement_tendsto_zero
    {Good : ℕ → (ℚ → M) → Prop} {r : ℕ → ℝ} {δ loss : ℕ → ℝ≥0∞}
    (D : ∀ n, PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (Good n) (r n) (δ n) (loss n))
    (hloss : Tendsto loss atTop (𝓝 0)) :
    Tendsto (fun n ↦ lambda (⋃ i : Fin (D n).continuous.count,
      ((D n).continuous.coefficient i).roots)ᶜ) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hloss (fun _ ↦ bot_le)
  intro n
  change lambda (⋃ i : Fin (D n).continuous.count, ((D n).continuous.coefficient i).roots)ᶜ ≤ loss n
  rw [(D n).continuous.union_eq]
  exact (D n).continuous.population.complement_small.le

/-- Actual disjoint original root masses recover one under stored loss
refinement. No mass-convergence premise is passed to this theorem. -/
theorem populationHaarPressureCore_root_mass_tendsto_one
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {Good : ℕ → (ℚ → M) → Prop} {r : ℕ → ℝ} {δ loss : ℕ → ℝ≥0∞}
    (D : ∀ n, PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (Good n) (r n) (δ n) (loss n))
    (hloss : Tendsto loss atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (D n).continuous.count,
      (lambda ((D n).continuous.coefficient i).roots).toReal) atTop (𝓝 1) := by
  have hcomp := populationHaarPressureCore_root_complement_tendsto_zero D hloss
  have hcompReal : Tendsto (fun n ↦ (lambda (⋃ i : Fin (D n).continuous.count,
      ((D n).continuous.coefficient i).roots)ᶜ).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hcomp
  have ht : Tendsto (fun n ↦ (1 : ℝ)-(lambda (⋃ i : Fin (D n).continuous.count,
      ((D n).continuous.coefficient i).roots)ᶜ).toReal) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hcompReal :
      Tendsto (fun n ↦ (1 : ℝ)-(lambda (⋃ i : Fin (D n).continuous.count,
        ((D n).continuous.coefficient i).roots)ᶜ).toReal) atTop (𝓝 ((1 : ℝ)-0)))
  apply ht.congr'
  filter_upwards with n
  have hm := ((D n).root_mass_partition hcomplete).2.2.1
  linarith

end ProbabilityLabel

section OriginalMapLabel
variable {μ : Measure M} [IsProbabilityMeasure μ]
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The exact partition formulas for the original probability label law
`μ.map a`, preserving the same literal roots and their original masses. -/
theorem PopulationHaarPressureCore.map_root_mass_partition
    (D : PopulationHaarPressureCore P a κ (μ.map a) η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (ha : Measurable a) :
    let K := ⋃ i : Fin D.continuous.count, (D.continuous.coefficient i).roots
    (∑ i, (μ.map a) (D.continuous.coefficient i).roots) = (μ.map a) K ∧
      (∑ i, ((μ.map a) (D.continuous.coefficient i).roots).toReal) = ((μ.map a) K).toReal ∧
      ((μ.map a) Kᶜ).toReal = 1-(∑ i, ((μ.map a) (D.continuous.coefficient i).roots).toReal) ∧
      (μ.map a) Kᶜ < loss := by
  let : IsProbabilityMeasure (μ.map a) := Measure.isProbabilityMeasure_map ha.aemeasurable
  exact D.root_mass_partition hcomplete

/-- The actual stored-loss core family supplies exactly the original mass
convergence needed by finite heterogeneous signed-shift refinement. -/
theorem populationHaarPressureCore_map_root_mass_tendsto_one
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (ha : Measurable a)
    {Good : ℕ → (ℚ → M) → Prop} {r : ℕ → ℝ} {δ loss : ℕ → ℝ≥0∞}
    (D : ∀ n, PopulationHaarPressureCore P a κ (μ.map a) η₀ η₁ ρ₀ ρ₁ v b
      (Good n) (r n) (δ n) (loss n))
    (hloss : Tendsto loss atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (D n).continuous.count,
      ((μ.map a) ((D n).continuous.coefficient i).roots).toReal) atTop (𝓝 1) := by
  let : IsProbabilityMeasure (μ.map a) := Measure.isProbabilityMeasure_map ha.aemeasurable
  exact populationHaarPressureCore_root_mass_tendsto_one hcomplete D hloss

end OriginalMapLabel
end OTSelector.Reconstruction
