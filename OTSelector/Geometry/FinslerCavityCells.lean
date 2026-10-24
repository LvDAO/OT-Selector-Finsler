import OTSelector.Geometry.Finsler.DistanceDifference
import OTSelector.Probability.CavityCells

/-!
# Original Finsler cavity cells and exact retained-input allocation

Chartwise absolute continuity in dimension at least two makes original distance
cost differences atomless. For almost every retained environment with distinct
measurable targets, an independent original insertion therefore belongs to exactly
one finite cavity cell. Every original almost-everywhere optimal assignment has
its partner allocation given by the actual cell masses, tested against every
measurable retained-input event. No measurable choice of optimizer is required.
-/

open Set Filter Metric MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology NNReal ENNReal ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M]
  {n : ℕ} {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]

/-- The inserted row consists of the original Finsler distances to retained targets. -/
def distanceCavityRow (F : ContinuousFinslerNorm E M)
    (Y : W → Fin (n + 1) → M) (z : W × M) (j : Fin (n + 1)) : ℝ :=
  let _instFinslerCavityRowMetric : MetricSpace M := F.metricSpace
  dist z.2 (Y z.1 j)

/-- Completeness gives the countability needed for joint measurability of the
actual distance row from measurability of the retained targets. -/
theorem measurable_distanceCavityRow (F : ContinuousFinslerNorm E M)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (Y : W → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (j : Fin (n + 1)) : Measurable (fun z ↦ F.distanceCavityRow Y z j) := by
  let _instFinslerCavityRowMeasurableMetric : MetricSpace M := F.metricSpace
  let _instFinslerCavityRowMeasurableProper : ProperSpace M :=
    F.properSpace_of_complete hcomplete
  exact measurable_snd.dist ((hY j).comp measurable_fst)

namespace IsSmoothStronglyConvex

variable [MeasurableSpace E] [BorelSpace E] {F : ContinuousFinslerNorm E M}

/-- Under original insertion independence and almost-everywhere distinct retained
targets, the original distance cavity cell is almost surely unique. Atomlessness and
joint row measurability follow from the actual Finsler geometry and measure. -/
theorem ae_existsUnique_distanceCavityCell (hF : F.IsSmoothStronglyConvex)
    (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsFiniteMeasure P]
    (W₀ : Ω → W) (X : Ω → M) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (Y : W → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (hinj : ∀ᵐ w ∂P.map W₀, Function.Injective (Y w))
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l)) (i : Fin (n + 1)) :
    ∀ᵐ ω₀ ∂P, ∃! j, (W₀ ω₀, X ω₀) ∈ cavityCell retained (F.distanceCavityRow Y) i j := by
  apply ae_existsUnique_mem_cavityCell_of_indepFun_atomless P μ W₀ X hW hX hindep hlaw
    retained (F.distanceCavityRow Y) hret (F.measurable_distanceCavityRow hcomplete Y hY) i
  filter_upwards [hinj] with w hw
  intro j k hjk
  exact hF.nullSingletonClass_map_distance_sub m μ hdim hchart hcomplete
    (fun heq ↦ hjk (hw heq))

/-- Every original almost-everywhere optimal assignment has the exact cell-mass
allocation law for original distance costs and every measurable retained-input event.
Only the inserted partner is forced unique; the full optimizer need not be measurable
or unique, and no independent differential or atomlessness condition is assumed. -/
theorem measure_distance_optimal_partner_restrict_retained (hF : F.IsSmoothStronglyConvex)
    (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsFiniteMeasure P]
    (W₀ : Ω → W) (X : Ω → M) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (Y : W → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (hinj : ∀ᵐ w ∂P.map W₀, Function.Injective (Y w))
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l)) (i j : Fin (n + 1))
    (σ : Ω → Assignment (n + 1))
    (hσ : ∀ᵐ ω₀ ∂P, OptimalAssignment
      (Function.update (retained (W₀ ω₀)) i (F.distanceCavityRow Y (W₀ ω₀, X ω₀))) (σ ω₀))
    (B : Set W) (hB : MeasurableSet B) :
    P {ω₀ | W₀ ω₀ ∈ B ∧ σ ω₀ i = j} =
      ∫⁻ w in B, cavityCellMass μ retained (F.distanceCavityRow Y) i j w ∂P.map W₀ := by
  let _instFinslerCavityAllocationFinite : IsFiniteMeasure μ := by
    rw [← hlaw]
    exact Measure.isFiniteMeasure_map P X
  apply measure_optimal_partner_restrict_retained_atomless P μ W₀ X hW hX hindep hlaw
    retained (F.distanceCavityRow Y) hret (F.measurable_distanceCavityRow hcomplete Y hY)
    i j ?_ σ hσ B hB
  filter_upwards [hinj] with w hw
  intro k l hkl
  exact hF.nullSingletonClass_map_distance_sub m μ hdim hchart hcomplete
    (fun heq ↦ hkl (hw heq))

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
