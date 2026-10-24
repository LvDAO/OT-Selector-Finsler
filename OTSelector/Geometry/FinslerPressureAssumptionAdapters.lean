import OTSelector.Geometry.Manifold.ChartPopulationAbsoluteContinuity
import OTSelector.Geometry.Finsler.SlackAtomlessness

/-!
# Assumption adapters for the physical Finsler selector

Three small bridges used by the pressure and rigidity lanes:

* smooth-volume density data gives chartwise absolute continuity of a Lipschitz
  physical population;
* atomlessness passes to a restricted source measure;
* scaled distance-slack differences stay atomless after restriction.

None of these changes the existing declaration chain.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry

/-- Original volume densities imply chartwise absolute continuity of a physical population. -/
theorem chartwise_ac_of_lipschitz_density_volume
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [MeasurableSpace M] [BorelSpace M]
    (vol : Measure M) (m : Measure E) {ρ : M → ℝ}
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (vol.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y))) (old : M) :
    ((vol.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m :=
  chartwise_ac_withDensity_of_volume_density vol m hρ.measurable hρ0 v hv hvolume old

/-- Atomlessness is inherited by the pushforward of a restricted measure. -/
theorem nullSingletonClass_map_restrict {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {f : S → ℝ} (hf : Measurable f) (D : Set S)
    (h : NullSingletonClass (μ.map f)) :
    NullSingletonClass ((μ.restrict D).map f) where
  measure_singleton a := by
    have hle : (μ.restrict D).map f ≤ μ.map f :=
      Measure.map_mono Measure.restrict_le_self hf
    have hle' : ((μ.restrict D).map f) {a} ≤ (μ.map f) {a} :=
      Measure.le_iff'.1 hle {a}
    have h0 : (μ.map f) {a} = 0 := h.measure_singleton a
    exact le_antisymm (hle'.trans_eq h0) (by simp)

end OTSelector.Geometry

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Scaled distance-slack differences remain atomless after restricting the source. -/
theorem nullSingletonClass_map_scaled_distanceSlack_sub_restrict
    (hF : F.IsSmoothStronglyConvex)
    (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (φ : M → ℝ) {k : ℝ} (hk : k ≠ 0) {y z : M} (hyz : y ≠ z) (D : Set M) :
    let _instOriginalSlackRestrictMetric : MetricSpace M := F.metricSpace
    NullSingletonClass ((μ.restrict D).map (fun x ↦
      k * (dist x y - φ y + φ x) - k * (dist x z - φ z + φ x))) := by
  let _instOriginalSlackRestrictProofMetric : MetricSpace M := F.metricSpace
  change NullSingletonClass ((μ.restrict D).map (fun x ↦
    k * (dist x y - φ y + φ x) - k * (dist x z - φ z + φ x)))
  have h := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim hchart
    hcomplete φ hk hyz
  have heq : (fun x ↦ k * (dist x y - φ y + φ x) - k * (dist x z - φ z + φ x)) =
      (fun x ↦ k * ((dist x y - dist x z) - φ y + φ z)) := by
    funext x
    ring
  have h' : NullSingletonClass (μ.map
      (fun x ↦ k * ((dist x y - dist x z) - φ y + φ z))) := by
    simpa only [heq] using h
  have hm : Measurable (fun x : M ↦ k * ((dist x y - dist x z) - φ y + φ z)) :=
    ((((continuous_id.dist continuous_const).sub
      (continuous_id.dist continuous_const)).sub continuous_const).add
      continuous_const).const_mul k |>.measurable
  have hres := OTSelector.Geometry.nullSingletonClass_map_restrict hm D h'
  simpa only [heq] using hres

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
