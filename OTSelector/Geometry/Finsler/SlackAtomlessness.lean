import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.DistanceDifference
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSlackAtomlessness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSlackAtomlessness`; the selected original proof blocks follow. -/
section

/-!
Conditions: The explicit Finsler completeness, dimension and chart absolute-continuity hypotheses, nonzero scale and the already proved distance-difference atomlessness.

Objects: Atomlessness of the scaled slack difference, with cancellation of the common source potential.

Proof detail: Cancel the common potential algebraically and transport null fibers through a nonzero affine scalar map, invoking the distance-difference theorem with its full assumptions.

Sources: D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); Zhongmin Shen, Section 4, p. 313: the length integral, induced distance and minimizing curves (https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11).
Relation: A derived Finsler slack adapter. The cited geometry supplies background; the exact distance-difference and cancellation statement is proved in the library.
-/

/-!
# Atomlessness of original scaled distance-slack differences

The source potential cancels between two targets. Nonzero scaling and the
remaining target-dependent constant preserve the already proved atomlessness
of genuine Finsler distance differences. This supplies the original pressure
cost directly to the finite iid and semidiscrete probability theorems.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every distinct-target difference of the original scaled slack is atomless.
No regularity of the potential is needed: its source value cancels exactly. -/
theorem nullSingletonClass_map_scaled_distanceSlack_sub (hF : F.IsSmoothStronglyConvex)
    (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (φ : M → ℝ) {k : ℝ} (hk : k ≠ 0) {y z : M} (hyz : y ≠ z) :
    let _instOriginalSlackMetric : MetricSpace M := F.metricSpace
    NullSingletonClass (μ.map (fun x ↦
      k * (dist x y - φ y + φ x) - k * (dist x z - φ z + φ x))) := by
  let _instOriginalSlackProofMetric : MetricSpace M := F.metricSpace
  change NullSingletonClass (μ.map (fun x ↦
    k * (dist x y - φ y + φ x) - k * (dist x z - φ z + φ x)))
  have heq : (fun x ↦ k * (dist x y - φ y + φ x) - k * (dist x z - φ z + φ x)) =
      (fun x ↦ k * ((dist x y - dist x z) - φ y + φ z)) := by
    funext x
    ring
  rw [heq]
  refine ⟨fun r ↦ ?_⟩
  have hm : Measurable (fun x : M ↦ k * ((dist x y - dist x z) - φ y + φ z)) :=
    ((((continuous_id.dist continuous_const).sub (continuous_id.dist continuous_const)).sub
      continuous_const).add continuous_const).const_mul k |>.measurable
  rw [Measure.map_apply hm (measurableSet_singleton r)]
  have hlevel : (fun x : M ↦ k * ((dist x y - dist x z) - φ y + φ z)) ⁻¹' {r} =
      {x | dist x y - dist x z = r / k + φ y - φ z} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    rw [mul_comm k, ← eq_div_iff hk]
    constructor <;> intro h <;> linarith
  rw [hlevel]
  exact hF.measure_distance_sub_eq_zero m μ hdim hchart hcomplete hyz _

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
