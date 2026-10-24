import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIntrinsicClockWindows
import OTSelector.Reconstruction.FinslerQuadraticCostDifferenceContinuity

/-!
# Original coefficient geometry throughout its calibrated clock interior

The same original phase jet and physical Jacobian are already defined at every
interior calibrated time. Their actual regularity therefore applies to any
compact clock window inside that interior, independently of the auxiliary
conditional support window used to construct a finite population core.
-/

open Set Function Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The original coefficient is continuous throughout its entire open
calibrated legal clock domain. Each point uses its own original compact window. -/
theorem continuousOn_pair_coefficient_calibrationInterior
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels) :
    ContinuousOn (originalSeedPairCoefficient S w)
      {p | p.1 - S.level ∈ interior (S.calibrationTimes w) ∧
        p.2 - S.level ∈ interior (S.calibrationTimes w) ∧ p.1 < p.2} := by
  intro p hp
  obtain ⟨q, hwindow, hxy, _⟩ :=
    exists_original_calibrationInterior_window_for_two_targets hF hu hw
      (x := ((0 : Fin 1 → ℝ), p.1)) (y := ((0 : Fin 1 → ℝ), p.2))
      (z := ((0 : Fin 1 → ℝ), p.2)) hp.1 hp.2.1 hp.2.1 hp.2.2 hp.2.2
  have hx : (q.val.1 : ℝ) < p.1 ∧ p.1 < (q.val.2.1 : ℝ) := hxy.1
  have hy : (q.val.1 : ℝ) < p.2 ∧ p.2 < (q.val.2.1 : ℝ) := hxy.2.1
  have hlr : (q.val.1 : ℝ) ≤ (q.val.2.1 : ℝ) := by exact_mod_cast q.property.1.le
  have hc := D.continuousOn_pair_coefficient_calibrationInterior_window hF hw hlr hwindow
  have hneigh : {r : ℝ × ℝ | r.1 ∈ Icc (q.val.1 : ℝ) q.val.2.1 ∧
      r.2 ∈ Icc (q.val.1 : ℝ) q.val.2.1 ∧ r.1 < r.2} ∈ 𝓝 p :=
    inter_mem
      (continuousAt_fst.preimage_mem_nhds (Icc_mem_nhds hx.1 hx.2))
      (inter_mem
        (continuousAt_snd.preimage_mem_nhds (Icc_mem_nhds hy.1 hy.2))
        ((isOpen_lt continuous_fst continuous_snd).mem_nhds hp.2.2))
  exact (hc.continuousAt hneigh).continuousWithinAt

/-- The SAME original quadratic cost is jointly continuous on the actual
calibrated legal domain, with its true clock-dependent inverse compliance. -/
theorem continuousOn_quadratic_cost_calibrationInterior
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels) :
    ContinuousOn (fun p : ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ) ×
        ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ) ↦
      matrixQuadratic (originalSeedPairCoefficient S w (p.1.2, p.2.2))
        (p.2.1 - p.1.1))
      {p | p.1.2 - S.level ∈ interior (S.calibrationTimes w) ∧
        p.2.2 - S.level ∈ interior (S.calibrationTimes w) ∧ p.1.2 < p.2.2} := by
  let X := (Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ
  have hclock : Continuous (fun p : X × X ↦ (p.1.2, p.2.2)) :=
    (continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)
  have hdelta : Continuous (fun p : X × X ↦ p.2.1 - p.1.1) :=
    (continuous_fst.comp continuous_snd).sub (continuous_fst.comp continuous_fst)
  have hA := (D.continuousOn_pair_coefficient_calibrationInterior hF hu hw).comp
    hclock.continuousOn (fun _ hp ↦ hp)
  exact continuous_matrixQuadratic.comp_continuousOn (hA.prodMk hdelta.continuousOn)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
