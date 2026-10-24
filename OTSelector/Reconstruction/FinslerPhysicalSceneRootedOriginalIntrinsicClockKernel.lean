import OTSelector.Reconstruction.OriginalSeedPairCoefficientContinuity
import OTSelector.Geometry.Finsler.SeedCalibrationSpan
import Mathlib.Topology.Algebra.Order.UpperLower

/-!
# Original coefficient geometry throughout its calibrated clock interior

The same original phase jet and physical Jacobian are already defined at every
interior calibrated time. Their actual regularity therefore applies to any
compact clock window inside that interior, independently of the auxiliary
conditional support window used to construct a finite population core.
-/

open Set Function Matrix Module Manifold MeasureTheory
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

/-- The same complete calibrated curve has an interval of calibrated times,
and its interior is still an interval. -/
theorem original_calibrationInterior_ordConnected
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels) : OrdConnected (interior (S.calibrationTimes w)) := by
  have hcal : OrdConnected (S.calibrationTimes w) :=
    ⟨fun _ hx _ hy ↦ S.Icc_subset_calibrationTimes hF hu hw hx hy⟩
  exact hcal.interior

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual original kernel is continuous and positive on the entire
calibrated interior, using its original phase jet and physical Jacobian. -/
theorem original_kernel_regular_calibrationInterior
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ContinuousOn (originalSeedKernel S w) (interior (S.calibrationTimes w)) ∧
      ∀ t ∈ interior (S.calibrationTimes w), (originalSeedKernel S w t).PosDef := by
  rw [D.original_kernel_eq hF hw]
  exact D.comparison.continuousOn_posDef_intrinsicKernel_of_original hF
    (Module.finBasis ℝ S.covector.ker) S.normalization D.curve_eq
    (fun old t _ hx ↦ D.phase_jet old t hx)
    (fun old t ht hx ↦ D.jacobian_pos old t ht hx)

/-- Any two strictly ordered original potential times inside the same actual
calibrated interior have positive definite compliance and coefficient. -/
theorem pair_compliance_posDef_calibrationInterior
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels) {x y : ℝ}
    (hx : x - S.level ∈ interior (S.calibrationTimes w))
    (hy : y - S.level ∈ interior (S.calibrationTimes w)) (hxy : x < y) :
    (∫ t in (x - S.level)..(y - S.level), originalSeedKernel S w t).PosDef ∧
      (originalSeedPairCoefficient S w (x, y)).PosDef := by
  have hsub := (original_calibrationInterior_ordConnected hF hu hw).out hx hy
  have hK := D.original_kernel_regular_calibrationInterior hF hw
  have hp := posDef_intervalIntegral (sub_lt_sub_right hxy _) (hK.1.mono hsub)
    (fun t ht ↦ hK.2 t (hsub ht))
  exact ⟨hp, hp.inv⟩

/-- Continuity on a compact original clock window requires only containment
inside the actual calibrated interior. The original conditional support span
need not be a common enclosing window for other target choices. -/
theorem continuousOn_pair_coefficient_calibrationInterior_window
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {l r : ℝ} (hlr : l ≤ r)
    (hwindow : Icc (l - S.level) (r - S.level) ⊆ interior (S.calibrationTimes w)) :
    ContinuousOn (originalSeedPairCoefficient S w)
      {p | p.1 ∈ Icc l r ∧ p.2 ∈ Icc l r ∧ p.1 < p.2} := by
  have hK := D.original_kernel_regular_calibrationInterior hF hw
  exact continuousOn_inverseScalarIntervalCompliance hlr (hK.1.mono hwindow)
    (fun t ht ↦ hK.2 t (hwindow ht))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
