import OTSelector.Reconstruction.OriginalKernelUniformLower

/-!
# The actual original inverse mobility stays bounded through focal endpoints

The original comparison length Hessian is continuous on the unchanged compact support
span. At every actual regular interior time it is exactly the inverse of the original
mobility. Compactness therefore bounds that same physical inverse uniformly, including
interior times arbitrarily close to either focal endpoint.
-/

open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The inverse of the unchanged original kernel is its actual original length Hessian. -/
theorem original_kernel_inverse_eq_lengthHessian
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) {t : ℝ} (ht : t∈Ioo D.lo D.hi) :
    (originalSeedKernel S w t)⁻¹=F.familyLabelHessianMatrix
      (Module.finBasis ℝ S.covector.ker) (fun q ↦ D.comparison.curve q.1 q.2) (w,t) := by
  let H := F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
    (fun q ↦ D.comparison.curve q.1 q.2) (w,t)
  have hKeq : originalSeedKernel S w t=H⁻¹ := congrFun (D.original_kernel_eq hF hw) t
  have hH : H.PosDef := Matrix.posDef_inv_iff.mp (by
    rw [←hKeq]
    exact (D.original_kernel_regular hF hw).2 t ht)
  rw [hKeq]
  exact Matrix.nonsing_inv_nonsing_inv H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')

/-- A single internally produced constant bounds the same physical inverse kernel over
the entire original open span. Endpoint singularities require no inverse endpoint value. -/
theorem exists_original_kernel_inverse_wholeSpan_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ H : ℝ, H≥0 ∧ ∀t∈Ioo D.lo D.hi, ‖(originalSeedKernel S w t)⁻¹‖≤H := by
  let A := fun t : ℝ ↦ F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
    (fun q ↦ D.comparison.curve q.1 q.2) (w,t)
  have hA : Continuous A := continuous_iff_continuousAt.mpr
    (fun t ↦ D.comparison.continuousAt_labelHessian hF (Module.finBasis ℝ S.covector.ker) t)
  obtain ⟨H,hbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hA.continuousOn
  refine ⟨max H 0,le_max_right _ _,fun t ht ↦ ?_⟩
  rw [D.original_kernel_inverse_eq_lengthHessian hF hw ht]
  exact (hbound t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
