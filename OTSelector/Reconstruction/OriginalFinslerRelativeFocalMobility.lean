import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole
import OTSelector.Analysis.Asymptotics.DoublePoleRelativeMobilityBounds
import OTSelector.Reconstruction.OriginalKernelInverseUniformBound

/-!
# Actual original Finsler mobility varies slowly on relative focal time bands

The genuine smooth double-pole expansion, the bounded original length Hessian and the
actual regular interior kernel provide every constant internally. The result controls the
literal original physical relative-mobility product at either actual support endpoint.
-/

open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Near the actual original left focal endpoint, physical relative mobility is O(τ) on
relative bands, with all inverse/remainder constants supplied by the original geometry. -/
theorem exists_original_left_focal_relative_mobility_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ η : ℝ, η>0 ∧ η<D.hi-D.lo ∧ ∃ C : ℝ, C>0 ∧
      ∀a∈Ioo 0 η, ∀τ∈Icc (0:ℝ) (1/2), ∀s : ℝ, |s-a|≤τ*a →
        ‖originalSeedKernel S w (D.lo+s)*(originalSeedKernel S w (D.lo+a))⁻¹-1‖≤C*τ := by
  obtain ⟨ε,hε,hεspan,G,R,hR,hpole⟩ := D.exists_original_kernel_left_double_pole hF hw
  obtain ⟨H,hH,hinv⟩ := D.exists_original_kernel_inverse_wholeSpan_bound hF hw
  have hclock : ∀s∈Ioo 0 ε, D.lo+s∈Ioo D.lo D.hi :=
    fun s hs ↦ ⟨by linarith [hs.1],by linarith [hs.2]⟩
  obtain ⟨η,hη,hηε,C,hC,hbound⟩ := exists_doublePole_relative_mobility_bound hε hH hR hpole
    (fun s hs ↦ isUnit_iff_ne_zero.mpr
      ((D.original_kernel_regular hF hw).2 (D.lo+s) (hclock s hs)).det_pos.ne')
    (fun s hs ↦ hinv (D.lo+s) (hclock s hs))
  exact ⟨η,hη,hηε.trans hεspan,C,hC,hbound⟩

/-- The actual original right endpoint has the same physical relative-band estimate in
its true inward-distance clock, allowing focal degeneration at that endpoint. -/
theorem exists_original_right_focal_relative_mobility_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ η : ℝ, η>0 ∧ η<D.hi-D.lo ∧ ∃ C : ℝ, C>0 ∧
      ∀a∈Ioo 0 η, ∀τ∈Icc (0:ℝ) (1/2), ∀s : ℝ, |s-a|≤τ*a →
        ‖originalSeedKernel S w (D.hi-s)*(originalSeedKernel S w (D.hi-a))⁻¹-1‖≤C*τ := by
  obtain ⟨ε,hε,hεspan,G,R,hR,hpole⟩ := D.exists_original_kernel_right_double_pole hF hw
  obtain ⟨H,hH,hinv⟩ := D.exists_original_kernel_inverse_wholeSpan_bound hF hw
  have hclock : ∀s∈Ioo 0 ε, D.hi-s∈Ioo D.lo D.hi :=
    fun s hs ↦ ⟨by linarith [hs.2],by linarith [hs.1]⟩
  obtain ⟨η,hη,hηε,C,hC,hbound⟩ := exists_doublePole_relative_mobility_bound hε hH hR hpole
    (fun s hs ↦ isUnit_iff_ne_zero.mpr
      ((D.original_kernel_regular hF hw).2 (D.hi-s) (hclock s hs)).det_pos.ne')
    (fun s hs ↦ hinv (D.hi-s) (hclock s hs))
  exact ⟨η,hη,hηε.trans hεspan,C,hC,hbound⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
