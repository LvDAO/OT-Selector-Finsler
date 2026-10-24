import OTSelector.Reconstruction.EndpointPhysicalKernelDoublePole
import OTSelector.Reconstruction.OriginalSeedCompliance
import OTSelector.Reconstruction.SeedEndpointJacobiDensity

/-!
# Exact left-endpoint double pole of the original Finsler length kernel

The actual original conditional geometry constructs its own endpoint graph from the
original seed cover. Original positive physical Jacobians internally give the original
interior position determinants. The actual graph, its original physical clock and its
same Legendre branch then produce the exact double pole of the original length kernel.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original Finsler kernel has a fixed double pole plus a remainder smooth
through its actual left support endpoint. All graph, clock, coefficient, crossing and
second-solution smoothness data are produced internally from the original geometry. -/
theorem exists_original_kernel_left_double_pole
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (R : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧ ∀ s∈Ioo 0 ε,
        originalSeedKernel S w (D.lo+s)=(s^2)⁻¹•G+R s := by
  let bW := Module.finBasis ℝ S.covector.ker
  obtain ⟨L,H,l,h,hlo,hlhi,hloh,hhi,hL,hH⟩ :=
    S.exists_seedEndpointCharts D.comparison hF hw D.curve_eq D.support.lt
  have hactive : Ioo D.lo D.hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.support.calibrated
  have hdet (t : ℝ) (ht : t∈Ioo D.lo l) :
      (L.jacobiPositionMatrix bW (L.clock t)).det≠0 := by
    have htIcc := Ioo_subset_Icc_self ht
    have hx := L.geometry.curve_source (w,t) (hL t htIcc)
    rw [← D.curve_eq] at hx
    have hjet := D.phase_jet L.old t hx
    have hpos := D.jacobian_pos L.old t (hactive ⟨ht.1,ht.2.trans hlhi⟩) hx
    exact L.jacobiPositionMatrix_det_ne_zero bW D.curve_eq (hL t htIcc) hjet.1 hjet.2 hpos
  obtain ⟨ε,hε,hεl,G,R,hR,hpole⟩ :=
    L.geometry.exists_actual_physical_kernel_left_double_pole D.comparison hF bW
      (L.spatialBasis bW) hlo hL hdet
  refine ⟨ε,hε,by linarith,G,R,hR,fun s hs ↦ ?_⟩
  rw [D.original_kernel_eq hF hw]
  exact hpole s hs

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
