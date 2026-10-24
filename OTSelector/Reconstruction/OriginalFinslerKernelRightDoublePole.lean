import OTSelector.Reconstruction.EndpointPhysicalKernelRightDoublePole
import OTSelector.Reconstruction.OriginalFocalPositiveResidue

/-!
# The actual original right-endpoint pole and positivity of both endpoint residues

The same actual right endpoint chart and original physical clock yield the inward-distance
double pole. Positivity of its fixed residue is derived from that original positive kernel.
No new endpoint, coefficient, phase-rank or residue assumption is introduced.
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

/-- The exact actual original inward-distance double pole at the right support endpoint,
with all graph, physical clock, smoothness and phase data produced internally. -/
theorem exists_original_kernel_right_double_pole
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (R : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧ ∀ s∈Ioo 0 ε,
        originalSeedKernel S w (D.hi-s)=(s^2)⁻¹•G+R s := by
  let bW := Module.finBasis ℝ S.covector.ker
  obtain ⟨L,H,l,h,hlo,hlhi,hloh,hhi,hL,hH⟩ :=
    S.exists_seedEndpointCharts D.comparison hF hw D.curve_eq D.support.lt
  have hactive : Ioo D.lo D.hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.support.calibrated
  have hdet (t : ℝ) (ht : t∈Ioo h D.hi) :
      (H.jacobiPositionMatrix bW (H.clock t)).det≠0 := by
    have htIcc := Ioo_subset_Icc_self ht
    have hx := H.geometry.curve_source (w,t) (hH t htIcc)
    rw [← D.curve_eq] at hx
    have hjet := D.phase_jet H.old t hx
    have hpos := D.jacobian_pos H.old t (hactive ⟨hloh.trans ht.1,ht.2⟩) hx
    exact H.jacobiPositionMatrix_det_ne_zero bW D.curve_eq (hH t htIcc) hjet.1 hjet.2 hpos
  obtain ⟨ε,hε,hεh,G,R,hR,hpole⟩ :=
    H.geometry.exists_actual_physical_kernel_right_double_pole D.comparison hF bW
      (H.spatialBasis bW) hhi hH hdet
  refine ⟨ε,hε,by linarith,G,R,hR,fun s hs ↦ ?_⟩
  rw [D.original_kernel_eq hF hw]
  exact hpole s hs

/-- The actual original right residue is positive semidefinite by the same original
squared-distance rescaling limit, with no new final residue assumption. -/
theorem exists_original_kernel_right_positive_double_pole
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (R : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧ ∀ s∈Ioo 0 ε,
        originalSeedKernel S w (D.hi-s)=(s^2)⁻¹•G+R s := by
  obtain ⟨ε,hε,hεh,G,R,hR,hpole⟩ := D.exists_original_kernel_right_double_pole hF hw
  refine ⟨ε,hε,hεh,G,R,?_,hR,hpole⟩
  apply posSemidef_of_positive_doublePole hε
    (hR.continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hε))
    (W := fun s ↦ originalSeedKernel S w (D.hi-s)) ?_ hpole
  intro s hs
  exact ((D.original_kernel_regular hF hw).2 (D.hi-s)
    ⟨by linarith [hs.2],by linarith [hs.1]⟩).posSemidef

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
