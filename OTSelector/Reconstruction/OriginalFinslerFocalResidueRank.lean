import OTSelector.Reconstruction.EndpointPhysicalKernelResidueRank
import OTSelector.Reconstruction.EndpointPhysicalKernelRightResidueRank
import OTSelector.Reconstruction.OriginalSeedCompliance
import OTSelector.Reconstruction.SeedEndpointJacobiDensity

/-!
# Original focal residues retain their actual endpoint Jacobi rank

The original conditional data supplies the same endpoint charts used by the original
physical Jacobian and density. Any smooth double-pole expansion of its unchanged kernel
has residue rank equal to the actual selected endpoint Jacobi nullity. The conclusion
applies to the same residue already used by the actual normalized phase estimates.
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

/-- The same actual left kernel residue has the actual selected endpoint nullity. -/
theorem original_left_doublePole_rank_in_endpointChart
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {ε : ℝ} (hε : 0<ε)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {Rem : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀s∈Ioo 0 ε, originalSeedKernel S w (D.lo+s)=(s^2)⁻¹•G+Rem s) :
    ∃ L : SeedEndpointChart S D.comparison D.lo,
      G.rank=Module.finrank ℝ (LinearMap.ker
        (L.jacobiPositionMatrix (Module.finBasis ℝ S.covector.ker) (L.clock D.lo)).mulVecLin) := by
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
  refine ⟨L,?_⟩
  apply L.geometry.actual_physical_kernel_left_doublePole_rank D.comparison hF bW
    (L.spatialBasis bW) hlo hL hdet hε hRem
  intro r hr
  have hp := hpole r hr
  rw [D.original_kernel_eq hF hw] at hp
  exact hp

/-- The same actual right kernel residue has the actual selected endpoint nullity. -/
theorem original_right_doublePole_rank_in_endpointChart
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {ε : ℝ} (hε : 0<ε)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {Rem : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀s∈Ioo 0 ε, originalSeedKernel S w (D.hi-s)=(s^2)⁻¹•G+Rem s) :
    ∃ L : SeedEndpointChart S D.comparison D.hi,
      G.rank=Module.finrank ℝ (LinearMap.ker
        (L.jacobiPositionMatrix (Module.finBasis ℝ S.covector.ker) (L.clock D.hi)).mulVecLin) := by
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
  refine ⟨H,?_⟩
  apply H.geometry.actual_physical_kernel_right_doublePole_rank D.comparison hF bW
    (H.spatialBasis bW) hhi hH hdet hε hRem
  intro r hr
  have hp := hpole r hr
  rw [D.original_kernel_eq hF hw] at hp
  exact hp

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
