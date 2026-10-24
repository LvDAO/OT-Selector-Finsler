import OTSelector.Reconstruction.EndpointPhysicalKernelDoublePole
import OTSelector.Reconstruction.ActualJacobiKernelRightDoublePole

/-!
# Double pole of the actual original Finsler endpoint kernel in physical time

The selected actual graph supplies its closed Hamiltonian system. Reparameterizing by its
unchanged original physical clock and true speed gives a closed system whose mobility is
exactly the original intrinsic label Hessian inverse. Its coefficients are internally
smooth through the endpoint, so the actual primitive/second-solution argument applies.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E W V M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {A : E≃L[ℝ](ℝ×V)}
  {w : W} {old : M} {t₀ : ℝ}
  {initial : M} {tᵢ : ℝ} {z₀ : E×(E→L[ℝ]ℝ)}
  {R₀ : W→L[ℝ]E} {Q₀ : W→L[ℝ]E→L[ℝ]ℝ}

/-- Actual original Finsler endpoint data produce the exact physical-clock double pole
with a remainder smooth through the endpoint. Smooth coefficients, smooth second solution
and absence of a simple-pole term are conclusions of the construction. -/
theorem exists_actual_physical_kernel_right_double_pole
    (C : F.SmoothPhaseJetComparison initial tᵢ w z₀ R₀ Q₀)
    (G : EndpointGraphData F A C.curve C.labels w old t₀)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {l h : ℝ} (hlh : l<h) (hI : ∀t∈Icc l h, (w,t)∈G.U) :
    let γ := fun q : W×ℝ ↦ A (extChartAt 𝓘(ℝ,E) old (C.curve q.1 q.2))
    let s := fun t ↦ (γ (w,t)).1
    let Ψ := F.adaptedGraphPhase old A γ G.e
    let J := fun r ↦ vectorFamilyMatrix bV
      (fun j ↦ (fderiv ℝ (fun z ↦ Ψ (z,r)) w (bW j)).1)
    (∀t∈Ioo l h, (J (s t)).det≠0) →
    ∃ ε : ℝ, ε>0 ∧ ε<h-l ∧ ∃ (Gres : Matrix ι ι ℝ) (Rem : ℝ→Matrix ι ι ℝ),
      ContDiffOn ℝ ∞ Rem (Ioo (-ε) ε) ∧ ∀ r∈Ioo 0 ε,
        (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w,h-r))⁻¹ =
          (r^2)⁻¹•Gres+Rem r := by
  let γ := fun q : W×ℝ ↦ A (extChartAt 𝓘(ℝ,E) old (C.curve q.1 q.2))
  let s := fun t ↦ (γ (w,t)).1
  let v := fun t ↦ (fderiv ℝ γ (w,t) (0,1)).1
  let L := F.adaptedGraphLagrangian old A
  let Ψ := F.adaptedGraphPhase old A γ G.e
  let Z := fun r ↦ fderiv ℝ (fun z ↦ Ψ (z,r)) w
  let J := fun r ↦ vectorFamilyMatrix bV (fun j ↦ (Z r (bW j)).1)
  let P := fun r ↦ covectorFamilyMatrix bV (fun j ↦ (Z r (bW j)).2)
  let AA := fun r ↦ hamiltonianMatrixA bV (GraphHamiltonian.blockA L G.g r (Ψ (w,r)))
  let BB := fun r ↦ hamiltonianMatrixB bV (GraphHamiltonian.blockB L G.g r (Ψ (w,r)))
  let CC := fun r ↦ hamiltonianMatrixC bV (GraphHamiltonian.blockC L G.g r (Ψ (w,r)))
  dsimp only
  intro hdet
  have hγ (t : ℝ) (ht : t∈Icc l h) : DifferentiableAt ℝ γ (w,t) :=
    (G.position_C2.contDiffAt (G.open_U.mem_nhds (hI t ht))).differentiableAt (by norm_num)
  have hsource (t : ℝ) (ht : t∈Icc l h) := G.source_U (hI t ht)
  have hclock : ∀t∈Icc l h, HasDerivAt s (v t) t :=
    fun t ht ↦ curveGraphClock_hasDerivAt (hγ t ht)
  have hvpos : ∀t∈Icc l h, 0<v t := fun t ht ↦ (G.regular (w,t) (hI t ht)).1
  have himage := (curveGraphClock_closedInverse_data G.raw.1 hlh.le hsource hγ
    (fun t ht ↦ hvpos t (Ioo_subset_Icc_self ht))).1
  have hmaps : MapsTo s (Icc l h) (Icc (s l) (s h)) := by
    intro t ht
    rw [← himage]
    exact mem_image_of_mem s ht
  have Hgraph : ClosedHamiltonianJacobiSystem J P AA BB CC (s l) (s h) :=
    G.closedJacobiSystem hF bW bV (G.closedGraphInterval_subset_phase hlh.le hI)
  have Hphys := Hgraph.physicalClock hclock (G.continuousOn_clockSpeed hI) hvpos hmaps
  obtain ⟨hAs,hBs,hCs⟩ := G.contDiffOn_actual_physical_matrix_coefficients C hF bV
  let U := {t : ℝ | (w,t)∈G.U}
  have hU : IsOpen U := G.open_U.preimage (continuous_const.prodMk continuous_id)
  have hhU : h∈U := hI h ⟨hlh.le,le_rfl⟩
  have hmid : (l+h)/2∈Ioo l h := ⟨by linarith,by linarith⟩
  obtain ⟨ε,hε,hεh,Gres,Rem,hRem,hpole⟩ :=
    Hphys.exists_actual_right_kernel_double_pole hdet hmid hU hhU hAs hBs hCs
  refine ⟨ε,hε,hεh,Gres,Rem,hRem,fun r hr ↦ ?_⟩
  have hlr : h-r∈Ioo l h := ⟨by linarith [hr.2],by linarith [hr.1]⟩
  have hkeq := G.intrinsic_kernel_eq C hF bW bV (hI (h-r) (Ioo_subset_Icc_self hlr))
    (hdet (h-r) hlr)
  rw [hkeq]
  simpa only [Function.comp_def,Matrix.mul_smul,Matrix.smul_mul] using hpole r hr

end OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
