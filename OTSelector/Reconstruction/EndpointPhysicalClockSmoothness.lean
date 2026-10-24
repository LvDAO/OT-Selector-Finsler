import OTSelector.Reconstruction.EndpointGraphCoefficientSmoothness
import OTSelector.Reconstruction.EndpointGraphIntrinsicKernel
import OTSelector.Reconstruction.EndpointGraphMomentWindow

/-!
# Smooth actual physical clock and unchanged reparameterized coefficients

The original complete Finsler comparison is a genuine Euler-Lagrange curve. Its actual
chart position is smooth, so its selected positive graph clock and its true speed are
smooth in the original physical time. Composing the same graph Hamiltonian coefficients
and multiplying by that same speed gives smooth physical-clock coefficients.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
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
  {R : W→L[ℝ]E} {Q : W→L[ℝ]E→L[ℝ]ℝ}

/-- Both the actual original graph clock and its unchanged speed are smooth on the retained
physical source, including its actual endpoint. The speed is proved to be its derivative. -/
theorem contDiffOn_actual_clock_and_speed
    (C : F.SmoothPhaseJetComparison initial tᵢ w z₀ R Q)
    (G : EndpointGraphData F A C.curve C.labels w old t₀) (hF : F.IsSmoothStronglyConvex) :
    let γ := fun q : W×ℝ ↦ A (extChartAt 𝓘(ℝ,E) old (C.curve q.1 q.2))
    let I := {t : ℝ | (w,t)∈G.U}
    ContDiffOn ℝ ∞ (fun t ↦ (γ (w,t)).1) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ (fderiv ℝ γ (w,t) (0,1)).1) I := by
  let I := {t : ℝ | (w,t)∈G.U}
  let γ := fun q : W×ℝ ↦ A (extChartAt 𝓘(ℝ,E) old (C.curve q.1 q.2))
  have hI : IsOpen I := G.open_U.preimage (continuous_const.prodMk continuous_id)
  have hcoord : ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ,E) old ∘ C.curve w) I :=
    (hF.chartEulerLagrange_of_isEulerLagrangeOn
      (fun t (_ : t∈I) ↦ C.complete w C.anchor_mem t (mem_univ _)) old
      (fun t ht ↦ G.curve_source (w,t) ht)).1
  have hclock : ContDiffOn ℝ ∞ (fun t ↦ (γ (w,t)).1) I :=
    (A.contDiff.comp_contDiffOn hcoord).fst
  refine ⟨hclock,?_⟩
  apply (hclock.deriv_of_isOpen hI (by simp)).congr
  intro t ht
  have hd := curveGraphClock_hasDerivAt
    ((G.position_C2.contDiffAt (G.open_U.mem_nhds ht)).differentiableAt (by norm_num))
  exact hd.deriv.symm

/-- Every actual physical-clock Hamiltonian matrix coefficient is smooth through the
selected original endpoint; the clock, speed, graph and Legendre branch are unchanged. -/
theorem contDiffOn_actual_physical_matrix_coefficients
    (C : F.SmoothPhaseJetComparison initial tᵢ w z₀ R Q)
    (G : EndpointGraphData F A C.curve C.labels w old t₀)
    (hF : F.IsSmoothStronglyConvex) (bV : Basis ι ℝ V) :
    let γ := fun q : W×ℝ ↦ A (extChartAt 𝓘(ℝ,E) old (C.curve q.1 q.2))
    let s := fun t ↦ (γ (w,t)).1
    let v := fun t ↦ (fderiv ℝ γ (w,t) (0,1)).1
    let L := F.adaptedGraphLagrangian old A
    let Ψ := F.adaptedGraphPhase old A γ G.e
    let I := {t : ℝ | (w,t)∈G.U}
    ContDiffOn ℝ ∞ (fun t ↦ v t•hamiltonianMatrixA bV
      (GraphHamiltonian.blockA L G.g (s t) (Ψ (w,s t)))) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ v t•hamiltonianMatrixB bV
        (GraphHamiltonian.blockB L G.g (s t) (Ψ (w,s t)))) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ v t•hamiltonianMatrixC bV
        (GraphHamiltonian.blockC L G.g (s t) (Ψ (w,s t)))) I := by
  obtain ⟨hA,hB,hC⟩ := G.contDiffOn_actual_matrix_coefficients hF bV
  obtain ⟨hs,hv⟩ := G.contDiffOn_actual_clock_and_speed C hF
  have hmaps : MapsTo (fun t ↦ (A (extChartAt 𝓘(ℝ,E) old (C.curve w t))).1)
      {t : ℝ | (w,t)∈G.U} {s : ℝ | (w,s)∈G.D} := fun t ht ↦ G.clock_mem_phase ht
  exact ⟨hv.smul (hA.comp hs hmaps),hv.smul (hB.comp hs hmaps),hv.smul (hC.comp hs hmaps)⟩

end OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
