import OTSelector.Analysis.ODE.GraphHamiltonianCoefficientSmoothness
import OTSelector.Reconstruction.EndpointGraphJacobiSystem

/-!
# Actual endpoint-graph coefficients are smooth through the endpoint

The retained original graph and Legendre branch have smooth field, and their actual C2
phase solves that same equation. Existing time-slice bootstrap gives the actual phase's
smoothness, hence smoothness of the same three fixed-basis Hamiltonian matrix coefficients
on the whole open central graph-time domain, including the selected focal endpoint.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {E W V M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {A : E≃L[ℝ](ℝ×V)}
  {Γ : W→ℝ→M} {B : Set W} {w : W} {old : M} {t₀ : ℝ}

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
/-- Actual endpoint data internally supply smooth matrix coefficients on an open clock
neighborhood. No additional coefficient regularity or extension hypothesis is required. -/
theorem contDiffOn_actual_matrix_coefficients
    (G : EndpointGraphData F A Γ B w old t₀) (hF : F.IsSmoothStronglyConvex)
    (bV : Basis ι ℝ V) :
    let γ := fun q : W×ℝ ↦ A (extChartAt 𝓘(ℝ,E) old (Γ q.1 q.2))
    let L := F.adaptedGraphLagrangian old A
    let Ψ := F.adaptedGraphPhase old A γ G.e
    let I := {s : ℝ | (w,s)∈G.D}
    ContDiffOn ℝ ∞ (fun s ↦ hamiltonianMatrixA bV (GraphHamiltonian.blockA L G.g s (Ψ (w,s)))) I ∧
      ContDiffOn ℝ ∞ (fun s ↦ hamiltonianMatrixB bV (GraphHamiltonian.blockB L G.g s (Ψ (w,s)))) I ∧
      ContDiffOn ℝ ∞ (fun s ↦ hamiltonianMatrixC bV (GraphHamiltonian.blockC L G.g s (Ψ (w,s)))) I := by
  obtain ⟨he,hs,hB,hg,hsub,hG,hD,hcenter,htarget,hΨ,hJacobi,hphase⟩ := G.raw
  let γ := fun q : W×ℝ ↦ A (extChartAt 𝓘(ℝ,E) old (Γ q.1 q.2))
  let L := F.adaptedGraphLagrangian old A
  let Ψ := F.adaptedGraphPhase old A γ G.e
  have hL : ContDiffOn ℝ ∞ L G.g.source :=
    (hF.contDiffOn_adaptedGraphLagrangian old A).mono hsub
  have hODE (q : W×ℝ) (hq : q∈G.D) : HasDerivAt (fun s ↦ Ψ (q.1,s))
      (GraphHamiltonian.field L G.g q.2 (Ψ q)) q.2 := (hJacobi q hq).2.1
  have hp (s : ℝ) (hs : (w,s)∈G.D) : ((s,(Ψ (w,s)).1),(Ψ (w,s)).2)∈G.g.target := by
    have h := G.g.map_source (hJacobi (w,s) hs).1
    rw [hg] at h
    exact h
  have hpath := (contDiffOn_graphHamiltonianFamily_slice hL hG hD hΨ hODE w hp).1
  exact contDiffOn_graphHamiltonian_matrix_coefficients bV hL hG hpath hp

end OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
