import OTSelector.Reconstruction.EndpointGraphJacobiSystem
import OTSelector.Geometry.FinslerComparisonGraphKernel

/-!
# The intrinsic original kernel in the selected endpoint frame

The endpoint record keeps the source witness for its original Legendre inverse.
The comparison's intrinsic label Hessian inverse therefore equals the clock speed
times the compliance integrand of this very same phase matrix and branch.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData

set_option backward.isDefEq.respectTransparency false

variable {E W V M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {A : E ≃L[ℝ] (ℝ × V)}
  {Γ : W → ℝ → M} {B : Set W} {w : W} {old : M} {t₀ : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] in
/-- Label differentiability follows from the selected record's actual C² phase. -/
theorem phase_label_differentiable
    (G : EndpointGraphData F A Γ B w old t₀) {s : ℝ} (hs : (w, s) ∈ G.D) :
    DifferentiableAt ℝ (fun z ↦ F.adaptedGraphPhase old A
      (fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))) G.e (z, s)) w := by
  obtain ⟨_, _, _, _, _, _, hD, _, _, hΨ, _, _⟩ := G.raw
  have hinner : DifferentiableAt ℝ (fun z : W ↦ (z, s)) w :=
    differentiableAt_id.prodMk (differentiableAt_const s)
  exact ((hΨ.contDiffAt (hD.mem_nhds hs)).differentiableAt (by norm_num)).comp w hinner

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] in
/-- Original physical times in the selected regular source land in its same phase domain. -/
theorem clock_mem_phase
    (G : EndpointGraphData F A Γ B w old t₀) {t : ℝ} (ht : (w, t) ∈ G.U) :
    (w, (A (extChartAt 𝓘(ℝ, E) old (Γ w t))).1) ∈ G.D := by
  have h := G.mapsTo_phase ht
  simpa only [G.raw.1, curveGraphCoordinateMap] using h

variable {initial : M} {tᵢ : ℝ} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}

/-- The intrinsic inverse label Hessian uses the actual positive speed, the same
phase-position matrix and the same original graph Hamiltonian inverse block. -/
theorem intrinsic_kernel_eq
    (C : F.SmoothPhaseJetComparison initial tᵢ w z₀ R Q)
    (G : EndpointGraphData F A C.curve C.labels w old t₀)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {t : ℝ} (ht : (w, t) ∈ G.U)
    (hdet : (vectorFamilyMatrix bV (fun j ↦
      (fderiv ℝ (fun z ↦ F.adaptedGraphPhase old A
        (fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2))) G.e
        (z, (A (extChartAt 𝓘(ℝ, E) old (C.curve w t))).1)) w (bW j)).1)).det ≠ 0) :
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2))
    let s := (γ (w, t)).1
    let Ψ := F.adaptedGraphPhase old A γ G.e
    let J := vectorFamilyMatrix bV (fun j ↦ (fderiv ℝ (fun z ↦ Ψ (z, s)) w (bW j)).1)
    let B := hamiltonianMatrixC bV
      (GraphHamiltonian.blockC (F.adaptedGraphLagrangian old A) G.g s (Ψ (w, s)))
    (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w, t))⁻¹ =
      (fderiv ℝ γ (w, t) (0, 1)).1 • (J⁻¹ * B * J⁻¹ᵀ) := by
  obtain ⟨he, _, _, hg, hsub, hG, _, _, _, _, hJacobi, _⟩ := G.raw
  have hs := G.clock_mem_phase ht
  have hphase := G.phase_label_differentiable hs
  have hJ := F.adaptedGraphPhase_position_matrix_eq old A bW bV _ G.e hphase
  have hdet' := hdet
  rw [← hJ] at hdet'
  have hk := C.intrinsic_label_inverse_eq_graph_blockC hF old A bW bV t
    (G.curve_source _ ht) he (G.source_U ht) (G.regular _ ht).1 hg hsub hG
    (hJacobi _ hs).1 hdet'
  dsimp only at hk ⊢
  simp only [SmoothPhaseJetComparison.chartReadout, Function.comp_def] at hk
  rw [hJ] at hk
  exact hk

end OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
