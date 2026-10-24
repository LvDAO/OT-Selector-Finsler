import OTSelector.Geometry.FinslerComparisonIntrinsicHessian

/-!
# The same intrinsic comparison kernel in each actual graph chart

Each genuine local graph clock represents the inverse of one chart-independent label
Hessian along the complete comparison. The same label basis and true clock speed remain
explicit, so endpoint charts and interior charts can share one original-time kernel.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.SmoothPhaseJetComparison

set_option backward.isDefEq.respectTransparency false

variable {E W V M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}
  {initial : M} {t₀ : ℝ} {w₀ : W} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}
  (C : F.SmoothPhaseJetComparison initial t₀ w₀ z₀ R Q)

/-- The same complete comparison read in one genuine manifold chart. -/
def chartReadout (old : M) (q : W × ℝ) : E :=
  extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2)

/-- Any actual local graph chart expresses the same intrinsic inverse label Hessian
as its speed times the same graph Jacobi compliance integrand. -/
theorem intrinsic_label_inverse_eq_graph_blockC
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) (t : ℝ)
    (hx : C.curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (A ∘ C.chartReadout old))
    (hz : (w₀, t) ∈ e.source)
    (hv : 0 < (fderiv ℝ (A ∘ C.chartReadout old) (w₀, t) (0, 1)).1)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old A))
    (hsub : g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    (hsource : graphVelocityPhase
      (fun z ↦ (curveGraphPosition (A ∘ C.chartReadout old) e z).2)
      (w₀, (A (C.chartReadout old (w₀, t))).1) ∈ g.source)
    (hJ : (vectorFamilyMatrix bV (fun j ↦ fderiv ℝ
      (fun z ↦ (curveGraphPosition (A ∘ C.chartReadout old) e
        (z, (A (C.chartReadout old (w₀, t))).1)).2) w₀ (bW j))).det ≠ 0) :
    let s := (A (C.chartReadout old (w₀, t))).1
    let Ψ := F.adaptedGraphPhase old A (A ∘ C.chartReadout old) e
    let J := vectorFamilyMatrix bV (fun j ↦ fderiv ℝ
      (fun z ↦ (curveGraphPosition (A ∘ C.chartReadout old) e (z, s)).2) w₀ (bW j))
    let B := hamiltonianMatrixC bV
      (GraphHamiltonian.blockC (F.adaptedGraphLagrangian old A) g s (Ψ (w₀, s)))
    (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t))⁻¹ =
      (fderiv ℝ (A ∘ C.chartReadout old) (w₀, t) (0, 1)).1 • (J⁻¹ * B * J⁻¹ᵀ) := by
  have hC2 := hF.contDiffAt_chartMomentumFamily_of_tangentFamily C.open_labels
    C.complete C.tangent_C2 C.anchor_mem old t hx
  have hd : DifferentiableAt ℝ (C.chartReadout old) (w₀, t) :=
    hC2.fst.differentiableAt (by norm_num)
  have hK : F.chartFamilyLabelHessianMatrix old bW (C.chartReadout old) (w₀, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t) :=
    C.chart_labelHessian_eq_intrinsic hF old bW C.anchor_mem t hx
  rw [← hK]
  exact hF.chartFamilyLabelHessian_inverse_eq_graph_blockC old A bW bV rfl
    hd.hasFDerivAt hd he hz hv hg hsub hG hsource hJ

end OTSelector.Geometry.ContinuousFinslerNorm.SmoothPhaseJetComparison
