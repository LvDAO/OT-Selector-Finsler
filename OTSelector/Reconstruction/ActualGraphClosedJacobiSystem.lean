import OTSelector.Geometry.FinslerSmoothPhaseJetJacobi
import OTSelector.Analysis.ODE.GraphHamiltonianCoefficientContinuity
import OTSelector.Reconstruction.ClosedJacobiConditionalMoments

/-!
# Closed-interval systems from the actual Finsler graph phase

One chosen graph chart supplies both the physical position matrix and the complete
Hamiltonian system on every closed central interval contained in its domain. Endpoint
phase rank, positivity and derivatives follow from the constructed comparison phase;
they are not additional endpoint inputs to the conditional-moment theorem.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W V ι M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M}

omit [DecidableEq ι] in
/-- The actual adapted chart constructs a closed Hamiltonian system in the same
bases and with the same position Jacobian, on every closed interval in its domain. -/
theorem exists_actualGraph_closedJacobiSystem
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {A : E ≃L[ℝ] (ℝ × V)} {Γ : W → ℝ → M} {B : Set W}
    {w₀ : W} {old : M} {t₀ : ℝ}
    (hchart : F.HasAdaptedGraphJacobiChart A Γ B w₀ old t₀) :
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
    let L := F.adaptedGraphLagrangian old A
    ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
      (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
      (D : Set (W × ℝ)),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      (w₀, t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ univ ∧
      (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ ∧
      ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧
      curveGraphCoordinateMap γ (w₀, t₀) ∈ D ∧ D ⊆ e.target ∧
      let Ψ := F.adaptedGraphPhase old A γ e
      let Z := fun r ↦ fderiv ℝ (fun w ↦ Ψ (w, r)) w₀
      let J := fun r ↦ vectorFamilyMatrix bV (fun j ↦ (Z r (bW j)).1)
      let P := fun r ↦ covectorFamilyMatrix bV (fun j ↦ (Z r (bW j)).2)
      let Aₛ := fun s ↦ hamiltonianMatrixA bV (GraphHamiltonian.blockA L g s (Ψ (w₀, s)))
      let Bₛ := fun s ↦ hamiltonianMatrixB bV (GraphHamiltonian.blockB L g s (Ψ (w₀, s)))
      let Cₛ := fun s ↦ hamiltonianMatrixC bV (GraphHamiltonian.blockC L g s (Ψ (w₀, s)))
      ContDiffOn ℝ 2 Ψ D ∧
      (∀ s, (w₀, s) ∈ D → J s = vectorFamilyMatrix bV (fun j ↦
        fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, s)).2) w₀ (bW j))) ∧
      ∀ a b : ℝ, (∀ s ∈ Icc a b, (w₀, s) ∈ D) →
        ClosedHamiltonianJacobiSystem J P Aₛ Bₛ Cₛ a b := by
  obtain ⟨e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget, hΨ, hmat⟩ :=
    hF.adaptedGraphJacobiChart_actual_matrices bW bV hchart
  refine ⟨e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget, hΨ,
    fun s hs ↦ (hmat s hs).2.1, ?_⟩
  intro a b hab
  have hpath : ContinuousOn (fun s ↦ F.adaptedGraphPhase old A
      (fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))) e (w₀, s))
      (Icc a b) :=
    hΨ.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hab
  obtain ⟨hA, hBb, hC⟩ := continuousOn_graphHamiltonian_matrix_coefficients bV
    ((hF.contDiffOn_adaptedGraphLagrangian old A).mono hsub) hG hpath
    (fun s hs ↦ (hmat s (hab s hs)).1)
  exact {
    position_derivative := fun s hs ↦ (hmat s (hab s hs)).2.2.1
    momentum_derivative := fun s hs ↦ (hmat s (hab s hs)).2.2.2.1
    continuous_A := hA
    continuous_B := hBb
    continuous_C := hC
    symmetric_A := fun s hs ↦ (hmat s (hab s hs)).2.2.2.2.1
    symmetric_C := fun s hs ↦ (hmat s (hab s hs)).2.2.2.2.2.1
    positive_C := fun s hs ↦ (hmat s (hab s hs)).2.2.2.2.2.2.1
    wronskian := fun s hs ↦ (hmat s (hab s hs)).2.2.2.2.2.2.2.1
    phase_rank := fun s hs ↦ (hmat s (hab s hs)).2.2.2.2.2.2.2.2.1 }

end OTSelector.Reconstruction
