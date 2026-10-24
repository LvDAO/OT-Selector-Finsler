import OTSelector.Geometry.FinslerSmoothPhaseJetData
import OTSelector.Geometry.FinslerGraphPositionJacobi

/-!
# Actual Jacobi matrices of the complete smooth comparison

The comparison's original momentum selects an adapted clock. Its actual graph phase
then supplies the Hamiltonian matrix equations, zero Wronskian, full stacked phase rank,
and positive inverse graph Hessian. The position matrix is identified with the same
graph-position derivative that occurs in the physical parameter Jacobian.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W V ι M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

namespace SmoothPhaseJetComparison

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Actual comparison momentum chooses the clock and constructs its own graph Jacobi chart. -/
theorem exists_adaptedGraphJacobiChart
    {initial : M} {t₀ : ℝ} {w₀ : W} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}
    (D : F.SmoothPhaseJetComparison initial t₀ w₀ z₀ R Q)
    (hF : F.IsSmoothStronglyConvex) (old : M) (t : ℝ)
    (hx : D.curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    let x := extChartAt 𝓘(ℝ, E) old ∘ D.curve w₀
    let p := fiberLegendre (F.chartEnergy old) (x t, deriv x t)
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
      ∃ A : E ≃L[ℝ] (ℝ × p.ker), A (deriv x t) = (1, 0) ∧
        F.HasAdaptedGraphJacobiChart A D.curve D.labels w₀ old t :=
  hF.exists_completeFamily_adaptedGraphStructure D.open_labels D.complete D.tangent_C2
    D.energy_eq D.anchor_mem D.phase_rank D.phase_isotropic D.normal old t hx

end SmoothPhaseJetComparison

namespace IsSmoothStronglyConvex

variable [Fintype ι]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] in
/-- The constructed chart supplies the very same graph-position Jacobi matrix as the
physical Jacobian formula, together with its actual Hamiltonian system and phase structure. -/
theorem adaptedGraphJacobiChart_actual_matrices
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {A : E ≃L[ℝ] (ℝ × V)} {Γ : W → ℝ → M} {B : Set W}
    {w₀ : W} {old : M} {t₀ : ℝ}
    (hchart : F.HasAdaptedGraphJacobiChart A Γ B w₀ old t₀) :
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
    let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
    let L := F.adaptedGraphLagrangian old A
    ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
      (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
      (D : Set (W × ℝ)),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      (w₀, t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ univ ∧
      (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ ∧
      ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
      ContDiffOn ℝ 2 (F.adaptedGraphPhase old A γ e) D ∧
      ∀ s : ℝ, (w₀, s) ∈ D →
        let Ψ := F.adaptedGraphPhase old A γ e
        let Z := fun r ↦ fderiv ℝ (fun w ↦ Ψ (w, r)) w₀
        let J := fun r ↦ vectorFamilyMatrix bV (fun j ↦ (Z r (bW j)).1)
        let P := fun r ↦ covectorFamilyMatrix bV (fun j ↦ (Z r (bW j)).2)
        let Aₛ := hamiltonianMatrixA bV (GraphHamiltonian.blockA L g s (Ψ (w₀, s)))
        let Bₛ := hamiltonianMatrixB bV (GraphHamiltonian.blockB L g s (Ψ (w₀, s)))
        let Cₛ := hamiltonianMatrixC bV (GraphHamiltonian.blockC L g s (Ψ (w₀, s)))
        ((s, (Ψ (w₀, s)).1), (Ψ (w₀, s)).2) ∈ g.target ∧
        J s = vectorFamilyMatrix bV (fun j ↦
          fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, s)).2) w₀ (bW j)) ∧
        HasDerivAt J (Bₛ * J s + Cₛ * P s) s ∧
        HasDerivAt P (-Aₛ * J s - Bₛᵀ * P s) s ∧ Aₛᵀ = Aₛ ∧ Cₛᵀ = Cₛ ∧ Cₛ.PosDef ∧
        (J s)ᵀ * P s = (P s)ᵀ * J s ∧
        (∀ v : ι → ℝ, J s *ᵥ v = 0 → P s *ᵥ v = 0 → v = 0) ∧
        Cₛ = hamiltonianMatrixC bV (ContinuousLinearMap.inverse
          (GraphLegendre.verticalHessian L (g.symm ((s, (Ψ (w₀, s)).1),
            (Ψ (w₀, s)).2)))) := by
  obtain ⟨e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget,
    hΨ, hJacobi, hphase⟩ := hchart
  let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
  let Ψ := F.adaptedGraphPhase old A γ e
  have hODE (q : W × ℝ) (hq : q ∈ D) : HasDerivAt (fun s ↦ Ψ (q.1, s))
      (GraphHamiltonian.field (F.adaptedGraphLagrangian old A) g q.2 (Ψ q)) q.2 :=
    (hJacobi q hq).2.1
  refine ⟨e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget, hΨ, ?_⟩
  intro s hs
  have hp : ((s, (Ψ (w₀, s)).1), (Ψ (w₀, s)).2) ∈ g.target := by
    have h := g.map_source (hJacobi (w₀, s) hs).1
    rw [hg] at h
    exact h
  have hmat := hF.adaptedGraph_parameter_matrices old A bW bV hg hsub hG hD hΨ hODE
    hs hp (hphase (w₀, s) hs rfl).1 (hphase (w₀, s) hs rfl).2
  have hd : DifferentiableAt ℝ (fun w ↦ Ψ (w, s)) w₀ := by
    apply DifferentiableAt.comp w₀ (g := Ψ)
    · exact (hΨ.contDiffAt (hD.mem_nhds hs)).differentiableAt (by norm_num)
    · exact differentiableAt_id.prodMk (differentiableAt_const s)
  exact ⟨hp, (F.adaptedGraphPhase_position_matrix_eq old A bW bV γ e hd).symm, hmat⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
