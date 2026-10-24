import OTSelector.Geometry.Finsler.AdaptedGraphJacobi
import OTSelector.Geometry.GraphHamiltonianFocal

/-!
# Actual focal expansions for original Finsler length in adapted coordinates

A linear splitting of an arbitrary model pulls back the original length. The actual
positive graph Hessian then supplies square Jacobi matrices, regular crossing and an
exact inverse pole for a jointly C2 solution family. Its true parameter differential is
smooth in time by the same original field equation. No replacement Finsler structure,
variation smoothness, crossing or position invertibility is assumed.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W V ι M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ V] in
/-- The actual adapted graph phase and its whole parameter differential are smooth in
central time, as consequences of their jointly C2 original-length solution equation. -/
theorem adaptedGraph_family_contDiffOn_slice [FiniteDimensional ℝ W]
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hsub : g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.adaptedGraphLagrangian old A) g z.2 (Ψ z)) z.2)
    (w₀ : W)
    (hp : ∀ t, (w₀, t) ∈ D → ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target) :
    ContDiffOn ℝ ∞ (fun t ↦ Ψ (w₀, t)) {t | (w₀, t) ∈ D} ∧
      ContDiffOn ℝ ∞ (fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀)
        {t | (w₀, t) ∈ D} :=
  contDiffOn_graphHamiltonianFamily_slice
    ((hF.contDiffOn_adaptedGraphLagrangian old A).mono hsub) hG hD hΨ hODE w₀ hp

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Matching bases read the actual adapted-family differential into square Jacobi
matrices. Their true inverse block is positive, their Wronskian vanishes, and their
joint phase kernel is zero without any position-block invertibility premise. -/
theorem adaptedGraph_parameter_matrices (hF : F.IsSmoothStronglyConvex)
    (old : M) (T : E ≃L[ℝ] (ℝ × V)) (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old T))
    (hsub : g.source ⊆ (T.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.adaptedGraphLagrangian old T) g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target)
    (hinj : Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    let L := F.adaptedGraphLagrangian old T
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    let P := fun s ↦ covectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).2)
    let A := hamiltonianMatrixA bV (GraphHamiltonian.blockA L g t (Ψ (w₀, t)))
    let B := hamiltonianMatrixB bV (GraphHamiltonian.blockB L g t (Ψ (w₀, t)))
    let C := hamiltonianMatrixC bV (GraphHamiltonian.blockC L g t (Ψ (w₀, t)))
    HasDerivAt J (B * J t + C * P t) t ∧
      HasDerivAt P (-A * J t - Bᵀ * P t) t ∧ Aᵀ = A ∧ Cᵀ = C ∧ C.PosDef ∧
      (J t)ᵀ * P t = (P t)ᵀ * J t ∧
      (∀ u : ι → ℝ, J t *ᵥ u = 0 → P t *ᵥ u = 0 → u = 0) ∧
      C = hamiltonianMatrixC bV (ContinuousLinearMap.inverse
        (GraphLegendre.verticalHessian L (g.symm ((t, (Ψ (w₀, t)).1),
          (Ψ (w₀, t)).2)))) := by
  apply graphHamiltonian_parameter_matrices bW bV hg
    ((hF.contDiffOn_adaptedGraphLagrangian old T).mono hsub) hG _ hD hΨ hODE hz hp hinj hpair
  intro z hz' w hw
  exact hF.adaptedGraphLagrangian_hessian_pos old T (hsub hz').1 z.2 hw

/-- Original adapted graph data give exact focal poles and rates for the same actual
phase and matching bases. Matrix smoothness and regular crossing are derived internally. -/
theorem adaptedGraph_hasFocalExpansion (hF : F.IsSmoothStronglyConvex)
    (old : M) (T : E ≃L[ℝ] (ℝ × V)) (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old T))
    (hsub : g.source ⊆ (T.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.adaptedGraphLagrangian old T) g z.2 (Ψ z)) z.2)
    (w₀ : W)
    (hp : ∀ t, (w₀, t) ∈ D → ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target)
    (hinj : ∀ t, (w₀, t) ∈ D →
      Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ t, (w₀, t) ∈ D → ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    HasGraphFocalExpansion bW bV Ψ D w₀ := by
  apply hasGraphFocalExpansion_of_graphHamiltonian bW bV hg
    ((hF.contDiffOn_adaptedGraphLagrangian old T).mono hsub) hG _ hD hΨ hODE hp hinj hpair
  intro z hz w hw
  exact hF.adaptedGraphLagrangian_hessian_pos old T (hsub hz).1 z.2 hw

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
