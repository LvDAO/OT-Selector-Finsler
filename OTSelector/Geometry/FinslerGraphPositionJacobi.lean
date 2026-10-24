import OTSelector.Geometry.FinslerAdaptedGraphFocal
import OTSelector.Geometry.Finsler.AdaptedGraphMomentum
import OTSelector.MeasureTheory.AreaFormula.ParameterizedJacobiDeterminant
import OTSelector.Geometry.Manifold.SameGraphInverse

/-!
# The actual graph-position matrix in the Hamiltonian Jacobi system

The first component of the actual adapted graph phase is the graph position itself.
Consequently its Jacobi matrix is exactly the matrix occurring in the original
parameter Jacobian. The identity retains graph time, longitudinal speed and the fixed
normalization determinant, and differentiability of the same inverse is derived.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W V ι M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual graph-position derivative is the first component of the same phase jet. -/
theorem adaptedGraphPhase_position_parameter_fderiv
    (F : ContinuousFinslerNorm E M) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    (γ : W × ℝ → ℝ × V) (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
    {w : W} {s : ℝ}
    (hP : DifferentiableAt ℝ (fun z ↦ F.adaptedGraphPhase old A γ e (z, s)) w)
    (ξ : W) :
    fderiv ℝ (fun z ↦ (curveGraphPosition γ e (z, s)).2) w ξ =
      (fderiv ℝ (fun z ↦ F.adaptedGraphPhase old A γ e (z, s)) w ξ).1 :=
  congrArg (fun D : W →L[ℝ] V ↦ D ξ) hP.hasFDerivAt.fst.fderiv

variable [Fintype ι]

omit [Fintype ι] in
/-- Reading the actual graph-position derivative in matching bases gives the exact
position matrix used by the Hamiltonian variation equations. -/
theorem adaptedGraphPhase_position_matrix_eq
    (F : ContinuousFinslerNorm E M) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (γ : W × ℝ → ℝ × V) (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
    {w : W} {s : ℝ}
    (hP : DifferentiableAt ℝ (fun z ↦ F.adaptedGraphPhase old A γ e (z, s)) w) :
    vectorFamilyMatrix bV (fun j ↦
      fderiv ℝ (fun z ↦ (curveGraphPosition γ e (z, s)).2) w (bW j)) =
    vectorFamilyMatrix bV (fun j ↦
      (fderiv ℝ (fun z ↦ F.adaptedGraphPhase old A γ e (z, s)) w (bW j)).1) := by
  congr 1
  funext j
  exact F.adaptedGraphPhase_position_parameter_fderiv old A γ e hP (bW j)

variable [FiniteDimensional ℝ W] [DecidableEq ι]

/-- The physical parameter Jacobian is the same Jacobi position determinant at the
actual graph time, with its speed and fixed normalization factors. The old-time inverse
derivative is constructed from regularity of the actual graph coordinate map. -/
theorem parameterizedJacobian_adaptedGraphPhase_data
    (F : ContinuousFinslerNorm E M) (old : M)
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) (ℓ : (ℝ × W) ≃L[ℝ] E)
    {γ : W × ℝ → E} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (A ∘ γ))
    {w : W} {t : ℝ} (hz : (w, t) ∈ e.source)
    (hγ : DifferentiableAt ℝ γ (w, t))
    (hv : (fderiv ℝ (A ∘ γ) (w, t) (0, 1)).1 ≠ 0)
    (hP : DifferentiableAt ℝ
      (fun z ↦ F.adaptedGraphPhase old A (A ∘ γ) e (z, (A (γ (w, t))).1)) w) :
    let s := (A (γ (w, t))).1
    let c := (fderiv ℝ (A ∘ γ) (w, t) (0, 1)).1
    let J := vectorFamilyMatrix bV (fun j ↦
      (fderiv ℝ (fun z ↦ F.adaptedGraphPhase old A (A ∘ γ) e (z, s)) w (bW j)).1)
    HasDerivAt (fun r ↦ (e.symm (w, r)).2) c⁻¹ s ∧
      parameterizedJacobian (fun p : ℝ × W ↦ γ (p.2, p.1)) ℓ (t, w) =
        |c| * |J.det| * |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
          (ℓ.trans A).symm.toLinearEquiv.toLinearMap).det| := by
  have heval : e (w, t) = (w, (A (γ (w, t))).1) := by rw [he]; rfl
  have hq : (w, (A (γ (w, t))).1) ∈ e.target := heval ▸ e.map_source hz
  have hback : e.symm (w, (A (γ (w, t))).1) = (w, t) := by
    rw [← heval]
    exact e.left_inv hz
  have hAγ : DifferentiableAt ℝ (A ∘ γ) (e.symm (w, (A (γ (w, t))).1)) := by
    rw [hback]
    exact A.differentiableAt.comp (w, t) hγ
  have hvelocity : (fderiv ℝ (A ∘ γ) (e.symm (w, (A (γ (w, t))).1)) (0, 1)).1 ≠ 0 := by
    rwa [hback]
  have hi := differentiableAt_curveGraphInverse_of_regular he hq hAγ hvelocity
  have h := parameterizedJacobian_adaptedGraphTime_data bW bV A ℓ he hz hγ hi hv
  dsimp only at h ⊢
  rw [F.adaptedGraphPhase_position_matrix_eq old A bW bV (A ∘ γ) e hP] at h
  exact h

end OTSelector.Geometry.ContinuousFinslerNorm
