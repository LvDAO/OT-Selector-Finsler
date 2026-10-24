import OTSelector.Analysis.Convex.FiniteSoftMinimum
import OTSelector.Analysis.Convex.FiniteSoftMinimumBounds
import OTSelector.Analysis.Convex.QuadraticSoftDualEndpoints
import OTSelector.Analysis.Convex.QuadraticSoftHamiltonJacobi
import OTSelector.Analysis.Convex.TimeDependentSoftTests
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiFiniteDual.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiFiniteDual`; the selected original proof blocks follow. -/
section

/-!
Conditions: Positive soft-minimum parameter, nonnegative time shift and finite nonnegative endpoint weights, with actual quadratic dual feasibility and bounded node costs.

Objects: A finite weighted dual bound by true quadratic soft tests at the two shifted endpoint times.

Proof detail: Apply soft-minimum upper/lower bounds at actual nodes, use the finite dual inequalities and retain the entropy and time-shift errors explicitly.

Sources: Stephen Boyd, Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86); Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31); Gabriel Peyré, Section 7.1, equations (7.1)–(7.5), pp. 112–113 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=116).
Relation: Locally derived finite quadratic endpoint estimate; positivity is used exactly as stated for this soft-minimum comparison.
-/

/-! Weighted finite dual endpoints for the actual finite quadratic soft test.
The two original weight families need not have equal total mass. -/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

variable {H I J : Type*} [NormedAddCommGroup H] [Fintype I] [Nonempty I] [Fintype J]

/-- Actual finite quadratic dual prices are bounded by their original weighted
soft-test endpoint readout, paying the explicit error only on the target mass. -/
theorem quadraticSoftMinimum_weighted_dual_endpoints
    {ε δ M : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (α : I → ℝ) (β : J → ℝ) (hα : ∀ i,0 ≤ α i) (hβ : ∀ j,0 ≤ β j)
    (u : I → ℝ) (v : J → ℝ) (x : I → H) (y : J → H)
    (hdual : ∀ i j,u i+v j ≤ ‖y j-x i‖^2/2)
    (hcost : ∀ i j,‖y j-x i‖^2/2 ≤ M) :
    let ψ := fun τ z ↦ finiteSoftMinimum ε
      (fun i ↦ quadraticHamiltonJacobiBranch (-u i) (x i) τ z)
    (∑ i,α i*u i)+(∑ j,β j*v j) ≤
      (∑ j,β j*ψ (1+δ) (y j))-(∑ i,α i*ψ δ (x i))+
        (∑ j,β j)*(M*δ+ε*Real.log (Fintype.card I)) := by
  dsimp only
  let ψ := fun τ z ↦ finiteSoftMinimum ε
    (fun i ↦ quadraticHamiltonJacobiBranch (-u i) (x i) τ z)
  let err := M*δ+ε*Real.log (Fintype.card I)
  have hsource : (∑ i,α i*u i) ≤ ∑ i,α i*(-ψ δ (x i)) := by
    apply Finset.sum_le_sum
    intro i _
    have hi := quadraticSoftMinimum_sourceNode_le (δ := δ) hε u x i
    apply mul_le_mul_of_nonneg_left _ (hα i)
    change u i ≤ -ψ δ (x i)
    linarith only [hi]
  have htarget : (∑ j,β j*v j) ≤ ∑ j,β j*(ψ (1+δ) (y j)+err) := by
    apply Finset.sum_le_sum
    intro j _
    have hj := finiteSoftMinimum_lower hε
      (fun i ↦ quadraticHamiltonJacobiBranch (-u i) (x i) (1+δ) (y j))
      (fun i ↦ quadraticHamiltonJacobiBranch_target_le_error hδ (x i) (y j) (hdual i j) (hcost i j))
    apply mul_le_mul_of_nonneg_left _ (hβ j)
    change v j ≤ ψ (1+δ) (y j)+err
    dsimp only [ψ,err]
    linarith only [hj]
  simp only [mul_neg,Finset.sum_neg_distrib] at hsource
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul] at htarget
  dsimp only [ψ,err] at hsource htarget ⊢
  linarith only [hsource,htarget]

/-- The same finite weighted dual is read by the actual physical soft tests at
interpolation times zero and one, with the original positive branch-time shift. -/
theorem neumannQuadraticSoftTest_weighted_dual_endpoints
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε δ M : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (α : I → ℝ) (β : J → ℝ) (hα : ∀ i,0 ≤ α i) (hβ : ∀ j,0 ≤ β j)
    (u : I → ℝ) (v : J → ℝ) (x : I → (ι → ℝ)) (y : J → (ι → ℝ))
    (hdual : ∀ i j,u i+v j ≤
      ‖(EuclideanSpace.equiv ι ℝ).symm (y j)-(EuclideanSpace.equiv ι ℝ).symm (x i)‖^2/2)
    (hcost : ∀ i j,
      ‖(EuclideanSpace.equiv ι ℝ).symm (y j)-(EuclideanSpace.equiv ι ℝ).symm (x i)‖^2/2 ≤ M) :
    let nodes := fun i ↦ (EuclideanSpace.equiv ι ℝ).symm (x i)
    (∑ i,α i*u i)+(∑ j,β j*v j) ≤
      (∑ j,β j*neumannQuadraticSoftTest ε (fun i ↦ -u i) nodes δ 1 (y j))-
      (∑ i,α i*neumannQuadraticSoftTest ε (fun i ↦ -u i) nodes δ 0 (x i))+
        (∑ j,β j)*(M*δ+ε*Real.log (Fintype.card I)) := by
  simpa only [neumannQuadraticSoftTest,zero_add] using
    quadraticSoftMinimum_weighted_dual_endpoints hε hδ α β hα hβ u v
      (fun i ↦ (EuclideanSpace.equiv ι ℝ).symm (x i))
      (fun j ↦ (EuclideanSpace.equiv ι ℝ).symm (y j)) hdual hcost

end OTSelector.Reconstruction

end
end
