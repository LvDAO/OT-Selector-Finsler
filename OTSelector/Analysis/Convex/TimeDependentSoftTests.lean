import OTSelector.Analysis.Calculus.EuclideanGradientPullback
import OTSelector.Analysis.Convex.FiniteSoftMinimum
import OTSelector.Analysis.Convex.QuadraticSoftGradientBound
import OTSelector.Analysis.Convex.QuadraticSoftHamiltonJacobi
import OTSelector.Analysis.Convex.QuadraticSoftSmoothness
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiSoftTests.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiSoftTests`; the selected original proof blocks follow. -/
section

/-!
# Analysis.Convex.TimeDependentSoftTests

Conditions: Finite nonempty branch indices, finite-dimensional Euclidean coordinates and shifted times avoiding zero; the pointwise HJ identity assumes nonzero epsilon while other signatures retain their actual generality.
Objects: The finite quadratic log-sum-exp test, its actual time derivative and physical gradient, plus joint continuity and gradient bounds.
Proof detail: Pull the established quadratic soft-test formulas through the Euclidean coordinate equivalence and time translation; combine normalized exponential weights for the HJ inequality and smoothness.

## Mathematical sources

- Stephen Boyd; Lieven Vandenberghe, *Convex Optimization (2004)*: Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation. https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86
- Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*: Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives. https://www.jirka.org/ra/realanal2.pdf

Source relation: A quadratic/time-dependent chain-rule specialization of log-sum-exp. The theorem is pointwise and imposes no Neumann boundary condition. The nonzero signed-epsilon generality is stated by the Lean signature, beyond the usual positive soft-min parameter.
-/

/-! Actual time-shifted finite quadratic soft tests in the original physical
coordinates, with their own derivatives, gradients and Hamilton-Jacobi bound. -/
open Set InnerProductSpace
open scoped BigOperators Topology RealInnerProductSpace ContDiff
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Nonempty I]

/-- The original finite quadratic soft test pulled back to physical coordinates. -/
def neumannQuadraticSoftTest (ε : ℝ) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    (δ t : ℝ) (x : ι → ℝ) : ℝ :=
  finiteSoftMinimum ε (fun i ↦ quadraticHamiltonJacobiBranch (a i) (y i) (t+δ)
    ((EuclideanSpace.equiv ι ℝ).symm x))

/-- The actual time derivative, using the original normalized exponential weights. -/
def neumannQuadraticSoftTimeDerivative (ε : ℝ) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    (δ t : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i,finiteSoftMinimumWeight ε
    (fun j ↦ quadraticHamiltonJacobiBranch (a j) (y j) (t+δ) ((EuclideanSpace.equiv ι ℝ).symm x)) i *
      (-‖(EuclideanSpace.equiv ι ℝ).symm x-y i‖^2/(2*(t+δ)^2))

/-- The actual physical coordinate gradient, with the same branches and weights. -/
def neumannQuadraticSoftGradient (ε : ℝ) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    (δ t : ℝ) (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  ∑ i,finiteSoftMinimumWeight ε
    (fun j ↦ quadraticHamiltonJacobiBranch (a j) (y j) (t+δ) ((EuclideanSpace.equiv ι ℝ).symm x)) i •
      ((t+δ)⁻¹ • ((EuclideanSpace.equiv ι ℝ).symm x-y i))

/-- The same actual soft test has its genuine time derivative and physical
coordinate gradient and satisfies the original Hamilton-Jacobi inequality. -/
theorem neumannQuadraticSoftTest_pointwise
    (ε : ℝ) (hε : ε ≠ 0) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    (δ t : ℝ) (ht : t+δ ≠ 0) (x : ι → ℝ) :
    HasDerivAt (fun s ↦ neumannQuadraticSoftTest ε a y δ s x)
      (neumannQuadraticSoftTimeDerivative ε a y δ t x) t ∧
    physicalCoordinateGradient ι (fderiv ℝ (neumannQuadraticSoftTest ε a y δ t) x) =
      neumannQuadraticSoftGradient ε a y δ t x ∧
    neumannQuadraticSoftTimeDerivative ε a y δ t x+
      ‖neumannQuadraticSoftGradient ε a y δ t x‖^2/2 ≤ 0 := by
  have h := quadraticSoftMinimum_hamiltonJacobi ε hε a y (t+δ) ht
    ((EuclideanSpace.equiv ι ℝ).symm x)
  refine ⟨?_,?_,h.2.2⟩
  · simpa only [neumannQuadraticSoftTest,neumannQuadraticSoftTimeDerivative,Function.comp_def,id_eq,mul_one]
      using h.1.comp t ((hasDerivAt_id t).add_const δ)
  · exact physicalCoordinateGradient_pullback _ _ x h.2.1

omit [DecidableEq ι] in
/-- Each fixed nonzero shifted-time physical soft test is smooth everywhere. -/
theorem contDiff_neumannQuadraticSoftTest
    (ε : ℝ) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    (δ t : ℝ) (ht : t+δ ≠ 0) :
    ContDiff ℝ ∞ (neumannQuadraticSoftTest ε a y δ t) :=
  (contDiff_quadraticSoftMinimum (⊤ : ℕ∞) ε a y (t+δ) ht).comp
    (EuclideanSpace.equiv ι ℝ).symm.contDiff

omit [DecidableEq ι] in
/-- The true shifted-time gradient bound retains only the original node
distances, independently of the finite dual prices and smoothing parameter. -/
theorem neumannQuadraticSoftGradient_norm_le
    (ε : ℝ) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    {δ t D : ℝ} (ht : 0 < t+δ) (x : ι → ℝ)
    (hD : ∀ i,‖(EuclideanSpace.equiv ι ℝ).symm x-y i‖ ≤ D) :
    ‖neumannQuadraticSoftGradient ε a y δ t x‖ ≤ D/(t+δ) :=
  quadraticSoftMinimum_gradient_norm_le ε a y _ ht hD

omit [DecidableEq ι] in
/-- The actual physical soft test and its actual time derivative are jointly
continuous on every closed time window that avoids the shifted time zero. -/
theorem continuousOn_neumannQuadraticSoftTest_timeDerivative
    (ε : ℝ) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    (δ aT bT : ℝ) (hTime : ∀ t ∈ Icc aT bT,t+δ ≠ 0) :
    ContinuousOn (fun z : ℝ × (ι → ℝ) ↦ neumannQuadraticSoftTest ε a y δ z.1 z.2)
      (Icc aT bT ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × (ι → ℝ) ↦ neumannQuadraticSoftTimeDerivative ε a y δ z.1 z.2)
      (Icc aT bT ×ˢ univ) := by
  let e := (EuclideanSpace.equiv ι ℝ).symm
  have hshift (z : ℝ × (ι → ℝ)) :
      ContDiffAt ℝ ∞ (fun z : ℝ × (ι → ℝ) ↦ (z.1+δ,e z.2)) z :=
    (contDiffAt_fst.add contDiffAt_const).prodMk (e.contDiff.contDiffAt.comp z contDiffAt_snd)
  have hbranch (i : I) : ContinuousOn
      (fun z : ℝ × (ι → ℝ) ↦ quadraticHamiltonJacobiBranch (a i) (y i) (z.1+δ) (e z.2))
      (Icc aT bT ×ˢ univ) := by
    intro z hz
    exact ((contDiffAt_quadraticHamiltonJacobiBranch (⊤ : ℕ∞) (a i) (y i) (z.1+δ)
      (hTime z.1 hz.1) (e z.2)).comp z (hshift z)).continuousAt.continuousWithinAt
  have hexp (i : I) : ContinuousOn
      (fun z : ℝ × (ι → ℝ) ↦ Real.exp (-ε⁻¹*quadraticHamiltonJacobiBranch (a i) (y i) (z.1+δ) (e z.2)))
      (Icc aT bT ×ˢ univ) := (continuousOn_const.mul (hbranch i)).rexp
  have hsum : ContinuousOn
      (fun z : ℝ × (ι → ℝ) ↦ ∑ i,Real.exp (-ε⁻¹*quadraticHamiltonJacobiBranch (a i) (y i) (z.1+δ) (e z.2)))
      (Icc aT bT ×ˢ univ) := continuousOn_finsetSum _ (fun i _ ↦ hexp i)
  have hweight (i : I) : ContinuousOn
      (fun z : ℝ × (ι → ℝ) ↦ finiteSoftMinimumWeight ε
        (fun j ↦ quadraticHamiltonJacobiBranch (a j) (y j) (z.1+δ) (e z.2)) i)
      (Icc aT bT ×ˢ univ) :=
    (hexp i).div hsum (fun z _ ↦ (finiteSoftMinimum_sum_exp_pos ε _).ne')
  have htimeDeriv (i : I) : ContinuousOn
      (fun z : ℝ × (ι → ℝ) ↦ -‖e z.2-y i‖^2/(2*(z.1+δ)^2))
      (Icc aT bT ×ˢ univ) := by
    apply (((e.continuous.comp continuous_snd).continuousOn.sub continuousOn_const).norm.pow 2).neg.div
      (continuousOn_const.mul ((continuous_fst.continuousOn.add continuousOn_const).pow 2))
    intro z hz
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (hTime z.1 hz.1))
  constructor
  · intro z hz
    exact ((contDiffAt_quadraticSoftMinimum (⊤ : ℕ∞) ε a y (z.1+δ) (hTime z.1 hz.1) (e z.2)).comp
      z (hshift z)).continuousAt.continuousWithinAt
  · exact continuousOn_finsetSum _ (fun i _ ↦ (hweight i).mul (htimeDeriv i))

end OTSelector.Reconstruction

end
end
