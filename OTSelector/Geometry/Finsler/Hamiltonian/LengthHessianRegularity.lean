import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Measure.Hausdorff
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthHessian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerIntrinsicKernelRegularity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerIntrinsicKernelRegularity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Hamiltonian.LengthHessianRegularity

* **Conditions:** Smooth strong convexity and a nonzero actual chart phase.
* **Objects:** Smooth dependence of the true fiber length Hessian on the original base and velocity.
* **Proof detail:** Differentiate the original slit-smooth length twice in velocity using joint smoothness and the chain rule.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Only this generic smoothness lemma is selected; the original intrinsic kernel positivity/continuity results are not added to this core.
-/

/-!
# Regularity of the actual intrinsic label kernel

The smooth comparison's true length Hessian varies continuously in any legal
chart, and chart independence gives one matrix along the original time interval.
Actual momentum normality and positive physical Jacobian make this matrix positive
definite; its inverse is therefore a continuous positive definite kernel.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {E W ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]





namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The genuine second fiber derivative of length is jointly smooth on the slit domain. -/
theorem contDiffAt_chartLength_fiberHessian (hF : F.IsSmoothStronglyConvex)
    (old : M) {z : E × E} (hz : z ∈ chartEnergyDomain old) :
    ContDiffAt ℝ ∞ (fun q : E × E ↦
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (q.1, v) : ℝ))) q.2) z := by
  have hL : ContDiffAt ℝ ∞ (fun p : E × E ↦ (F.chartLength old p : ℝ)) z :=
    (hF.contDiffOn_chartLength old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)
  have hfirst : ContDiffAt ℝ ∞ (fun q : E × E ↦
      fderiv ℝ (fun v ↦ (F.chartLength old (q.1, v) : ℝ)) q.2) z := by
    apply ContDiffAt.fderiv (n := ∞) (m := ∞)
      (g := fun q : E × E ↦ q.2)
      (f := fun q v ↦ (F.chartLength old (q.1, v) : ℝ)) _ contDiffAt_snd (by simp)
    exact hL.comp (z, z.2) (f := fun p : (E × E) × E ↦ (p.1.1, p.2))
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  apply ContDiffAt.fderiv (n := ∞) (m := ∞)
    (g := fun q : E × E ↦ q.2)
    (f := fun q v ↦ fderiv ℝ (fun u ↦ (F.chartLength old (q.1, u) : ℝ)) v)
    _ contDiffAt_snd (by simp)
  exact hfirst.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)



end ContinuousFinslerNorm.IsSmoothStronglyConvex


end OTSelector.Geometry

end
end
