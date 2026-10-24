import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerGraphLabelInverse.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerGraphLabelInverse`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Jacobi.LabelHessian

* **Conditions:** An actual Finsler chart family and a transverse basis, with no regularity hypothesis needed to define its totalized derivative expression.
* **Objects:** The matrix obtained by evaluating the true fiber length Hessian on actual label derivatives at the actual time velocity.
* **Proof detail:** Define each matrix entry by the original Hessian and the two basis-generated family derivatives, retaining their exact index convention.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition prop:rough-ray-quadratic, lines 1188–1205; equation eq:rough-ray-quadratic, integral inverse-Hessian coefficient.

Source relation (adapter): Only the generic matrix definition is selected. Its inverse/graph identities and the remaining source-file results are outside this extraction.
-/

/-!
# The original label inverse Hessian in the actual graph Jacobi frame

The original-time label length Hessian is defined from the actual position derivative.
Its inverse equals the graph Jacobi compliance integrand multiplied by the actual clock
speed. A genuine Legendre source point identifies this Hessian with the same Hamiltonian
coefficient, so neither a coefficient equality nor a separate quadratic form is assumed.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W V M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι] {F : ContinuousFinslerNorm E M}

/-- The original fiber length Hessian evaluated on the actual label variations,
in one fixed label basis. Time remains the original parameter. -/
def chartFamilyLabelHessianMatrix (F : ContinuousFinslerNorm E M) (old : M)
    (bW : Basis ι ℝ W) (x : W × ℝ → E) (q : W × ℝ) : Matrix ι ι ℝ :=
  let H := fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (x q, v) : ℝ)))
    (fderiv ℝ x q (0, 1))
  fun i j ↦ H (fderiv ℝ x q (bW j, 0)) (fderiv ℝ x q (bW i, 0))


end OTSelector.Geometry.ContinuousFinslerNorm

end
end
