import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerGraphVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerGraphVariation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Variation.Graph

* **Conditions:** The actual graph inverse of a differentiable curve family, nonzero longitudinal velocity and a legal original Finsler phase.
* **Objects:** Equality of original length-Hessian quadratic pairings on old and regraphed parameter variations.
* **Proof detail:** Compute the inverse-time correction to each variation; their difference is radial velocity, which the actual length Hessian annihilates.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): This keeps the old velocity in the Hessian. Velocity rescaling and two-endpoint distance Hessians are separate.
-/

/-!
# Original Finsler length quadratic forms under actual regraphing

Use the actual inverse graph coordinates of the same curve family. Its parameter
variation differs from the old variation by a computed multiple of the old velocity.
The original fiber length Hessian kills that velocity, so its quadratic form is
unchanged. The state, velocity and variations all come from the original family.
This does not identify the point-to-point distance Hessian or rescale the Hessian
from old velocity to normalized graph velocity.
-/

open Set Manifold
open scoped ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- Regraphing the same actual curve family preserves the original fiber length
Hessian on every pair of parameter variations. -/
theorem chartLength_hessian_regraphed (x₀ : M) {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0)
    (hz : (γ (e.symm q), fderiv ℝ γ (e.symm q) (0, 1)) ∈ chartEnergyDomain x₀)
    (u w : W) :
    let H := fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (γ (e.symm q), v) : ℝ)))
      (fderiv ℝ γ (e.symm q) (0, 1))
    H (fderiv ℝ (curveGraphPosition γ e) q (u, 0))
      (fderiv ℝ (curveGraphPosition γ e) q (w, 0)) =
      H (fderiv ℝ γ (e.symm q) (u, 0)) (fderiv ℝ γ (e.symm q) (w, 0)) := by
  let z : (ℝ × V) × (ℝ × V) :=
    (γ (e.symm q), fderiv ℝ γ (e.symm q) (0, 1))
  let H := fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2
  have hs : ∀ a b, H a b = H b a :=
    fun a b ↦ hF.chartLength_hessian_symm x₀ (z := z) hz a b
  have hr : H z.2 = 0 := hF.chartLength_hessian_radial x₀ (z := z) hz
  exact curveGraphPosition_bilinear_invariant he hq hγ hi hv H hs hr u w

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
