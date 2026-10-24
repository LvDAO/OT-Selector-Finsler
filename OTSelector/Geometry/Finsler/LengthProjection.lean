import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.LinearAlgebra.Dual.CovectorKernel
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthProjection.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthProjection`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.LengthProjection

* **Conditions:** Actual Finsler momentum has positive pairing with its nonzero velocity and the original norm is smooth strongly convex.
* **Objects:** The canonical radial projection to the momentum kernel and the complete positivity/null-line characterization of the actual length Hessian.
* **Proof detail:** Subtract radial components, use radial Hessian annihilation in each argument, and reduce the diagonal to the positive kernel restriction.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A coordinate-free algebraic consequence of the original length Hessian; no chosen orthogonal projection or nonfocusing premise is used.
-/

/-!
# Radial quotient of the original Finsler length Hessian

The actual momentum and velocity define a kernel projection with no chosen inner product.
The true fiber length Hessian is unchanged by projecting either argument: subtracting
radial components does not change it. Its diagonal is nonnegative, and it vanishes
exactly on the radial line. These facts supply positivity on graph velocity directions,
without a geometric nonfocusing or curvature assumption.
-/

open Set Manifold
open scoped ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The actual momentum pairs strictly positively with its nonzero velocity. -/
theorem chartMomentum_self_pos (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    0 < fiberLegendre (F.chartEnergy x₀) z z.2 := by
  rw [hF.chartLegendre_self_eq_chartLength_sq x₀ hz]
  exact sq_pos_of_pos (NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz))

/-- Projecting both arguments onto the actual momentum kernel leaves length Hessian unchanged. -/
theorem chartLength_hessian_projected (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (u w : E) :
    let p := fiberLegendre (F.chartEnergy x₀) z
    let π := covectorKernelProjection p z.2 (hF.chartMomentum_self_pos x₀ hz).ne'
    fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2
      (π u : E) (π w : E) =
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 u w := by
  dsimp only
  have hr := hF.chartLength_hessian_radial x₀ hz
  have hr' (y : E) :
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 y z.2 = 0 := by
    rw [hF.chartLength_hessian_symm x₀ hz y z.2, hr, zero_apply]
  rw [covectorKernelProjection_coe, covectorKernelProjection_coe]
  simp only [map_sub, _root_.map_smul, sub_apply, smul_apply, smul_eq_mul,
    hr, zero_apply, hr', mul_zero, sub_zero]

/-- The diagonal of the actual fiber length Hessian is nonnegative in every direction. -/
theorem chartLength_hessian_nonneg (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (w : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 w w := by
  let p := fiberLegendre (F.chartEnergy x₀) z
  let π := covectorKernelProjection p z.2 (hF.chartMomentum_self_pos x₀ hz).ne'
  rw [← hF.chartLength_hessian_projected x₀ hz w w]
  change 0 ≤ fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2
    (π w : E) (π w : E)
  by_cases hw : (π w : E) = 0
  · simp only [hw, _root_.map_zero, le_refl]
  · exact (hF.chartLength_hessian_pos_on_momentum_ker x₀ hz hw (π w).property).le

/-- Vanishing length-Hessian diagonal means that the vector is exactly its radial component. -/
theorem chartLength_hessian_eq_zero_iff_radial (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (w : E) :
    fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 w w = 0 ↔
      w = (fiberLegendre (F.chartEnergy x₀) z w /
        fiberLegendre (F.chartEnergy x₀) z z.2) • z.2 := by
  let p := fiberLegendre (F.chartEnergy x₀) z
  let π := covectorKernelProjection p z.2 (hF.chartMomentum_self_pos x₀ hz).ne'
  have he := hF.chartLength_hessian_projected x₀ hz w w
  have hp : (π w : E) = w - (p w / p z.2) • z.2 := covectorKernelProjection_coe _ _ _ _
  constructor
  · intro hw
    have hzπ : (π w : E) = 0 := by
      by_contra hn
      have hpos := hF.chartLength_hessian_pos_on_momentum_ker x₀ hz hn (π w).property
      have he' : fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2
          (π w : E) (π w : E) = 0 := he.trans hw
      linarith
    exact sub_eq_zero.mp (hp.symm.trans hzπ)
  · intro hw
    have hzπ : (π w : E) = 0 := hp.trans (sub_eq_zero.mpr hw)
    rw [← he]
    change fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2
      (π w : E) (π w : E) = 0
    simp only [hzπ, _root_.map_zero]

/-- The actual length Hessian is strictly positive precisely off the radial line. -/
theorem chartLength_hessian_pos_iff_not_radial (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (w : E) :
    0 < fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 w w ↔
      w ≠ (fiberLegendre (F.chartEnergy x₀) z w /
        fiberLegendre (F.chartEnergy x₀) z z.2) • z.2 := by
  rw [lt_iff_le_and_ne]
  simp only [hF.chartLength_hessian_nonneg x₀ hz w, true_and, ne_eq,
    eq_comm (a := (0 : ℝ)), hF.chartLength_hessian_eq_zero_iff_radial x₀ hz w]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
