import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Jacobi.LabelHessian
import OTSelector.Geometry.Finsler.LengthHessian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerIntrinsicLabelHessian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerIntrinsicLabelHessian`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.IntrinsicLabelHessian

* **Conditions:** A differentiable actual manifold family with nonzero time velocity at the point, and a fixed transverse label basis.
* **Objects:** One intrinsic label length-Hessian matrix equal to every legal chart formula.
* **Proof detail:** Pull back the fiber length through the actual chart differential and apply the bilinear second-derivative chain rule to both actual label and time derivatives.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition prop:rough-ray-quadratic, lines 1188–1205; equation eq:rough-ray-quadratic, integral inverse-Hessian coefficient.

Source relation (derived): The matrix is defined intrinsically from original Finsler length. Chart independence is derived, and the manuscript label-Hessian construction is preserved separately.
-/

/-!
# Intrinsic length Hessians in the fixed label space

The original family defines a label Hessian directly in the actual tangent fiber.
Every legal manifold chart gives the same matrix: its length function is the pullback
through the actual chart differential, and both label and time derivatives use that
same differential. This supplies one kernel for different local graph clocks.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual fiber length Hessian evaluated on the family's label variations.
The reference fiber model is used for differentiation only; no manifold chart is chosen. -/
def familyLabelHessianMatrix (F : ContinuousFinslerNorm E M)
    (bW : Basis ι ℝ W) (Γ : W × ℝ → M) (q : W × ℝ) : Matrix ι ι ℝ :=
  let D := (tangentFiberModelEquiv (Γ q)).symm.toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
  let H := fderiv ℝ (fderiv ℝ (fun v : E ↦
    (F.toFun ⟨Γ q, tangentFiberModelEquiv (Γ q) v⟩ : ℝ))) (D (0, 1))
  fun i j ↦ H (D (bW j, 0)) (D (bW i, 0))

namespace IsSmoothStronglyConvex

/-- The actual fiber length Hessian is invariant under the genuine tangent chart change. -/
theorem chartLength_hessian_mfderiv_extChartAt
    (hF : F.IsSmoothStronglyConvex) (old : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {v : E} (hv : v ≠ 0) (u w : E) :
    let T := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x).comp
      (tangentFiberModelEquiv x).toContinuousLinearMap
    fderiv ℝ (fderiv ℝ (fun z ↦
      (F.chartLength old (extChartAt 𝓘(ℝ, E) old x, z) : ℝ))) (T v) (T u) (T w) =
      fderiv ℝ (fderiv ℝ (fun z : E ↦
        (F.toFun ⟨x, tangentFiberModelEquiv x z⟩ : ℝ))) v u w := by
  obtain ⟨B, hB⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) hx
  let A : E ≃L[ℝ] E := (tangentFiberModelEquiv x).trans B
  let L := fun z : E ↦ (F.chartLength old (extChartAt 𝓘(ℝ, E) old x, z) : ℝ)
  have hA : A.toContinuousLinearMap =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x).comp
        (tangentFiberModelEquiv x).toContinuousLinearMap := by
    change B.toContinuousLinearMap.comp (tangentFiberModelEquiv x).toContinuousLinearMap = _
    rw [hB]
  have heq : (fun z : E ↦ (F.toFun ⟨x, tangentFiberModelEquiv x z⟩ : ℝ)) = L ∘ A := by
    funext z
    change (F.toFun ⟨x, tangentFiberModelEquiv x z⟩ : ℝ) =
      F.chartLength old (extChartAt 𝓘(ℝ, E) old x, A.toContinuousLinearMap z)
    rw [hA]
    exact (congrArg NNReal.toReal (F.chartLength_mfderiv_extChartAt old hx
      (tangentFiberModelEquiv x z))).symm
  have hAv : A v ≠ 0 := A.map_eq_zero_iff.not.mpr hv
  have hz : (extChartAt 𝓘(ℝ, E) old x, A v) ∈ chartEnergyDomain old :=
    ⟨(extChartAt 𝓘(ℝ, E) old).map_source hx, hAv⟩
  have h2 : DifferentiableAt ℝ (fderiv ℝ L) (A v) :=
    ((hF.contDiffAt_chartFiberLength old hz).fderiv_right (m := 1) (by simp)).differentiableAt_one
  have hh := fderiv2_comp_linearEquiv A h2 u w
  rw [← heq] at hh
  dsimp only
  simpa only [L, ← hA, ContinuousLinearEquiv.coe_coe] using! hh.symm

/-- Every legal chart computes the same intrinsic label Hessian of the original family. -/
theorem chartFamilyLabelHessianMatrix_eq_intrinsic
    (hF : F.IsSmoothStronglyConvex) (old : M) (bW : Basis ι ℝ W)
    {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hv : mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q (0, 1) ≠ 0) :
    F.chartFamilyLabelHessianMatrix old bW (extChartAt 𝓘(ℝ, E) old ∘ Γ) q =
      F.familyLabelHessianMatrix bW Γ q := by
  have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hd : fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ Γ) q =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q)).comp
        (mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp q hc hΓ]
  let D := (tangentFiberModelEquiv (Γ q)).symm.toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
  have hDv : D (0, 1) ≠ 0 :=
    (tangentFiberModelEquiv (Γ q)).symm.map_eq_zero_iff.not.mpr hv
  ext i j
  have h := hF.chartLength_hessian_mfderiv_extChartAt old hx hDv
    (D (bW j, 0)) (D (bW i, 0))
  simpa only [chartFamilyLabelHessianMatrix, familyLabelHessianMatrix, hd,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, D,
    ContinuousLinearEquiv.apply_symm_apply, Function.comp_apply] using! h

/-- Distinct legal manifold charts give exactly the same original label matrix. -/
theorem chartFamilyLabelHessianMatrix_eq_chart
    (hF : F.IsSmoothStronglyConvex) (old₁ old₂ : M) (bW : Basis ι ℝ W)
    {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (h₁ : Γ q ∈ (extChartAt 𝓘(ℝ, E) old₁).source)
    (h₂ : Γ q ∈ (extChartAt 𝓘(ℝ, E) old₂).source)
    (hv : mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q (0, 1) ≠ 0) :
    F.chartFamilyLabelHessianMatrix old₁ bW (extChartAt 𝓘(ℝ, E) old₁ ∘ Γ) q =
      F.chartFamilyLabelHessianMatrix old₂ bW (extChartAt 𝓘(ℝ, E) old₂ ∘ Γ) q :=
  (hF.chartFamilyLabelHessianMatrix_eq_intrinsic old₁ bW hΓ h₁ hv).trans
    (hF.chartFamilyLabelHessianMatrix_eq_intrinsic old₂ bW hΓ h₂ hv).symm

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
