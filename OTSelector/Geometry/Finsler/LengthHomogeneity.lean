import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Compact
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthHessian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthHomogeneity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthHomogeneity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.LengthHomogeneity

* **Conditions:** The actual chart length is smooth off zero and positively homogeneous; the scale is strictly positive.
* **Objects:** Degrees 1, 0, 1 and −1 for actual length, fiber differential, base differential and fiber Hessian respectively.
* **Proof detail:** Differentiate the original positive velocity-scaling identity in the base and fiber variables, using the chain rule on the slit domain.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Positive homogeneity of the actual length differentials

The true chart length has degree one in velocity. Its fiber differential has degree
zero, its base differential has degree one, and its fiber Hessian has degree minus one.
All derivatives are those of the original length on the slit chart domain; no separate
bilinear form or homogeneity of a prescribed derivative is assumed.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Real-valued original chart length scales linearly under positive velocity scaling. -/
theorem chartLength_pos_smul (F : ContinuousFinslerNorm E M) (x₀ : M) {x : E}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) x₀).target) {a : ℝ} (ha : 0 < a) (v : E) :
    (F.chartLength x₀ (x, a • v) : ℝ) = a * (F.chartLength x₀ (x, v) : ℝ) := by
  simp only [F.chartLength_smul x₀ hx, NNReal.coe_mul, coe_nnnorm,
    Real.norm_eq_abs, abs_of_pos ha]

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The true fiber differential of original length is invariant under positive scaling. -/
theorem chartLength_fiberLegendre_pos_smul (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) {a : ℝ} (ha : 0 < a) :
    fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ)) (z.1, a • z.2) =
      fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ)) z := by
  have hza : (z.1, a • z.2) ∈ chartEnergyDomain x₀ :=
    ⟨hz.1, smul_ne_zero ha.ne' hz.2⟩
  have hp := hF.chartLegendre_pos_smul x₀ hz.1 hz.2 ha
  rw [hF.chartLegendre_eq_length_smul_fderiv x₀ hza,
    hF.chartLegendre_eq_length_smul_fderiv x₀ hz,
    F.chartLength_pos_smul x₀ hz.1 ha] at hp
  have hs : 0 < (F.chartLength x₀ z : ℝ) := NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
  ext w
  have he := congrArg (fun p : E →L[ℝ] ℝ ↦ p w) hp
  simp only [_root_.smul_apply, smul_eq_mul] at he
  change _ = _
  change a * (F.chartLength x₀ z : ℝ) * _ =
    a * ((F.chartLength x₀ z : ℝ) * _) at he
  exact (mul_left_cancel₀ (mul_pos ha hs).ne') (by simpa only [fiberLegendre, mul_assoc] using he)

/-- The true base differential of original length has degree one in velocity. -/
theorem chartLength_baseDifferential_pos_smul (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) {a : ℝ} (ha : 0 < a) :
    baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ)) (z.1, a • z.2) =
      a • baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ)) z := by
  have hd := ((hF.contDiffOn_chartLength x₀).contDiffAt
    ((isOpen_chartEnergyDomain x₀).mem_nhds hz)).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (fun x : E ↦ (x, z.2)) z.1 :=
    differentiableAt_id.prodMk (differentiableAt_const z.2)
  have hb : DifferentiableAt ℝ (fun x ↦ (F.chartLength x₀ (x, z.2) : ℝ)) z.1 := by
    simpa only [Function.comp_def] using! hd.comp z.1 hi
  have heq : (fun x ↦ (F.chartLength x₀ (x, a • z.2) : ℝ)) =ᶠ[𝓝 z.1]
      (fun x ↦ a * (F.chartLength x₀ (x, z.2) : ℝ)) := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hz.1] with x hx
    exact F.chartLength_pos_smul x₀ hx ha z.2
  change fderiv ℝ (fun x ↦ (F.chartLength x₀ (x, a • z.2) : ℝ)) z.1 = _
  rw [heq.fderiv_eq]
  exact (hb.hasFDerivAt.const_mul a).fderiv

/-- The actual fiber Hessian of original length has degree minus one in velocity. -/
theorem chartLength_fiberHessian_pos_smul (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) {a : ℝ} (ha : 0 < a) :
    fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) (a • z.2) =
      a⁻¹ • fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 := by
  let g := fun v ↦ fderiv ℝ (fun w ↦ (F.chartLength x₀ (z.1, w) : ℝ)) v
  have hza : (z.1, a • z.2) ∈ chartEnergyDomain x₀ :=
    ⟨hz.1, smul_ne_zero ha.ne' hz.2⟩
  have hd (v : E) (hv : v ≠ 0) : DifferentiableAt ℝ g v :=
    ((hF.contDiffAt_chartFiberLength x₀ (z := (z.1, v)) ⟨hz.1, hv⟩).fderiv_right
      (m := 1) (by simp)).differentiableAt_one
  have heq : (fun v ↦ g (a • v)) =ᶠ[𝓝 z.2] g := by
    filter_upwards [eventually_ne_nhds hz.2] with v hv
    exact hF.chartLength_fiberLegendre_pos_smul x₀ (z := (z.1, v)) ⟨hz.1, hv⟩ ha
  have hl := (hd (a • z.2) hza.2).hasFDerivAt.comp z.2
    ((hasFDerivAt_id z.2).const_smul a)
  have he := hl.unique ((hd z.2 hz.2).hasFDerivAt.congr_of_eventuallyEq heq)
  ext u w
  have hh := congrArg (fun D : E →L[ℝ] (E →L[ℝ] ℝ) ↦ D u w) he
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, _root_.map_smul, smul_eq_mul] at hh ⊢
  change _ = a⁻¹ * _
  change a * _ = _ at hh
  rw [← hh]
  simp [ha.ne', g]

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
