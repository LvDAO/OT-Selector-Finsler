import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthProjection
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerGraphLength.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerGraphLength`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Coordinates.GraphLength

* **Conditions:** A smooth strongly convex Finsler norm in a chart modeled on R×V; the base lies in the actual chart target.
* **Objects:** Smooth graph length at velocities (1,η), a positive graph velocity Hessian and a finite-dimensional Hessian–dual equivalence.
* **Proof detail:** Pull back the original length Hessian by w↦(0,w); these nonzero directions cannot be radial to (1,η), so strict positivity follows.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The graph integrand is a local coordinate restriction of actual length, before any geodesic reparameterization.
-/

/-!
# The original Finsler length in graph velocity coordinates

In any manifold chart modeled on `ℝ × V`, graph velocities have the form `(1, η)`.
Their original Finsler length is smooth, and its actual velocity Hessian is the
pullback of the original fiber length Hessian by `w ↦ (0, w)`. These directions
miss the radial line, so the graph Hessian is strictly positive. In finite dimensions
it gives a continuous linear equivalence with the dual, without a chosen inner product.

This is a local coordinate construction for general Finsler data. It does not yet
reparameterize geodesic variations as graphs or identify a distance Hessian.
-/

open Set Manifold Filter
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

private theorem fderiv2_comp_affine
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → ℝ} (A : G →L[ℝ] E) (b : E) {x : G}
    (hf : ContDiffAt ℝ 2 f (b + A x)) (u w : G) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f (b + A y))) x u w =
      fderiv ℝ (fderiv ℝ f) (b + A x) (A u) (A w) := by
  have hψ : HasFDerivAt (fun y ↦ b + A y) A x := A.hasFDerivAt.const_add b
  have he : fderiv ℝ (fun y ↦ f (b + A y)) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ f (b + A y)).comp A) := by
    filter_upwards [hψ.continuousAt.eventually (hf.eventually (by norm_num))] with y hy
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (A.hasFDerivAt.const_add b)).fderiv
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hsecond := ((hd.hasFDerivAt.comp x hψ).clm_comp
    (hasFDerivAt_const A x)).fderiv
  simp only [Function.comp_def] at hsecond
  rw [he.fderiv_eq, hsecond]
  simp

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- Original graph length is jointly smooth in chart position and graph velocity. -/
theorem contDiffOn_chartGraphLength (x₀ : M) :
    ContDiffOn ℝ ∞ (fun z : (ℝ × V) × V ↦ (F.chartLength x₀ (z.1, (1, z.2)) : ℝ))
      ((extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ) := by
  have hmap : MapsTo (fun z : (ℝ × V) × V ↦ (z.1, (1, z.2)))
      ((extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ) (chartEnergyDomain x₀) := by
    intro z hz
    exact ⟨hz.1, by simp⟩
  exact (hF.contDiffOn_chartLength x₀).comp
    (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)) hmap

/-- Original graph length is smooth for every graph velocity at an admissible chart base. -/
theorem contDiff_chartGraphLength (x₀ : M) {x : ℝ × V}
    (hx : x ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) :
    ContDiff ℝ ∞ (fun η : V ↦ (F.chartLength x₀ (x, (1, η)) : ℝ)) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  have hz : (x, (1, η)) ∈ chartEnergyDomain x₀ := ⟨hx, by simp⟩
  have h := hF.contDiffAt_chartFiberLength x₀ hz
  simpa only [Function.comp_def] using!
    h.comp η (contDiffAt_const.prodMk (contDiffAt_id (x := η)))

/-- The actual graph Hessian is the pullback of the actual fiber length Hessian. -/
theorem chartGraphLength_hessian_eq (x₀ : M) {x : ℝ × V}
    (hx : x ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) (η u w : V) :
    fderiv ℝ (fderiv ℝ (fun θ : V ↦ (F.chartLength x₀ (x, (1, θ)) : ℝ))) η u w =
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (x, v) : ℝ)))
        (1, η) (0, u) (0, w) := by
  have hz : (x, (1, η)) ∈ chartEnergyDomain x₀ := ⟨hx, by simp⟩
  let A : V →L[ℝ] (ℝ × V) := (0 : V →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ V)
  have hs : ContDiffAt ℝ 2 (fun v ↦ (F.chartLength x₀ (x, v) : ℝ))
      ((1, (0 : V)) + A η) := by
    simpa [A] using (hF.contDiffAt_chartFiberLength x₀ hz).of_le (by simp : 2 ≤ ∞)
  simpa [A] using fderiv2_comp_affine A (1, (0 : V)) hs u w

/-- The graph Hessian is symmetric, as an actual second derivative of original length. -/
theorem chartGraphLength_hessian_symm (x₀ : M) {x : ℝ × V}
    (hx : x ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) (η u w : V) :
    fderiv ℝ (fderiv ℝ (fun θ : V ↦ (F.chartLength x₀ (x, (1, θ)) : ℝ))) η u w =
      fderiv ℝ (fderiv ℝ (fun θ : V ↦ (F.chartLength x₀ (x, (1, θ)) : ℝ))) η w u :=
  (hF.contDiff_chartGraphLength x₀ hx).contDiffAt.isSymmSndFDerivAt (by simp) u w

/-- Every nonzero graph velocity direction has strictly positive original length Hessian. -/
theorem chartGraphLength_hessian_pos (x₀ : M) {x : ℝ × V}
    (hx : x ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) (η : V) {w : V} (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (fun θ : V ↦ (F.chartLength x₀ (x, (1, θ)) : ℝ)))
      η w w := by
  rw [hF.chartGraphLength_hessian_eq x₀ hx]
  have hz : (x, (1, η)) ∈ chartEnergyDomain x₀ := ⟨hx, by simp⟩
  apply (hF.chartLength_hessian_pos_iff_not_radial x₀ hz (0, w)).mpr
  intro he
  let a := fiberLegendre (F.chartEnergy x₀) (x, (1, η)) (0, w) /
    fiberLegendre (F.chartEnergy x₀) (x, (1, η)) (1, η)
  change (0, w) = a • (1, η) at he
  have ha : a = 0 := by simpa using (congrArg Prod.fst he).symm
  exact hw (by simpa [ha] using congrArg Prod.snd he)

/-- In finite dimensions the actual graph Hessian gives an equivalence with the dual. -/
theorem exists_chartGraphLengthHessian_equiv [FiniteDimensional ℝ V]
    (x₀ : M) {x : ℝ × V}
    (hx : x ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) (η : V) :
    ∃ e : V ≃L[ℝ] (V →L[ℝ] ℝ), ∀ u w : V,
      e u w = fderiv ℝ (fderiv ℝ
        (fun θ : V ↦ (F.chartLength x₀ (x, (1, θ)) : ℝ))) η u w := by
  exact ⟨positive_dualMap_equiv _ (fun w hw ↦ hF.chartGraphLength_hessian_pos x₀ hx η hw),
    fun _ _ ↦ rfl⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
