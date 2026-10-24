import OTSelector.Geometry.Finsler.AdaptedGraphMomentum
import OTSelector.Geometry.Manifold.CurveGraphJacobian

/-!
# Actual label length Hessians in the graph clock

Regraphing removes a multiple of the original velocity from each label variation.
The original length Hessian kills that direction. Its degree minus one homogeneity
then retains the precise positive clock speed in the graph Hessian pullback.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The same graph label Hessian is the original label length Hessian multiplied
by the actual longitudinal speed, with no affine-clock assumption. -/
theorem adaptedGraphLength_label_hessian
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1)
    (hx : A.symm (γ (e.symm q)) ∈ (extChartAt 𝓘(ℝ, E) old).target)
    (ξ η : W) :
    let y := curveGraphPosition γ e
    let J := fderiv ℝ (fun w ↦ (y (w, q.2)).2) q.1
    let v := fderiv ℝ γ (e.symm q) (0, 1)
    let H := fderiv ℝ (fderiv ℝ (fun u ↦
      (F.chartLength old (A.symm (γ (e.symm q)), u) : ℝ))) (A.symm v)
    GraphLegendre.verticalHessian (F.adaptedGraphLagrangian old A)
      (y q, deriv (fun s ↦ (y (q.1, s)).2) q.2) (J ξ) (J η) =
      v.1 * H (A.symm (fderiv ℝ γ (e.symm q) (ξ, 0)))
        (A.symm (fderiv ℝ γ (e.symm q) (η, 0))) := by
  let y := curveGraphPosition γ e
  let v := fderiv ℝ γ (e.symm q) (0, 1)
  let H := fderiv ℝ (fderiv ℝ (fun u ↦
    (F.chartLength old (A.symm (γ (e.symm q)), u) : ℝ))) (A.symm v)
  have hz : (A.symm (γ (e.symm q)), A.symm v) ∈ chartEnergyDomain old := by
    refine ⟨hx, ?_⟩
    intro hz
    have hvzero : v = 0 := A.symm.injective (by simpa using hz)
    exact hv.ne' (congrArg Prod.fst hvzero)
  have hy : DifferentiableAt ℝ y q := hγ.comp q hi
  have hfst : (ContinuousLinearMap.fst ℝ ℝ V).comp (fderiv ℝ y q) =
      ContinuousLinearMap.snd ℝ W ℝ := by
    apply hy.hasFDerivAt.fst.unique
    apply hasFDerivAt_snd.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hq] with r hr
    exact (curveGraph_inverse_components he hr).2
  have hlabel (w : W) : fderiv ℝ y q (w, 0) =
      (0, fderiv ℝ (fun z ↦ (y (z, q.2)).2) q.1 w) := by
    have hs : HasFDerivAt (fun z : W ↦ (z, q.2))
        (ContinuousLinearMap.inl ℝ W ℝ) q.1 :=
      (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
    have hd := hy.hasFDerivAt.snd.comp q.1 hs
    change HasFDerivAt (fun z ↦ (y (z, q.2)).2) _ q.1 at hd
    apply Prod.ext
    · exact congrArg (fun L : (W × ℝ) →L[ℝ] ℝ ↦ L (w, 0)) hfst
    · change (fderiv ℝ y q (w, 0)).2 =
        fderiv ℝ (fun z ↦ (y (z, q.2)).2) q.1 w
      rw [hd.fderiv]
      rfl
  have htime := curveGraphPosition_slice_hasDerivAt he hq hγ hi hv.ne'
  have hvelocity : A.symm (1, deriv (fun s ↦ (y (q.1, s)).2) q.2) =
      v.1⁻¹ • A.symm v := by
    have ht : (1, deriv (fun s ↦ (y (q.1, s)).2) q.2) = v.1⁻¹ • v := by
      apply Prod.ext
      · simp [hv.ne', v]
      · exact ((ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt.comp_hasDerivAt
          q.2 htime).deriv
    rw [ht, _root_.map_smul]
  let H' := H.bilinearComp A.symm.toContinuousLinearMap A.symm.toContinuousLinearMap
  have hsym : ∀ u w, H' u w = H' w u := fun u w ↦
    hF.chartLength_hessian_symm old hz (A.symm u) (A.symm w)
  have hrad : H' v = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    change H (A.symm v) (A.symm w) = 0
    rw [show H (A.symm v) = 0 from hF.chartLength_hessian_radial old hz]
    rfl
  have hsame := curveGraphPosition_bilinear_invariant he hq hγ hi hv.ne'
    H' hsym hrad ξ η
  rw [hlabel ξ, hlabel η] at hsame
  have hscale : fderiv ℝ (fderiv ℝ (fun u ↦
      (F.chartLength old (A.symm (curveGraphPosition γ e q), u) : ℝ)))
      (v.1⁻¹ • A.symm v) = v.1 • H := by
    simpa only [inv_inv, H, curveGraphPosition] using! hF.chartLength_fiberHessian_pos_smul old
      (z := (A.symm (curveGraphPosition γ e q), A.symm v)) hz
      (a := v.1⁻¹) (inv_pos.mpr hv)
  dsimp only [GraphLegendre.verticalHessian]
  rw [hF.adaptedGraphLagrangian_hessian_eq old A (x := curveGraphPosition γ e q) hx,
    hvelocity, hscale]
  change v.1 * H' (0, _) (0, _) = v.1 * H' _ _
  exact congrArg (fun r : ℝ ↦ v.1 * r) hsame

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
