import OTSelector.Analysis.Calculus.Variational.EulerLagrangeReparam
import OTSelector.Analysis.Calculus.Variational.GraphEulerLagrange
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.AdaptedClock
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthProjection
import OTSelector.Geometry.Finsler.LengthReparam

/-!
# Geometry.Finsler.AdaptedGraphLagrangian

* **Conditions:** A genuine linear splitting E≃R×V and the original smooth strongly convex Finsler chart data.
* **Objects:** The actual adapted graph-length Lagrangian, positive graph Hessian and local Legendre inverse, with its reparameterized Euler–Lagrange equation.
* **Proof detail:** Pull original length back by the inverse tangent lift, restrict velocities to (1,η), differentiate and exclude radial spatial directions.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedGraphLagrangian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedGraphLagrangian`; the selected original proof blocks follow. -/
section

/-!
# Original Finsler graph length in genuinely adapted coordinates

An arbitrary linear equivalence to a time-space product acts on the original chart
length by its actual inverse tangent lift. Restricting this length to graph velocities
constructs the graph Lagrangian without changing the Finsler norm or manifold atlas.
Its actual Hessian is positive because spatial graph directions cannot be radial.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

private theorem secondDerivative_affine
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E → ℝ} (A : V →L[ℝ] E) (b : E) {x : V}
    (hf : ContDiffAt ℝ 2 f (b + A x)) (u w : V) :
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

namespace ContinuousFinslerNorm

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Original chart length in linear product coordinates and actual graph velocity. -/
def adaptedGraphLagrangian (F : ContinuousFinslerNorm E M) (old : M)
    (A : E ≃L[ℝ] (ℝ × V)) (z : (ℝ × V) × V) : ℝ :=
  F.chartLength old (A.symm z.1, A.symm (1, z.2))

/-- This graph integrand is the actual inverse tangent pullback of original length. -/
theorem adaptedGraphLagrangian_eq_pullback (F : ContinuousFinslerNorm E M) (old : M)
    (A : E ≃L[ℝ] (ℝ × V)) (z : (ℝ × V) × V) :
    F.adaptedGraphLagrangian old A z =
      pullbackEnergy A.symm (fun q ↦ (F.chartLength old q : ℝ)) (z.1, (1, z.2)) := by
  simp only [pullbackEnergy, tangentLift_linearEquiv, adaptedGraphLagrangian]

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- Joint smoothness holds on the genuine transformed chart-base domain. -/
theorem contDiffOn_adaptedGraphLagrangian (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] (ℝ × V)) :
    ContDiffOn ℝ ∞ (F.adaptedGraphLagrangian old A)
      ((A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ) := by
  apply (hF.contDiffOn_chartLength old).comp
    ((A.symm.contDiff.comp contDiff_fst).contDiffOn.prodMk
      (A.symm.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn)
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro he
  have h := congrArg A he
  simp at h

/-- The true graph Hessian is the original length Hessian in inverse spatial directions. -/
theorem adaptedGraphLagrangian_hessian_eq (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] (ℝ × V)) {x : ℝ × V}
    (hx : A.symm x ∈ (extChartAt 𝓘(ℝ, E) old).target) (η u w : V) :
    fderiv ℝ (fderiv ℝ (fun θ ↦ F.adaptedGraphLagrangian old A (x, θ))) η u w =
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (A.symm x, v) : ℝ)))
        (A.symm (1, η)) (A.symm (0, u)) (A.symm (0, w)) := by
  have hz : (A.symm x, A.symm (1, η)) ∈ chartEnergyDomain old := by
    refine ⟨hx, ?_⟩
    intro he
    have h := congrArg A he
    simp at h
  let T : V →L[ℝ] E := A.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ V)
  have he (θ : V) : A.symm (1, (0 : V)) + A.symm (0, θ) = A.symm (1, θ) := by
    rw [← _root_.map_add]
    simp
  have hs : ContDiffAt ℝ 2 (fun v ↦ (F.chartLength old (A.symm x, v) : ℝ))
      (A.symm (1, (0 : V)) + T η) := by
    change ContDiffAt ℝ 2 _ (A.symm (1, (0 : V)) + A.symm (0, η))
    rw [he]
    exact (hF.contDiffAt_chartFiberLength old hz).of_le (by simp)
  simpa only [T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearEquiv.coe_coe, he,
    adaptedGraphLagrangian] using
    secondDerivative_affine T (A.symm (1, (0 : V))) hs u w

/-- Every nonzero graph direction has positive actual Hessian in these coordinates. -/
theorem adaptedGraphLagrangian_hessian_pos (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] (ℝ × V)) {x : ℝ × V}
    (hx : A.symm x ∈ (extChartAt 𝓘(ℝ, E) old).target) (η : V) {w : V} (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (fun θ ↦ F.adaptedGraphLagrangian old A (x, θ))) η w w := by
  rw [hF.adaptedGraphLagrangian_hessian_eq old A hx]
  have hz : (A.symm x, A.symm (1, η)) ∈ chartEnergyDomain old := by
    refine ⟨hx, ?_⟩
    intro he
    have h := congrArg A he
    simp at h
  apply (hF.chartLength_hessian_pos_iff_not_radial old hz (A.symm (0, w))).mpr
  intro he
  let a := fiberLegendre (F.chartEnergy old) (A.symm x, A.symm (1, η)) (A.symm (0, w)) /
    fiberLegendre (F.chartEnergy old) (A.symm x, A.symm (1, η)) (A.symm (1, η))
  have hr : ((0 : ℝ), w) = a • (1, η) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply, _root_.map_smul] using congrArg A he
  have ha : a = 0 := by simpa using (congrArg Prod.fst hr).symm
  exact hw (by simpa [ha] using congrArg Prod.snd hr)

/-- In finite dimension the actual graph Hessian is an equivalence with its dual. -/
theorem exists_adaptedGraphHessian_equiv [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V)) {x : ℝ × V}
    (hx : A.symm x ∈ (extChartAt 𝓘(ℝ, E) old).target) (η : V) :
    ∃ e : V ≃L[ℝ] (V →L[ℝ] ℝ), ∀ u w : V,
      e u w = fderiv ℝ
        (fderiv ℝ (fun θ ↦ F.adaptedGraphLagrangian old A (x, θ))) η u w :=
  ⟨positive_dualMap_equiv _ (fun _ hw ↦ hF.adaptedGraphLagrangian_hessian_pos old A hx η hw),
    fun _ _ ↦ rfl⟩

/-- Original smooth convexity constructs the true adapted graph Legendre inverse. -/
theorem exists_smooth_adaptedGraphLegendre_local_inverse [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {z : (ℝ × V) × V} (hz : A.symm z.1 ∈ (extChartAt 𝓘(ℝ, E) old).target) :
    ∃ e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)),
      (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
        parametricLegendre (F.adaptedGraphLagrangian old A) ∧
      z ∈ e.source ∧ parametricLegendre (F.adaptedGraphLagrangian old A) z ∈ e.target ∧
      e.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ ∧
      ContDiffOn ℝ ∞ (parametricLegendre (F.adaptedGraphLagrangian old A)) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.target, (e.symm p).1 = p.1) ∧
      ∀ p ∈ e.target, HasFDerivAt e.symm
        (ContinuousLinearMap.inverse
          (fderiv ℝ (parametricLegendre (F.adaptedGraphLagrangian old A)) (e.symm p))) p := by
  apply exists_smooth_parametricLegendre_local_inverse
    (((isOpen_extChartAt_target old).preimage A.symm.continuous).prod isOpen_univ)
    (hF.contDiffOn_adaptedGraphLagrangian old A)
  · intro y hy w hw
    exact hF.adaptedGraphLagrangian_hessian_pos old A hy.1 y.2 hw
  · exact ⟨hz, mem_univ _⟩

/-- A positive actual graph reparameterization of an original energy solution satisfies
Euler--Lagrange for this original-length graph integrand. No length or graph equation
is assumed; the coordinate and time changes are genuine functions. -/
theorem adaptedGraph_eulerLagrange_reparam (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ s ∈ I, (x s, deriv x s) ∈ chartEnergyDomain old)
    (hEL : ∀ s ∈ I, HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old) (x r, deriv x r))
      (baseEnergyDifferential (F.chartEnergy old) (x s, deriv x s)) s)
    {τ : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J) (hτ : ContDiffOn ℝ 2 τ J)
    (hτI : MapsTo τ J I) (hpos : ∀ s ∈ J, 0 < deriv τ s)
    (hclock : ∀ s ∈ J, (A (x (τ s))).1 = s) :
    let y := fun s ↦ (A (x (τ s))).2
    ∀ t ∈ J, HasDerivAt
      (fun s ↦ fiberLegendre (F.adaptedGraphLagrangian old A) ((s, y s), deriv y s))
      (GraphHamiltonian.positionDifferential (F.adaptedGraphLagrangian old A)
        ((t, y t), deriv y t)) t := by
  let y := fun s ↦ (A (x (τ s))).2
  let γ := fun s ↦ (s, y s)
  let L := fun z ↦ (F.chartLength old z : ℝ)
  have hy : ContDiffOn ℝ 2 y J := (A.contDiff.comp_contDiffOn (hx.comp hτ hτI)).snd
  have hγ : ContDiffOn ℝ 2 γ J := contDiffOn_id.prodMk hy
  have hyD (s : ℝ) (hs : s ∈ J) : DifferentiableAt ℝ y s :=
    (hy.contDiffAt (hJ.mem_nhds hs)).differentiableAt (by norm_num)
  have hdγ (s : ℝ) (hs : s ∈ J) : deriv γ s = (1, deriv y s) :=
    ((hasDerivAt_id s).prodMk (hyD s hs).hasDerivAt).deriv
  have hbase (s : ℝ) (hs : s ∈ J) : A.symm (γ s) = x (τ s) := by
    have he : γ s = A (x (τ s)) := Prod.ext (hclock s hs).symm rfl
    rw [he, ContinuousLinearEquiv.symm_apply_apply]
  have hp (s : ℝ) (hs : s ∈ J) :
      tangentLift A.symm (γ s, deriv γ s) ∈ chartEnergyDomain old := by
    rw [tangentLift_linearEquiv, hbase s hs, hdγ s hs]
    refine ⟨(hphase _ (hτI hs)).1, ?_⟩
    intro he
    have he' := congrArg A he
    simp at he'
  have hlength (s : ℝ) (hs : s ∈ J) : HasDerivAt
      (fun r ↦ fiberLegendre (pullbackEnergy A.symm L) (γ r, deriv γ r))
      (baseEnergyDifferential (pullbackEnergy A.symm L) (γ s, deriv γ s)) s := by
    apply hasDerivAt_eulerLagrange_pullback isOpen_univ (isOpen_chartEnergyDomain old)
      A.symm.contDiff.contDiffOn ((hF.contDiffOn_chartLength old).of_le (by simp))
      hJ hγ (mapsTo_univ _ _) hp hs
    have hr := hF.chartLength_eulerLagrange_reparam old hI hconn hx hphase hEL
      (τ := τ) (t := s) (by
        filter_upwards [hJ.mem_nhds hs] with r hr
        exact ⟨(hτ.contDiffAt (hJ.mem_nhds hr)).differentiableAt (by norm_num),
          hpos r hr, hτI hr⟩)
    apply hasDerivAt_eulerLagrange_congr _ hr
    filter_upwards [hJ.mem_nhds hs] with r hr
    exact (hbase r hr).symm
  have hT : ContDiff ℝ ∞ (tangentLift A.symm) := by
    rw [show tangentLift A.symm =
      (fun z : (ℝ × V) × (ℝ × V) ↦ (A.symm z.1, A.symm z.2)) from
      funext (tangentLift_linearEquiv A.symm)]
    exact (A.symm.contDiff.comp contDiff_fst).prodMk (A.symm.contDiff.comp contDiff_snd)
  have hL (s : ℝ) (hs : s ∈ J) :
      DifferentiableAt ℝ (pullbackEnergy A.symm L) ((s, y s), (1, deriv y s)) := by
    have hsp : tangentLift A.symm ((s, y s), (1, deriv y s)) ∈ chartEnergyDomain old := by
      simpa only [hdγ s hs] using hp s hs
    exact (((hF.contDiffOn_chartLength old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hsp)).differentiableAt (by simp)).comp _
        (hT.differentiable (by simp) _)
  have heq : F.adaptedGraphLagrangian old A =
      fun z : (ℝ × V) × V ↦ pullbackEnergy A.symm L (z.1, (1, z.2)) :=
    funext (F.adaptedGraphLagrangian_eq_pullback old A)
  dsimp only
  intro t ht
  rw [heq]
  exact eulerLagrange_graphRestriction hJ hyD hL hlength t ht

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry

end
end
