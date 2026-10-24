import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPositionJacobianRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPositionJacobianRank`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PositionJacobianRank

* **Conditions:** A joint linear position derivative has an injective label restriction annihilated by a covector and a nonzero time pairing; actual Finsler momentum provides that pairing.
* **Objects:** Full joint position rank and strictly positive actual parameterized Jacobian.
* **Proof detail:** Apply the covector to a zero joint derivative to kill its time component, recover the label component by injectivity and use the determinant of the resulting isomorphism.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22): Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): An elementary transverse-plus-time rank argument; positive Finsler energy supplies the time pairing without extra geometric nonfocusing.
-/

/-!
# Position rank and the physical Jacobian

An injective label derivative and actual momentum normality make the joint
position derivative injective. Euler's identity supplies its nonzero time
component directly from the original positive Finsler energy.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A normal injective label derivative and a nonzero time component give joint rank. -/
theorem injective_joint_of_normal_label (T : (W × ℝ) →L[ℝ] E) (p : E →L[ℝ] ℝ)
    (hlabel : Function.Injective (fun ξ : W ↦ T (ξ, 0)))
    (hnormal : ∀ ξ : W, p (T (ξ, 0)) = 0) (htime : p (T (0, 1)) ≠ 0) :
    Function.Injective T := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨ξ, s⟩ hzero
  change T (ξ, s) = 0 at hzero
  have hsplit : T (ξ, s) = T (ξ, 0) + s • T (0, 1) := by
    rw [← map_smul, ← map_add]
    congr 1
    simp
  have hs : s = 0 := by
    have h := congrArg p hzero
    rw [hsplit, map_add, map_smul, hnormal, map_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right htime
  subst s
  have hξ : ξ = 0 := hlabel (hzero.trans (T.map_zero).symm)
  simp [hξ]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- Actual normality and injective position labels force positive physical Jacobian.
The time direction is supplied by the intrinsic Euler--Lagrange curve itself. -/
theorem parameterizedJacobian_pos_of_position_rank (hF : F.IsSmoothStronglyConvex)
    (old : M) {Γ : W → ℝ → M} {w : W} {t : ℝ}
    (hEL : F.IsEulerLagrangeAt (Γ w) t)
    (hlegal : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hd : DifferentiableAt ℝ
      (fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)) (w, t))
    (hlabel : Function.Injective
      (fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) old (Γ z t)) w))
    (hnormal : ∀ ξ : W, (F.chartMomentumFamily old Γ (w, t)).2
      (fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) old (Γ z t)) w ξ) = 0)
    (ℓ : (ℝ × W) ≃L[ℝ] E) :
    0 < parameterizedJacobian
      (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)) ℓ (t, w) := by
  let γ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
  let T := fderiv ℝ γ (w, t)
  let p := (F.chartMomentumFamily old Γ (w, t)).2
  have hlabelEq : ∀ ξ : W,
      fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) old (Γ z t)) w ξ = T (ξ, 0) := by
    intro ξ
    have hline : HasFDerivAt (fun z : W ↦ (z, t))
        ((ContinuousLinearMap.id ℝ W).prod (0 : W →L[ℝ] ℝ)) w :=
      (hasFDerivAt_id (𝕜 := ℝ) w).prodMk (hasFDerivAt_const t w)
    have h := hd.hasFDerivAt.comp w hline
    exact congrArg (fun L : W →L[ℝ] E ↦ L ξ) h.fderiv
  have htimeEq : deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t = T (0, 1) :=
    (hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t w).prodMk (hasDerivAt_id t))).deriv
  have hz := (hF.chartTangent_of_isEulerLagrangeAt hEL old hlegal).2
  have hpv : 0 < p (T (0, 1)) := by
    rw [← htimeEq]
    change 0 < fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t)
          (deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t)
    rw [hF.chartEnergy_euler old hz]
    exact mul_pos (by norm_num) (F.chartEnergy_pos old hz)
  have hT : Function.Injective T := injective_joint_of_normal_label T p
    (by simpa only [← hlabelEq] using hlabel)
    (by simpa only [← hlabelEq] using hnormal) hpv.ne'
  let swap := ContinuousLinearEquiv.prodComm ℝ ℝ W
  have hswap : HasFDerivAt (fun q : ℝ × W ↦ γ (q.2, q.1))
      (T.comp swap.toContinuousLinearMap) (t, w) := by
    have h := hd.hasFDerivAt.comp (t, w) swap.hasFDerivAt
    simpa only [Function.comp_def, ContinuousLinearEquiv.prodComm_apply, γ, T, swap] using! h
  have hfull : Function.Injective
      ((fderiv ℝ (fun q : ℝ × W ↦ γ (q.2, q.1)) (t, w)).comp
        ℓ.symm.toContinuousLinearMap) := by
    rw [hswap.fderiv]
    exact (hT.comp swap.injective).comp ℓ.symm.injective
  apply abs_pos.mpr
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero)
    (LinearMap.ker_eq_bot.mpr hfull)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
