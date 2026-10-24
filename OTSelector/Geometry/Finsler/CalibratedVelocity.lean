import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FundamentalInequality
import OTSelector.Geometry.Finsler.LegendreInjectivity

/-!
# Geometry.Finsler.CalibratedVelocity

* **Conditions:** For the generic helper, differentiable convex support equality; for geometric corollaries, actual equal Finsler length/energy and saturation by the same covector.
* **Objects:** Equality of actual calibrated velocities in fiber, chart and tangent spaces.
* **Proof detail:** Turn support saturation into equality of actual energy Legendre covectors, then use already established injectivity of the original Legendre map.

Mathematical sources:
- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83): Section 3.1.3, p. 69, equation (3.2), first-order convex supporting inequality.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): Strict velocity selection follows from the original strong-convexity energy data, without a new tangent norm or independent strict-convexity assumption.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedVelocity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedVelocity`; the selected original proof blocks follow. -/
section

/-!
# Equality of actual Finsler calibrated velocities

Equality in the supporting inequality makes the same supporting covector the energy
Legendre covector at both velocities. The already proved injectivity of the original
Finsler Legendre map then identifies those velocities. This reuses the actual positive
energy Hessian rather than adding a strict-convexity assumption or a new tangent norm.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equality in a differentiable convex supporting inequality identifies the two
actual differentials, by Fermat's theorem at the second contact point. -/
theorem fderiv_eq_of_convex_support_eq {L : E → ℝ} (hconv : ConvexOn ℝ univ L)
    {v w : E} (hv : DifferentiableAt ℝ L v) (hw : DifferentiableAt ℝ L w)
    (heq : fderiv ℝ L v (w - v) = L w - L v) :
    fderiv ℝ L w = fderiv ℝ L v := by
  have hmin : IsLocalMin (fun u ↦ L u - fderiv ℝ L v u) w := by
    apply Filter.Eventually.of_forall
    intro u
    have hu := support_of_convexOn_univ hconv hv u
    rw [map_sub] at hu heq
    change L w - fderiv ℝ L v w ≤ L u - fderiv ℝ L v u
    linarith
  exact sub_eq_zero.mp
    (hmin.hasFDerivAt_eq_zero (hw.hasFDerivAt.sub (fderiv ℝ L v).hasFDerivAt))

/-- A covector bounded by a length and attaining its value at a unit vector is the
actual differential there of one half the squared length. -/
theorem fderiv_half_sq_eq_of_unit_calibration {L G : E → ℝ} (p : E →L[ℝ] ℝ)
    (hL : ∀ u, L u = (G u) ^ 2 / 2) {v : E} (hv : DifferentiableAt ℝ L v)
    (hunit : G v = 1) (hbound : ∀ u, p u ≤ G u) (hsat : p v = 1) :
    fderiv ℝ L v = p := by
  have hmin : IsLocalMin (fun u ↦ L u - p u) v := by
    apply Filter.Eventually.of_forall
    intro u
    change L v - p v ≤ L u - p u
    rw [hL v, hunit, hsat, hL u]
    nlinarith [sq_nonneg (G u - 1), hbound u]
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hv.hasFDerivAt.sub p.hasFDerivAt))

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}
  (hF : F.IsSmoothStronglyConvex)
include hF

/-- Equal original energy and saturation by actual energy momentum identify the velocity. -/
theorem fiber_velocity_eq_of_energy_and_momentum (x : M) {v w : E} (hv : v ≠ 0)
    (henergy : F.fiberEnergyModel x w = F.fiberEnergyModel x v)
    (hmomentum : fderiv ℝ (F.fiberEnergyModel x) v w = 2 * F.fiberEnergyModel x v) :
    w = v := by
  have hw : w ≠ 0 := by
    intro hw
    have hzero : F.fiberEnergyModel x w = 0 := by
      simp [hw, ContinuousFinslerNorm.fiberEnergyModel]
    have hp := F.fiberEnergyModel_pos x hv
    rw [hzero] at henergy
    linarith
  apply hF.injOn_fiberEnergy_legendre x hw hv
  apply fderiv_eq_of_convex_support_eq (hF.convexOn_fiberEnergyModel x)
    (hF.differentiableAt_fiberEnergyModel x hv)
    (hF.differentiableAt_fiberEnergyModel x hw)
  rw [map_sub, hmomentum, hF.fiberEnergy_euler x hv, henergy]
  ring

/-- Equal original Finsler speed and equality in its fundamental inequality identify
both actual fiber velocities. -/
theorem fiber_velocity_eq_of_length_and_momentum (x : M) {v w : E} (hv : v ≠ 0)
    (hlength : F.toFun ⟨x, tangentFiberModelEquiv x w⟩ =
      F.toFun ⟨x, tangentFiberModelEquiv x v⟩)
    (hmomentum : fderiv ℝ (F.fiberEnergyModel x) v w =
      (F.toFun ⟨x, tangentFiberModelEquiv x v⟩ : ℝ) ^ 2) :
    w = v := by
  apply hF.fiber_velocity_eq_of_energy_and_momentum x hv
  · change (F.toFun ⟨x, tangentFiberModelEquiv x w⟩ : ℝ) ^ 2 / 2 = _
    rw [hlength]
    rfl
  · rw [hmomentum]
    change _ = 2 * ((F.toFun ⟨x, tangentFiberModelEquiv x v⟩ : ℝ) ^ 2 / 2)
    ring

/-- Equality at fixed speed in the actual chart momentum bound identifies the original
chart velocity, through the genuine inverse tangent chart. -/
theorem chart_velocity_eq_of_length_and_momentum (old : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain old) {w : E}
    (hlength : F.chartLength old (z.1, w) = F.chartLength old z)
    (hmomentum : fiberLegendre (F.chartEnergy old) z w =
      (F.chartLength old z : ℝ) ^ 2) :
    w = z.2 := by
  apply (chartFiberEquiv old hz.1).injective
  apply hF.fiber_velocity_eq_of_length_and_momentum
    ((extChartAt 𝓘(ℝ, E) old).symm z.1)
    ((chartFiberEquiv old hz.1).map_ne_zero_iff.mpr hz.2)
  · simpa only [F.chartLength_eq_fiber old hz.1] using! hlength
  · simpa only [F.chartLegendre_apply_eq_fiber old hz.1,
      F.chartLength_eq_fiber old hz.1] using! hmomentum

/-- A single actual calibration covector selects at most one original unit fiber
velocity. Its bound is against the given Finsler length in every fiber direction. -/
theorem fiber_unit_velocity_eq_of_calibration (x : M) (p : E →L[ℝ] ℝ) {v w : E}
    (hv : F.toFun ⟨x, tangentFiberModelEquiv x v⟩ = 1)
    (hw : F.toFun ⟨x, tangentFiberModelEquiv x w⟩ = 1)
    (hbound : ∀ u : E, p u ≤ (F.toFun ⟨x, tangentFiberModelEquiv x u⟩ : ℝ))
    (hpv : p v = 1) (hpw : p w = 1) : w = v := by
  have hv0 : v ≠ 0 := by
    intro hzero
    have hz : F.toFun ⟨x, tangentFiberModelEquiv x v⟩ = 0 := by
      rw [hzero]
      exact F.map_zero x
    exact zero_ne_one (hz.symm.trans hv)
  have hlegendre : fderiv ℝ (F.fiberEnergyModel x) v = p :=
    fderiv_half_sq_eq_of_unit_calibration p (fun _ ↦ rfl)
      (hF.differentiableAt_fiberEnergyModel x hv0)
      (by exact_mod_cast hv) hbound hpv
  apply hF.fiber_velocity_eq_of_length_and_momentum x hv0 (hw.trans hv.symm)
  rw [hlegendre, hpw, hv]
  norm_num

/-- In the actual tangent fiber, an original-length-bounded calibration covector
has at most one saturating unit velocity. No coordinate velocity is supplied. -/
theorem tangent_unit_velocity_eq_of_calibration (x : M)
    (p : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) {v w : TangentSpace 𝓘(ℝ, E) x}
    (hv : F.toFun ⟨x, v⟩ = 1) (hw : F.toFun ⟨x, w⟩ = 1)
    (hbound : ∀ u : TangentSpace 𝓘(ℝ, E) x, p u ≤ (F.toFun ⟨x, u⟩ : ℝ))
    (hpv : p v = 1) (hpw : p w = 1) : w = v := by
  let A := tangentFiberModelEquiv (E := E) x
  apply A.symm.injective
  apply hF.fiber_unit_velocity_eq_of_calibration x (p.comp A.toContinuousLinearMap)
  · simpa only [A, ContinuousLinearEquiv.apply_symm_apply] using hv
  · simpa only [A, ContinuousLinearEquiv.apply_symm_apply] using hw
  · intro u
    exact hbound (A u)
  · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using hpv
  · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using hpw

/-- In a genuine tangent chart, two original unit velocities saturating the same
actual length-bounded covector coincide. -/
theorem chart_unit_velocity_eq_of_calibration (old : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) old).target) (p : E →L[ℝ] ℝ) {v w : E}
    (hv : F.chartLength old (y, v) = 1) (hw : F.chartLength old (y, w) = 1)
    (hbound : ∀ u : E, p u ≤ (F.chartLength old (y, u) : ℝ))
    (hpv : p v = 1) (hpw : p w = 1) : w = v := by
  let A := chartFiberEquiv old hy
  let x := (extChartAt 𝓘(ℝ, E) old).symm y
  apply A.injective
  apply hF.fiber_unit_velocity_eq_of_calibration x (p.comp A.symm.toContinuousLinearMap)
  · simpa only [F.chartLength_eq_fiber old hy] using! hv
  · simpa only [F.chartLength_eq_fiber old hy] using! hw
  · intro u
    have h := hbound (A.symm u)
    simpa only [F.chartLength_eq_fiber old hy, A,
      ContinuousLinearEquiv.apply_symm_apply] using! h
  · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hpv
  · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hpw

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
