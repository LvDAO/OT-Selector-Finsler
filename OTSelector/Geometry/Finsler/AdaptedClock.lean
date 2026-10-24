import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.ODE.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.NormedSpace.CovectorSplitting
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.LengthHessian

/-!
# Geometry.Finsler.AdaptedClock

* **Conditions:** Actual nonzero Finsler momentum/velocity, or a general covector with nonzero pairing and a continuous linear model equivalence.
* **Objects:** A momentum-kernel clock sending the actual velocity to (1,0), and the actual pulled-back energy/length with preserved positive Hessian.
* **Proof detail:** Split along velocity and covector kernel, differentiate the inverse-linear tangent pullback and use original Hessian positivity.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): Only the model-with-corners coordinate integrands are changed; a replacement global Finsler atlas/norm is not constructed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedClock.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedClock`; the selected original proof blocks follow. -/
section

/-!
# Genuine linear clocks adapted to the original Finsler velocity

The actual momentum and its nonzero velocity split the model into a time coordinate
and the momentum kernel. The velocity has coordinates (1,0). The original chart energy
and length are pulled back by the inverse linear tangent lift; their smoothness and
actual positive vertical Hessian are preserved. No replacement Finsler norm is chosen.

The model-with-corners change keeps the original manifold atlas. These results provide
actual coordinate Lagrangians; transporting the project-wide Finsler structure to a
new standard-model atlas is not asserted here.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual covector supplies the clock; its kernel supplies the transverse model. -/
def covectorClock (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) : E ≃L[ℝ] (ℝ × p.ker) :=
  (covectorSplitting p v hv).symm.trans (ContinuousLinearEquiv.prodComm ℝ p.ker ℝ)

/-- The clock coordinate is normalized evaluation by the same covector. -/
theorem covectorClock_fst (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (u : E) :
    (covectorClock p v hv u).1 = p u / p v :=
  covectorSplitting_symm_snd p v hv u

/-- The chosen velocity becomes the positive unit time direction. -/
theorem covectorClock_velocity (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) :
    covectorClock p v hv v = (1, 0) := by
  have h : covectorSplitting p v hv (0, 1) = v := by simp
  have hi : (covectorSplitting p v hv).symm v = (0, 1) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (congrArg (covectorSplitting p v hv).symm h).symm
  rw [covectorClock, ContinuousLinearEquiv.trans_apply, hi]
  rfl

/-- A linear coordinate change has the literal product action as its actual tangent lift. -/
theorem tangentLift_linearEquiv (A : E ≃L[ℝ] G) (z : E × E) :
    tangentLift A z = (A z.1, A z.2) := by
  simp only [tangentLift, A.hasFDerivAt.fderiv]
  rfl

/-- Pulling the actual re-coordinatized curve back recovers its actual old phase. -/
theorem tangentLift_symm_linearEquiv_curve (A : E ≃L[ℝ] G) {x : ℝ → E} {t : ℝ}
    (hx : DifferentiableAt ℝ x t) :
    tangentLift A.symm ((A ∘ x) t, deriv (A ∘ x) t) = (x t, deriv x t) := by
  rw [tangentLift_linearEquiv,
    (A.hasFDerivAt.comp_hasDerivAt t hx.hasDerivAt).deriv]
  simp

private theorem hessian_linearEquiv {L : E → ℝ} (A : G ≃L[ℝ] E) {v : G}
    (hL : DifferentiableAt ℝ (fderiv ℝ L) (A v)) (u w : G) :
    fderiv ℝ (fderiv ℝ (L ∘ A)) v u w =
      fderiv ℝ (fderiv ℝ L) (A v) (A u) (A w) := by
  have he : fderiv ℝ (L ∘ A) = fun x ↦ (fderiv ℝ L (A x)).comp (A : G →L[ℝ] E) := by
    funext x
    exact A.comp_right_fderiv
  rw [he]
  have hd := ((hL.hasFDerivAt.comp v A.hasFDerivAt).clm_comp
    (hasFDerivAt_const (A : G →L[ℝ] E) v)).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The model change is an actual coordinate change on the same manifold and curve. -/
theorem hasDerivAt_extChartAt_linearModel (A : E ≃L[ℝ] G) (old : M)
    {c : ℝ → M} {t : ℝ} {v : E}
    (hc : HasDerivAt (extChartAt 𝓘(ℝ, E) old ∘ c) v t) :
    HasDerivAt (extChartAt ((𝓘(ℝ, E)).transContinuousLinearEquiv A) old ∘ c) (A v) t :=
  A.hasFDerivAt.comp_hasDerivAt t hc

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- The inverse linear tangent lift preserves joint smoothness of the original energy. -/
theorem contDiffOn_pullback_chartEnergy (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] G) :
    ContDiffOn ℝ ∞ (pullbackEnergy A.symm (F.chartEnergy old))
      ((tangentLift A.symm) ⁻¹' chartEnergyDomain old) := by
  have ht : ContDiff ℝ ∞ (tangentLift A.symm) := by
    rw [show tangentLift A.symm = (fun z : G × G ↦ (A.symm z.1, A.symm z.2)) from
      funext (tangentLift_linearEquiv A.symm)]
    exact (A.symm.contDiff.comp contDiff_fst).prodMk (A.symm.contDiff.comp contDiff_snd)
  exact (hF.contDiffOn_chartEnergy old).comp ht.contDiffOn (fun _ h ↦ h)

/-- The pulled-back length is the same original Finsler length, jointly smooth off zero. -/
theorem contDiffOn_pullback_chartLength (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] G) :
    ContDiffOn ℝ ∞ (pullbackEnergy A.symm (fun z ↦ (F.chartLength old z : ℝ)))
      ((tangentLift A.symm) ⁻¹' chartEnergyDomain old) := by
  have ht : ContDiff ℝ ∞ (tangentLift A.symm) := by
    rw [show tangentLift A.symm = (fun z : G × G ↦ (A.symm z.1, A.symm z.2)) from
      funext (tangentLift_linearEquiv A.symm)]
    exact (A.symm.contDiff.comp contDiff_fst).prodMk (A.symm.contDiff.comp contDiff_snd)
  exact (hF.contDiffOn_chartLength old).comp ht.contDiffOn (fun _ h ↦ h)

/-- The new momentum is precisely the pullback of the original energy momentum. -/
theorem fiberLegendre_pullback_chartEnergy (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] G) {z : G × G}
    (hz : tangentLift A.symm z ∈ chartEnergyDomain old) :
    fiberLegendre (pullbackEnergy A.symm (F.chartEnergy old)) z =
      (fiberLegendre (F.chartEnergy old) (tangentLift A.symm z)).comp
        A.symm.toContinuousLinearMap := by
  rw [fiberLegendre_pullbackEnergy
    (((hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hz)).differentiableAt (by simp)),
    A.symm.hasFDerivAt.fderiv]

/-- This is the actual old fiber Hessian evaluated on inverse-transformed directions. -/
theorem pullback_chartEnergy_hessian (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] G) {z : G × G}
    (hz : tangentLift A.symm z ∈ chartEnergyDomain old) (u w : G) :
    fderiv ℝ (fderiv ℝ (fun v ↦ pullbackEnergy A.symm (F.chartEnergy old) (z.1, v)))
      z.2 u w = fderiv ℝ (fderiv ℝ (fun v ↦ F.chartEnergy old (A.symm z.1, v)))
        (A.symm z.2) (A.symm u) (A.symm w) := by
  have hc := (hF.contDiffOn_chartEnergy old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)
  rw [tangentLift_linearEquiv] at hc
  have hv : ContDiffAt ℝ ∞ (fun v ↦ F.chartEnergy old (A.symm z.1, v)) (A.symm z.2) :=
    hc.comp _ (contDiffAt_const.prodMk contDiffAt_id)
  have he : (fun v ↦ pullbackEnergy A.symm (F.chartEnergy old) (z.1, v)) =
      (fun v ↦ F.chartEnergy old (A.symm z.1, v)) ∘ A.symm := by
    funext v
    simp only [pullbackEnergy, tangentLift_linearEquiv, Function.comp_apply]
  rw [he]
  exact hessian_linearEquiv A.symm
    ((hv.fderiv_right (m := 1) (by simp)).differentiableAt_one) u w

/-- The original strong convexity is preserved under the genuine linear model change. -/
theorem pullback_chartEnergy_hessian_pos (hF : F.IsSmoothStronglyConvex)
    (old : M) (A : E ≃L[ℝ] G) {z : G × G}
    (hz : tangentLift A.symm z ∈ chartEnergyDomain old) {u : G} (hu : u ≠ 0) :
    0 < fderiv ℝ
      (fderiv ℝ (fun v ↦ pullbackEnergy A.symm (F.chartEnergy old) (z.1, v))) z.2 u u := by
  rw [hF.pullback_chartEnergy_hessian old A hz]
  apply hF.chartEnergy_hessian_pos old
    (show (A.symm z.1, A.symm z.2) ∈ chartEnergyDomain old from
      (tangentLift_linearEquiv A.symm z) ▸ hz)
  exact fun h ↦ hu (A.symm.injective (h.trans (_root_.map_zero A.symm).symm))

/-- Actual momentum selects a codimension-one model with positive central clock velocity. -/
theorem exists_positive_chartClock [FiniteDimensional ℝ E] (hF : F.IsSmoothStronglyConvex)
    (old : M) {z : E × E} (hz : z ∈ chartEnergyDomain old) :
    let p := fiberLegendre (F.chartEnergy old) z
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
    ∃ A : E ≃L[ℝ] (ℝ × p.ker), A z.2 = (1, 0) ∧
      (∀ u : E, (A u).1 = p u / p z.2) ∧ 0 < (A z.2).1 := by
  let p := fiberLegendre (F.chartEnergy old) z
  have hpv : 0 < p z.2 := by
    rw [show p z.2 = 2 * F.chartEnergy old z from hF.chartEnergy_euler old hz]
    exact mul_pos (by norm_num) (F.chartEnergy_pos old hz)
  have hp : p.toLinearMap ≠ 0 := by
    intro h
    have he : p z.2 = 0 := congrArg (fun q : E →ₗ[ℝ] ℝ ↦ q z.2) h
    exact hpv.ne' he
  refine ⟨Module.Dual.finrank_ker_add_one_of_ne_zero hp,
    covectorClock p z.2 hpv.ne', covectorClock_velocity p z.2 hpv.ne',
    covectorClock_fst p z.2 hpv.ne', ?_⟩
  rw [covectorClock_velocity]
  norm_num

/-- Every actual intrinsic EL curve admits genuine local product coordinates with
positive clock velocity. Its actual equation, energy and length are retained by the
inverse linear tangent pullback of the original coordinate Lagrangians. -/
theorem exists_adapted_chartClock_of_isEulerLagrangeAt [FiniteDimensional ℝ E]
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {t : ℝ}
    (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    let x := extChartAt 𝓘(ℝ, E) old ∘ c
    let p := fiberLegendre (F.chartEnergy old) (x t, deriv x t)
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
    ∃ (A : E ≃L[ℝ] (ℝ × p.ker)) (J : Set ℝ),
      let y := extChartAt ((𝓘(ℝ, E)).transContinuousLinearEquiv A) old ∘ c
      IsOpen J ∧ t ∈ J ∧ MapsTo c J (extChartAt 𝓘(ℝ, E) old).source ∧
      ContDiffOn ℝ ∞ y J ∧ HasDerivAt y (1, 0) t ∧
      (∀ s ∈ J, 0 < (deriv y s).1) ∧
      (∀ s ∈ J, tangentLift A.symm (y s, deriv y s) ∈ chartEnergyDomain old) ∧
      (∀ s ∈ J, HasDerivAt
        (fun r ↦ fiberLegendre (pullbackEnergy A.symm (F.chartEnergy old))
          (y r, deriv y r))
        (baseEnergyDifferential (pullbackEnergy A.symm (F.chartEnergy old))
          (y s, deriv y s)) s) ∧
      ∀ s ∈ J,
        pullbackEnergy A.symm (F.chartEnergy old) (y s, deriv y s) =
          F.chartEnergy old (x s, deriv x s) ∧
        pullbackEnergy A.symm (fun z ↦ (F.chartLength old z : ℝ)) (y s, deriv y s) =
          (F.chartLength old (x s, deriv x s) : ℝ) := by
  let x := extChartAt 𝓘(ℝ, E) old ∘ c
  obtain ⟨U, hU, ht, hm, hxc, hphase, hEL⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc old hx
  obtain ⟨hdim, A, hAv, _, _⟩ := hF.exists_positive_chartClock old (hphase t ht)
  change A (deriv x t) = (1, 0) at hAv
  let y := A ∘ x
  have hy : ContDiffOn ℝ ∞ y U := A.contDiff.comp_contDiffOn hxc
  have hxD (s : ℝ) (hs : s ∈ U) : DifferentiableAt ℝ x s :=
    (hxc.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)
  have hyt : HasDerivAt y (1, 0) t :=
    (A.hasFDerivAt.comp_hasDerivAt t (hxD t ht).hasDerivAt).congr_deriv hAv
  have hdy : ContinuousOn (fun s ↦ (deriv y s).1) U :=
    (hy.deriv_of_isOpen hU (by simp : (1 : ℕ∞ω) + 1 ≤ ∞)).continuousOn.fst
  let J := U ∩ (fun s ↦ (deriv y s).1) ⁻¹' Ioi 0
  have hJ : IsOpen J := hdy.isOpen_inter_preimage hU isOpen_Ioi
  have htJ : t ∈ J := ⟨ht, by change 0 < (deriv y t).1; rw [hyt.deriv]; norm_num⟩
  have hlift (s : ℝ) (hs : s ∈ U) :
      tangentLift A.symm (y s, deriv y s) = (x s, deriv x s) :=
    tangentLift_symm_linearEquiv_curve A (hxD s hs)
  refine ⟨hdim, A, J, hJ, htJ, hm.mono_left inter_subset_left,
    hy.mono inter_subset_left, hyt, (fun _ hs ↦ hs.2), ?_, ?_, ?_⟩
  · intro s hs
    change tangentLift A.symm (y s, deriv y s) ∈ chartEnergyDomain old
    rw [hlift s hs.1]
    exact hphase s hs.1
  · intro s hs
    apply hasDerivAt_eulerLagrange_pullback isOpen_univ (isOpen_chartEnergyDomain old)
      A.symm.contDiff.contDiffOn ((hF.contDiffOn_chartEnergy old).of_le (by simp))
      hU (hy.of_le (by simp)) (mapsTo_univ _ _) (fun r hr ↦ ?_) hs.1
    · simpa only [Function.comp_def, y, x, ContinuousLinearEquiv.symm_apply_apply] using
        hEL s hs.1
    · rw [hlift r hr]
      exact hphase r hr
  · intro s hs
    exact ⟨congrArg (F.chartEnergy old) (hlift s hs.1),
      congrArg (fun z ↦ (F.chartLength old z : ℝ)) (hlift s hs.1)⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
