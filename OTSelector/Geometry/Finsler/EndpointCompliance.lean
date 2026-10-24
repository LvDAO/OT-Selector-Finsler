import OTSelector.Analysis.Calculus.Variational.EndpointJacobiCompliance
import OTSelector.Analysis.Calculus.Variational.HamiltonianFlatBase
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteChartBox
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlatBaseEndpoint
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Geometry.Finsler.EndpointCompliance

* **Conditions:** A legal actual intrinsic curve in smooth strongly convex finite-dimensional Finsler geometry; endpoint variation recovery additionally uses the stated zero-base-column equation.
* **Objects:** Continuous positive inverse energy Hessian, its symmetric invertible time integral and actual momentum variation recovered from endpoint derivatives.
* **Proof detail:** Identify the inverse branch momentum derivative, integrate its positive bilinear pairing and integrate the genuine constant-momentum variational equation.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46): Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.

Source relation (derived): Integral positivity/invertibility is general on a legal nondegenerate segment; the simple endpoint-recovery formula retains its explicit flat-base hypothesis.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEndpointCompliance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEndpointCompliance`; the selected original proof blocks follow. -/
section

/-!
# Actual endpoint compliance of the original Finsler family

The original energy's inverse vertical Hessian is continuous along every legal segment
of the same intrinsic family. Its actual integral is positive, symmetric and invertible.
The proved parameter-variation equation then recovers the actual momentum variation
from actual endpoint position derivatives, with no independently prescribed Jacobi data.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The inverse actual vertical energy Hessian evaluated on the actual chart curve. -/
def chartInverseEnergyHessian (F : ContinuousFinslerNorm E M) (old : M)
    (c : ℝ → M) (t : ℝ) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  (verticalEnergyHessian (F.chartEnergy old)
    ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t)).inverse

/-- The original inverse energy Hessian integrated along the actual curve segment. -/
def chartEndpointCompliance (F : ContinuousFinslerNorm E M) (old : M)
    (c : ℝ → M) (a b : ℝ) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  endpointCompliance (F.chartInverseEnergyHessian old c) a b

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Every genuine local Legendre branch represents the same actual inverse energy Hessian. -/
theorem chartInverseEnergyHessian_eq_inverseLegendreMomentumDerivative
    (hF : F.IsSmoothStronglyConvex) (old : M) {c : ℝ → M} {t : ℝ}
    (hc : F.IsEulerLagrangeAt c t) (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hs : e.source ⊆ chartEnergyDomain old) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hp : eulerLagrangePhaseLift (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ e.target) :
    F.chartInverseEnergyHessian old c t = inverseLegendreMomentumDerivative e
      (eulerLagrangePhaseLift (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old ∘ c) t) := by
  have hz := (hF.chartTangent_of_isEulerLagrangeAt hc old hx).2
  have hident : e.symm (eulerLagrangePhaseLift (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old ∘ c) t) =
      ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) := by
    apply hF.injOn_parametricLegendre_chartEnergy old (hs (e.map_target hp)) hz
    have h := e.right_inv hp
    rw [he] at h
    exact h
  rw [inverseLegendreMomentumDerivative_eq_inverse he hp
    ((hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds (hs (e.map_target hp))))
    ((hi.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp))
    (fun u hu ↦ hF.chartEnergy_hessian_pos old (hs (e.map_target hp)) hu), hident]
  rfl

/-- Joint regularity of the actual tangent family makes its original inverse energy
Hessian continuous, with local inverse-branch compatibility derived from the original energy. -/
theorem continuousAt_chartInverseEnergyHessian (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (old : M) (t : ℝ)
    (hx : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    ContinuousAt (F.chartInverseEnergyHessian old (Γ w)) t := by
  obtain ⟨e, r, he, hs, hi, hr, _, hxD, hΨ, hm, _⟩ :=
    hF.exists_chartMomentumFamily_box hB hEL hG hw old t hx
  have ht : (w, t) ∈ Metric.ball w r ×ˢ Ioo (t - r) (t + r) :=
    ⟨Metric.mem_ball_self hr, by constructor <;> linarith⟩
  have hQ : ContinuousAt (fun s ↦ F.chartMomentumFamily old Γ (w, s)) t :=
    (hΨ.contDiffAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ht)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
  have hDi : ContinuousAt (fderiv ℝ e.symm) (F.chartMomentumFamily old Γ (w, t)) :=
    ((hi.contDiffAt (e.open_target.mem_nhds (hm ht))).fderiv_right
      (m := ∞) (by simp)).continuousAt
  have hD : ContinuousAt (fun s ↦ fderiv ℝ e.symm
      (F.chartMomentumFamily old Γ (w, s))) t :=
    hDi.comp (f := fun s ↦ F.chartMomentumFamily old Γ (w, s)) hQ
  have hC : ContinuousAt (fun s ↦ inverseLegendreMomentumDerivative e
      (F.chartMomentumFamily old Γ (w, s))) t :=
    (continuousAt_const.clm_comp hD).clm_comp continuousAt_const
  apply hC.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht.2] with s hst
  have hws : (w, s) ∈ Metric.ball w r ×ˢ Ioo (t - r) (t + r) := ⟨ht.1, hst⟩
  exact hF.chartInverseEnergyHessian_eq_inverseLegendreMomentumDerivative old
    (hEL w hw s (mem_univ _)) (hxD (w, s) hws) he hs hi (hm hws)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Original strong convexity gives positivity of the actual inverse energy Hessian. -/
theorem chartInverseEnergyHessian_pos (hF : F.IsSmoothStronglyConvex)
    (old : M) {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) {p : E →L[ℝ] ℝ} (hp : p ≠ 0) :
    0 < p (F.chartInverseEnergyHessian old c t p) :=
  inverse_verticalEnergyHessian_pos (fun _ hu ↦ hF.chartEnergy_hessian_pos old
    (hF.chartTangent_of_isEulerLagrangeAt hc old hx).2 hu) hp

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Actual scalar energy Hessian symmetry gives canonical symmetry of its inverse. -/
theorem chartInverseEnergyHessian_symm (hF : F.IsSmoothStronglyConvex)
    (old : M) {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) (p q : E →L[ℝ] ℝ) :
    p (F.chartInverseEnergyHessian old c t q) = q (F.chartInverseEnergyHessian old c t p) := by
  have hz := (hF.chartTangent_of_isEulerLagrangeAt hc old hx).2
  obtain ⟨e, he, _, hp, hs, hi, _, _, _⟩ := hF.exists_smooth_chartHamiltonian old hz
  change eulerLagrangePhaseLift (F.chartEnergy old)
    (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ e.target at hp
  rw [hF.chartInverseEnergyHessian_eq_inverseLegendreMomentumDerivative old hc hx he hs hi hp,
    ← localHamiltonianBlockC_eq_inverseLegendreMomentumDerivative
      ((hF.contDiffOn_chartEnergy old).mono hs) hi hp]
  exact localHamiltonianBlockC_symm he ((hF.contDiffOn_chartEnergy old).mono hs) hi hp q p

/-- The actual integrated response is invertible on each legal nontrivial curve segment. -/
theorem isInvertible_chartEndpointCompliance (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (old : M) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    (F.chartEndpointCompliance old (Γ w) a b).IsInvertible := by
  apply endpointCompliance_isInvertible hab
    (fun t ht ↦ (hF.continuousAt_chartInverseEnergyHessian hB hEL hG hw old t
      (hx t ht)).continuousWithinAt)
  exact fun t ht p hp ↦ hF.chartInverseEnergyHessian_pos old
    (hEL w hw t (mem_univ _)) (hx t ht) hp

/-- The same actual family has constant momentum variation equal to the inverse
integrated original Hessian applied to its actual endpoint position variation. -/
theorem chartMomentumVariation_eq_compliance_inverse_phase
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (old : M) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hzero : ∀ t ∈ Icc a b, ∀ u : E, fderiv ℝ (fderiv ℝ (F.chartEnergy old))
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t) (u, 0) = 0) (ξ : W) :
    ∀ t ∈ Icc a b,
      (fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, t)) w ξ).2 =
        (F.chartEndpointCompliance old (Γ w) a b).inverse
          ((fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, b)) w ξ).1 -
            (fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, a)) w ξ).1) := by
  let R := fun t ↦ fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, t)) w ξ
  have hODE (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt R (F.chartInverseEnergyHessian old (Γ w) t (R t).2, 0) t :=
    hF.hasDerivAt_chartMomentumVariation_of_hessian_base_zero hB hEL hG hw old t
      (hx t ht) (hzero t ht) ξ
  exact momentum_eq_endpointCompliance_inverse hab
    (fun t ht ↦ (hF.continuousAt_chartInverseEnergyHessian hB hEL hG hw old t
      (hx t ht)).continuousWithinAt)
    (fun t ht p hp ↦ hF.chartInverseEnergyHessian_pos old
      (hEL w hw t (mem_univ _)) (hx t ht) hp)
    (fun t ht ↦ (hODE t ht).fst) (fun t ht ↦ (hODE t ht).snd)

/-- The compliance formula expressed directly through the true endpoint position
Fréchet derivatives, with both endpoints and every intermediate momentum retained. -/
theorem chartMomentumVariation_eq_compliance_inverse
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (old : M) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hzero : ∀ t ∈ Icc a b, ∀ u : E, fderiv ℝ (fderiv ℝ (F.chartEnergy old))
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t) (u, 0) = 0) (ξ : W) :
    ∀ t ∈ Icc a b,
      (fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, t)) w ξ).2 =
        (F.chartEndpointCompliance old (Γ w) a b).inverse
          (fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v b)) w ξ -
            fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v a)) w ξ) := by
  have hpos (t : ℝ) (ht : t ∈ Icc a b) :
      (fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, t)) w ξ).1 =
        fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v t)) w ξ := by
    obtain ⟨e, r, _, _, _, hr, _, _, hΨ, _, _⟩ :=
      hF.exists_chartMomentumFamily_box hB hEL hG hw old t (hx t ht)
    have hwt : (w, t) ∈ Metric.ball w r ×ˢ Ioo (t - r) (t + r) :=
      ⟨Metric.mem_ball_self hr, by constructor <;> linarith⟩
    have hd : DifferentiableAt ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, t)) w :=
      ((hΨ.contDiffAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hwt)).comp w
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
    exact (congrArg (fun D : W →L[ℝ] E ↦ D ξ) hd.hasFDerivAt.fst.fderiv).symm
  intro t ht
  rw [hF.chartMomentumVariation_eq_compliance_inverse_phase hB hEL hG hw old hab hx hzero ξ t ht,
    hpos b (right_mem_Icc.mpr hab.le), hpos a (left_mem_Icc.mpr hab.le)]

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
