import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.EndpointMinimizerStability
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Geometry.Finsler.C11ReadoutDerivative

* **Conditions:** A supplied complete actual family with the true differentiable initial position/covector at one seed.
* **Objects:** Actual joint phase and position-readout differentiability at every legal finite output time.
* **Proof detail:** Represent the family locally using the genuine inverse Legendre branch and one smooth complete tangent flow, then differentiate the initial seed composite.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): No ambient parameter regularity of the supplied family, rank premise or exceptional time set is assumed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11ReadoutDerivative.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11ReadoutDerivative`; the selected original proof blocks follow. -/
section

/-!
# Actual derivatives of complete families with differentiable initial covectors

The actual initial point and momentum identify a supplied complete geodesic family
with one smooth tangent flow through the genuine Legendre inverse. Differentiability
of the initial position and covector at one seed therefore gives joint phase
differentiability at every chart-legal time. No regularity of the supplied family
in its parameter, rank premise or exceptional time set is assumed.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ContinuousFinslerNorm E M}

/-- Differentiable actual initial position and covector imply joint differentiability
of the supplied complete family's actual chart phase at every legal output time.
The complete flow, inverse branch and family identity are constructed internally. -/
theorem differentiableAt_chartMomentumFamily_of_initial_covectors
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {B : Set W} (hB : IsOpen B) {σ : W → E} {p : W → E →L[ℝ] ℝ}
    (hBtarget : MapsTo σ B (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : W → ℝ → M}
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hinit : ∀ w ∈ B, Γ w 0 = (extChartAt 𝓘(ℝ, E) initial).symm (σ w))
    (hp : ∀ w ∈ B, F.chartMomentumFamily initial Γ (w, 0) = (σ w, p w))
    {w₀ : W} (hw₀ : w₀ ∈ B) (hσ : DifferentiableAt ℝ σ w₀)
    (hD : DifferentiableAt ℝ p w₀) (terminal : M) (t : ℝ)
    (hlegal : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    DifferentiableAt ℝ (F.chartMomentumFamily terminal Γ) (w₀, t) := by
  have hsource (w : W) (hw : w ∈ B) :
      Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hinit w hw]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target (hBtarget hw)
  let z : W → E × E := fun w ↦
    ((extChartAt 𝓘(ℝ, E) initial ∘ Γ w) 0,
      deriv (extChartAt 𝓘(ℝ, E) initial ∘ Γ w) 0)
  have hz (w : W) (hw : w ∈ B) : z w ∈ chartEnergyDomain initial :=
    (hF.chartTangent_of_isEulerLagrangeAt (hEL w hw 0 (mem_univ _))
      initial (hsource w hw)).2
  let P : W → E × (E →L[ℝ] ℝ) := fun w ↦ (σ w, p w)
  have hP : DifferentiableAt ℝ P w₀ := hσ.prodMk hD
  have hphase (w : W) (hw : w ∈ B) :
      parametricLegendre (F.chartEnergy initial) (z w) = P w := hp w hw
  obtain ⟨e, he, _, hzt, hsub, _, hInv, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse initial (hz w₀ hw₀)
  have hPtarget : P w₀ ∈ e.target := (hphase w₀ hw₀) ▸ hzt
  let S : W → E × E := fun w ↦ e.symm (P w)
  have hS : DifferentiableAt ℝ S w₀ :=
    ((hInv.contDiffAt (e.open_target.mem_nhds hPtarget)).differentiableAt
      (by simp)).comp w₀ hP
  have hnear : ∀ᶠ w in 𝓝 w₀, w ∈ B ∧ P w ∈ e.target := by
    filter_upwards [hB.mem_nhds hw₀,
      hP.continuousAt (e.open_target.mem_nhds hPtarget)] with w hw hpw
    exact ⟨hw, hpw⟩
  obtain ⟨Φ, hΦEL, hΦinit, hΦ⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial 0
  have hcurve : (fun w ↦ Φ (S w)) =ᶠ[𝓝 w₀] Γ := by
    filter_upwards [hnear] with w hw
    have hSlegal : S w ∈ chartEnergyDomain initial := hsub (e.map_target hw.2)
    have hSz : S w = z w := by
      apply hF.injOn_parametricLegendre_chartEnergy initial hSlegal (hz w hw.1)
      rw [hphase w hw.1, ← he]
      exact e.right_inv hw.2
    rw [hSz]
    exact (hF.eq_complete_family_of_isEulerLagrangeOn initial hΦEL hΦinit
      (hEL w hw.1) (hsource w hw.1)).2
  have hSlegal : S w₀ ∈ chartEnergyDomain initial := hsub (e.map_target hPtarget)
  have hcenter : Φ (S w₀) = Γ w₀ := hcurve.self_of_nhds
  have hΦlegal : Φ (S w₀) t ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    rw [hcenter]
    exact hlegal
  have hread : DifferentiableAt ℝ (F.chartMomentumFamily terminal Φ) (S w₀, t) :=
    (hF.contDiffAt_chartMomentumFamily_of_tangentFamily
    (isOpen_chartEnergyDomain initial) hΦEL hΦ hSlegal terminal t hΦlegal)
      |>.differentiableAt (by norm_num)
  have hseed : DifferentiableAt ℝ (fun q : W × ℝ ↦ (S q.1, q.2)) (w₀, t) :=
    (DifferentiableAt.comp (f := fun q : W × ℝ ↦ q.1) (g := S)
      (w₀, t) hS differentiableAt_fst).prodMk differentiableAt_snd
  have hcomp : DifferentiableAt ℝ
      (fun q : W × ℝ ↦ F.chartMomentumFamily terminal Φ (S q.1, q.2)) (w₀, t) :=
    DifferentiableAt.comp (f := fun q : W × ℝ ↦ (S q.1, q.2))
      (g := F.chartMomentumFamily terminal Φ) (w₀, t) hread hseed
  have heq : (fun q : W × ℝ ↦ F.chartMomentumFamily terminal Φ (S q.1, q.2))
      =ᶠ[𝓝 (w₀, t)] F.chartMomentumFamily terminal Γ := by
    filter_upwards [(continuousAt_fst : ContinuousAt (Prod.fst : W × ℝ → W) (w₀, t))
      hcurve] with q hq
    change Φ (S q.1) = Γ q.1 at hq
    simp only [ContinuousFinslerNorm.chartMomentumFamily, hq]
  exact hcomp.congr_of_eventuallyEq heq.symm

/-- At a seed where the initial covector is differentiable, the actual fixed-time
position readout of the same complete family has its ordinary Fréchet derivative.
This applies to a C1,1 extension at every point where its derivative is differentiable. -/
theorem differentiableAt_chart_readout_of_initial_covector
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {B : Set E} (hB : IsOpen B)
    (hBtarget : B ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {p : E → E →L[ℝ] ℝ} {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ B, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ B, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ B, F.chartMomentumFamily initial Γ (x, 0) = (x, p x))
    {x₀ : E} (hx₀ : x₀ ∈ B) (hD : DifferentiableAt ℝ p x₀)
    (terminal : M) (t : ℝ)
    (hlegal : Γ x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    DifferentiableAt ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)) x₀ := by
  have hphase := hF.differentiableAt_chartMomentumFamily_of_initial_covectors
    hcomplete initial hB hBtarget hEL hinit hp hx₀ differentiableAt_id hD terminal t hlegal
  have hpos : DifferentiableAt ℝ
      (fun q : E × ℝ ↦ extChartAt 𝓘(ℝ, E) terminal (Γ q.1 q.2)) (x₀, t) := hphase.fst
  exact DifferentiableAt.comp (f := fun x : E ↦ (x, t))
    (g := fun q : E × ℝ ↦ extChartAt 𝓘(ℝ, E) terminal (Γ q.1 q.2)) x₀ hpos
    (differentiableAt_id.prodMk (differentiableAt_const t))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
