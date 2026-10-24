import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.C11FiniteTimeLipschitz

* **Conditions:** A given complete actual family with C1,1 initial momentum and its true initial-position identity.
* **Objects:** Joint/local finite-time Lipschitz chart readouts and continuity at every fixed time.
* **Proof detail:** Represent the family by the same complete tangent flow through the actual Legendre inverse, then compose smooth dependence with the C1,1 initial covector.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Only forward finite-time readout bounds are proved here; no inverse-flow estimate is asserted.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11FiniteTimeLipschitz.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11FiniteTimeLipschitz`; the selected original proof blocks follow. -/
section

/-!
# Finite-time Lipschitz readout of the actual C1,1 geodesic family

An actual complete Euler--Lagrange family with prescribed C1,1 initial covectors
agrees with the original complete tangent flow after the actual Legendre inverse.
Consequently every fixed finite-time position readout is locally Lipschitz in any
chart containing the central output point. No inverse-flow estimate is asserted.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [PreconnectedSpace M] in
/-- Equal actual initial chart phases determine the same complete intrinsic curve. -/
private theorem complete_eq_of_initial_chart_momentum
    (hF : F.IsSmoothStronglyConvex) (old : M) {c d : ℝ → M}
    (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hcx : c 0 ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hdx : d 0 ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hi : eulerLagrangePhaseLift (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old ∘ c) 0 =
      eulerLagrangePhaseLift (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old ∘ d) 0) :
    c = d := by
  have hcr := hF.chartTangent_of_isEulerLagrangeAt (hc 0 (mem_univ _)) old hcx
  have hdr := hF.chartTangent_of_isEulerLagrangeAt (hd 0 (mem_univ _)) old hdx
  have hz := hF.injOn_parametricLegendre_chartEnergy old hcr.2 hdr.2 hi
  have hcs : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ ∈
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).source := by
    simpa only [extChartAt_source, FiberBundle.chartedSpace_chartAt, mfld_simps] using hcx
  have hds : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ ∈
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).source := by
    simpa only [extChartAt_source, FiberBundle.chartedSpace_chartAt, mfld_simps] using hdx
  have hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ :=
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).injOn hcs hds
        (hcr.1.trans (hz.trans hdr.1.symm))
  exact funext (fun t ↦ hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
    hc hd (mem_univ 0) hv (mem_univ t))


/-- The same complete original family with C1,1 initial covectors has a jointly
Lipschitz position readout near every finite seed-time point in any legal output chart.
The original family is identified with the actual complete flow on the full time axis. -/
theorem exists_joint_lipschitz_chart_readout_of_C11_initial_momentum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {B : Set E} (hB : IsOpen B)
    (hBtarget : B ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ B, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ B, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ B, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {x₀ : E} (hx₀ : x₀ ∈ B) (terminal : M) (s : ℝ)
    (hlegal : Γ x₀ s ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    ∃ (r : ℝ) (C : ℝ≥0), 0 < r ∧ closedBall (x₀, s) r ⊆ B ×ˢ univ ∧
      MapsTo (fun q : E × ℝ ↦ Γ q.1 q.2) (closedBall (x₀, s) r)
        (extChartAt 𝓘(ℝ, E) terminal).source ∧
      LipschitzOnWith C (fun q : E × ℝ ↦ extChartAt 𝓘(ℝ, E) terminal (Γ q.1 q.2))
        (closedBall (x₀, s) r) := by
  have hsource (x : E) (hx : x ∈ B) :
      Γ x 0 ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hinit x hx]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target (hBtarget hx)
  let z₀ : E × E := ((extChartAt 𝓘(ℝ, E) initial ∘ Γ x₀) 0,
    deriv (extChartAt 𝓘(ℝ, E) initial ∘ Γ x₀) 0)
  have hz₀ : z₀ ∈ chartEnergyDomain initial :=
    (hF.chartTangent_of_isEulerLagrangeAt (hEL x₀ hx₀ 0 (mem_univ _))
      initial (hsource x₀ hx₀)).2
  let p : E → E × (E →L[ℝ] ℝ) := fun x ↦ (x, fderiv ℝ G x)
  have hp₀ : p x₀ = parametricLegendre (F.chartEnergy initial) z₀ := by
    exact (hp x₀ hx₀).symm
  obtain ⟨e, he, _, hzt, hsub, _, hInv, hbase, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse initial hz₀
  let S : E → E × E := fun x ↦ e.symm (p x)
  have hpcont : Continuous p := continuous_id.prodMk (hG.continuous_fderiv one_ne_zero)
  have hpLip : LipschitzWith (max 1 L) p := LipschitzWith.id.prodMk hLip
  have hp₀mem : p x₀ ∈ e.target := hp₀ ▸ hzt
  obtain ⟨C, V, hV, hVLip⟩ :=
    ((hInv.contDiffAt (e.open_target.mem_nhds hp₀mem)).of_le (by simp)).exists_lipschitzOnWith
  have hnear : B ∩ p ⁻¹' (V ∩ e.target) ∈ 𝓝 x₀ :=
    inter_mem (hB.mem_nhds hx₀) (hpcont.continuousAt.preimage_mem_nhds
      (inter_mem hV (e.open_target.mem_nhds hp₀mem)))
  obtain ⟨ρ, hρ, hρmap⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  have hSLip : LipschitzOnWith (C * max 1 L) S (closedBall x₀ ρ) :=
    hVLip.comp hpLip.lipschitzOnWith (fun _ hx ↦ (hρmap hx).2.1)
  have hSAt : ContinuousAt S x₀ :=
    (hSLip.continuousOn x₀ (mem_closedBall_self hρ.le)).continuousAt
      (closedBall_mem_nhds _ hρ)
  have hSlegal (x : E) (hx : x ∈ closedBall x₀ ρ) :
      S x ∈ chartEnergyDomain initial := hsub (e.map_target (hρmap hx).2.2)
  have hSbase (x : E) (hx : x ∈ closedBall x₀ ρ) : (S x).1 = x :=
    hbase (p x) (hρmap hx).2.2
  obtain ⟨Φ, hELΦ, hi, hΦ⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial 0
  have hΦzero (x : E) (hx : x ∈ closedBall x₀ ρ) :
      Φ (S x) 0 = (extChartAt 𝓘(ℝ, E) initial).symm x := by
    have hb := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hi (S x) (hSlegal x hx))
    rw [tangentChart_symm_eq initial (hSlegal x hx).1 (S x).2] at hb
    change Φ (S x) 0 = (extChartAt 𝓘(ℝ, E) initial).symm (S x).1 at hb
    rwa [hSbase x hx] at hb
  have hcurve (x : E) (hx : x ∈ closedBall x₀ ρ) : Γ x = Φ (S x) := by
    have hxs := hSlegal x hx
    have hΦsource : Φ (S x) 0 ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
      rw [hΦzero x hx]
      exact (extChartAt 𝓘(ℝ, E) initial).map_target (hBtarget (hρmap hx).1)
    have hΦp : eulerLagrangePhaseLift (F.chartEnergy initial)
        (extChartAt 𝓘(ℝ, E) initial ∘ Φ (S x)) 0 = p x := by
      rw [hF.chartMomentum_of_tangent_eq (hELΦ (S x) hxs 0 (mem_univ _))
        initial hxs (hi (S x) hxs), ← he]
      exact e.right_inv (hρmap hx).2.2
    exact complete_eq_of_initial_chart_momentum hF initial (hEL x (hρmap hx).1)
      (hELΦ (S x) hxs) (hsource x (hρmap hx).1) hΦsource
      ((hp x (hρmap hx).1).trans hΦp.symm)
  have hxρ : x₀ ∈ closedBall x₀ ρ := mem_closedBall_self hρ.le
  have hΦlegal : Φ (S x₀) s ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    rwa [← hcurve x₀ hxρ]
  have hread : ContDiffAt ℝ 2
      (fun q : (E × E) × ℝ ↦ extChartAt 𝓘(ℝ, E) terminal (Φ q.1 q.2))
      (S x₀, s) :=
    (hF.contDiffAt_chartMomentumFamily_of_tangentFamily
      (isOpen_chartEnergyDomain initial) hELΦ hΦ (hSlegal x₀ hxρ) terminal s hΦlegal).fst
  obtain ⟨D, W, hW, hWLip⟩ := (hread.of_le (by norm_num)).exists_lipschitzOnWith
  have hpos : ContinuousAt (fun q : (E × E) × ℝ ↦ Φ q.1 q.2) (S x₀, s) :=
    (contMDiffOn_positionFamily_of_tangentFamily hΦ).continuousOn.continuousAt
      (((isOpen_chartEnergyDomain initial).prod isOpen_univ).mem_nhds
        ⟨hSlegal x₀ hxρ, mem_univ _⟩)
  have hreadnear : W ∩ (fun q : (E × E) × ℝ ↦ Φ q.1 q.2) ⁻¹'
      (extChartAt 𝓘(ℝ, E) terminal).source ∈ 𝓝 (S x₀, s) :=
    inter_mem hW (hpos.preimage_mem_nhds
      ((isOpen_extChartAt_source terminal).mem_nhds hΦlegal))
  have hparamAt : ContinuousAt (fun q : E × ℝ ↦ (S q.1, q.2)) (x₀, s) := by
    have hf : ContinuousAt (fun q : E × ℝ ↦ S q.1) (x₀, s) :=
      ContinuousAt.comp (x := (x₀, s)) (f := fun q : E × ℝ ↦ q.1)
        (g := S) hSAt continuousAt_fst
    exact hf.prodMk continuousAt_snd
  obtain ⟨r, hr, hrmap⟩ := nhds_basis_closedBall.mem_iff.mp
    (inter_mem (prod_mem_nhds (closedBall_mem_nhds x₀ hρ) univ_mem)
      (hparamAt.preimage_mem_nhds hreadnear))
  have hsmall {q : E × ℝ} (hq : q ∈ closedBall (x₀, s) r) :
      q.1 ∈ closedBall x₀ ρ := (hrmap hq).1.1
  have hSLipJoint := hSLip.comp LipschitzWith.prod_fst.lipschitzOnWith
    (show MapsTo Prod.fst (closedBall (x₀, s) r) (closedBall x₀ ρ) from
      fun _ hq ↦ hsmall hq)
  have hh := hWLip.comp (hSLipJoint.prodMk LipschitzWith.prod_snd.lipschitzOnWith)
    (fun _ hq ↦ (hrmap hq).2.1)
  refine ⟨r, D * max (C * max 1 L * 1) 1, hr,
    fun _ hq ↦ ⟨(hρmap (hsmall hq)).1, mem_univ _⟩, ?_, ?_⟩
  · intro q hq
    change Γ q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) terminal).source
    rw [hcurve q.1 (hsmall hq)]
    exact (hrmap hq).2.2
  · intro q hq q' hq'
    simpa only [Function.comp_apply, hcurve q.1 (hsmall hq),
      hcurve q'.1 (hsmall hq')] using hh hq hq'

/-- The same complete original family with C1,1 initial covectors has a locally
Lipschitz position readout at every fixed finite time and every legal output chart.
Actual initial positions ensure chart legality; the flow identity and its parameter
regularity are proved from the original geometry, not assumed of the supplied family. -/
theorem exists_lipschitz_chart_readout_of_C11_initial_momentum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {B : Set E} (hB : IsOpen B)
    (hBtarget : B ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ B, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ B, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ B, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {x₀ : E} (hx₀ : x₀ ∈ B) (terminal : M) (s : ℝ)
    (hlegal : Γ x₀ s ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    ∃ (r : ℝ) (C : ℝ≥0), 0 < r ∧ closedBall x₀ r ⊆ B ∧
      MapsTo (fun x ↦ Γ x s) (closedBall x₀ r)
        (extChartAt 𝓘(ℝ, E) terminal).source ∧
      LipschitzOnWith C (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x s))
        (closedBall x₀ r) := by
  obtain ⟨r, C, hr, hsub, hmap, hread⟩ :=
    hF.exists_joint_lipschitz_chart_readout_of_C11_initial_momentum hcomplete initial
      hG hLip hB hBtarget hEL hinit hp hx₀ terminal s hlegal
  have hslice : MapsTo (fun x : E ↦ (x, s)) (closedBall x₀ r)
      (closedBall (x₀, s) r) := by
    intro x hx
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hx
  refine ⟨r, C, hr, fun _ hx ↦ (hsub (hslice hx)).1,
    fun _ hx ↦ hmap (hslice hx), ?_⟩
  simpa only [Function.comp_def, mul_one] using
    hread.comp (LipschitzWith.prodMk_right s).lipschitzOnWith hslice

/-- The actual complete family with C1,1 initial covectors is continuous in its seed
at any fixed finite time, in the original manifold topology. -/
theorem continuousOn_of_C11_initial_momentum (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {B : Set E} (hB : IsOpen B)
    (hBtarget : B ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ B, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ B, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ B, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    (s : ℝ) : ContinuousOn (fun x ↦ Γ x s) B := by
  intro x hx
  obtain ⟨r, C, hr, _, hmap, hread⟩ :=
    hF.exists_lipschitz_chart_readout_of_C11_initial_momentum hcomplete initial hG hLip
      hB hBtarget hEL hinit hp hx (Γ x s) s (mem_extChartAt_source (Γ x s))
  have hc : ContinuousAt (fun y ↦ extChartAt 𝓘(ℝ, E) (Γ x s) (Γ y s)) x :=
    (hread.continuousOn x (mem_closedBall_self hr.le)).continuousAt
      (closedBall_mem_nhds x hr)
  have hi : ContinuousAt (extChartAt 𝓘(ℝ, E) (Γ x s)).symm
      (extChartAt 𝓘(ℝ, E) (Γ x s) (Γ x s)) :=
    (continuousOn_extChartAt_symm (Γ x s)).continuousAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (Γ x s)).mem_nhds
        ((extChartAt 𝓘(ℝ, E) (Γ x s)).map_source (mem_extChartAt_source (Γ x s))))
  have heq : (fun y ↦ Γ y s) =ᶠ[𝓝 x]
      (fun y ↦ (extChartAt 𝓘(ℝ, E) (Γ x s)).symm
        (extChartAt 𝓘(ℝ, E) (Γ x s) (Γ y s))) := by
    filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact ((extChartAt 𝓘(ℝ, E) (Γ x s)).left_inv (hmap hy)).symm
  have hback := ContinuousAt.comp
    (f := fun y : E ↦ extChartAt 𝓘(ℝ, E) (Γ x s) (Γ y s)) hi hc
  exact (hback.congr_of_eventuallyEq heq).continuousWithinAt

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
