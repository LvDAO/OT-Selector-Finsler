import OTSelector.Analysis.Calculus.ShortTimeLipschitz
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.C11ShortTranslation

* **Conditions:** A C1,1 potential covector field on a coordinate ball and the actual smooth local Legendre inverse/complete flow.
* **Objects:** Actual short complete geodesic translations whose coordinate displacement from identity is at most half-Lipschitz.
* **Proof detail:** Compose the Lipschitz covector field with the true inverse and smooth flow; use uniform small-time derivative bounds without second-differentiating the potential.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11ShortTranslation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11ShortTranslation`; the selected original proof blocks follow. -/
section

/-!
# Actual short-time geodesic translations from a C1,1 potential

The original local Legendre inverse converts the actual potential differential into
initial tangent states. The original complete tangent family then constructs genuine
complete geodesics. Their short-time position displacement has Lipschitz constant at
most one half on a coordinate ball, without differentiating the potential twice.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Actual C1,1 covectors construct complete original geodesics whose short-time coordinate
readout is jointly Lipschitz and whose spatial displacement is one-half-Lipschitz. -/
theorem exists_C11_short_geodesic_translation_lipschitz (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G)) {z₀ : E × E}
    (hz₀ : z₀ ∈ chartEnergyDomain old)
    (hp : fiberLegendre (F.chartEnergy old) z₀ = fderiv ℝ G z₀.1) :
    ∃ (r τ : ℝ) (Γ : E → ℝ → M), 0 < r ∧ 0 < τ ∧
      closedBall z₀.1 r ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      (∀ x ∈ closedBall z₀.1 r,
        Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x ∧
        F.IsEulerLagrangeOn (Γ x) univ ∧
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Γ x) ∧
        F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x)) ∧
      ContinuousOn (fun q : ℝ × E ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1))
        (Icc (-τ) τ ×ˢ closedBall z₀.1 r) ∧
      (∃ C : ℝ≥0, LipschitzOnWith C
        (fun q : ℝ × E ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1))
        (Icc (-τ) τ ×ˢ closedBall z₀.1 r)) ∧
      ∀ t ∈ Icc (-τ) τ,
        MapsTo (fun x ↦ Γ x t) (closedBall z₀.1 r) (extChartAt 𝓘(ℝ, E) old).source ∧
        LipschitzOnWith (1 / 2) (fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t) - x)
          (closedBall z₀.1 r) := by
  obtain ⟨e, he, hzs, hzt, hsub, _, hInv, hbase, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse old hz₀
  let p : E → E × (E →L[ℝ] ℝ) := fun x ↦ (x, fderiv ℝ G x)
  let S : E → E × E := fun x ↦ e.symm (p x)
  have hp₀ : p z₀.1 = parametricLegendre (F.chartEnergy old) z₀ :=
    Prod.ext rfl hp.symm
  have hpcont : Continuous p := continuous_id.prodMk (hG.continuous_fderiv one_ne_zero)
  have hpLip : LipschitzWith (max 1 L) p := LipschitzWith.id.prodMk hLip
  have hp₀mem : p z₀.1 ∈ e.target := hp₀ ▸ hzt
  have hS₀ : S z₀.1 = z₀ := by
    change e.symm (p z₀.1) = z₀
    rw [hp₀, ← he]
    exact e.left_inv hzs
  obtain ⟨C, V, hV, hVLip⟩ :=
    ((hInv.contDiffAt (e.open_target.mem_nhds hp₀mem)).of_le (by simp)).exists_lipschitzOnWith
  have hnear : p ⁻¹' (V ∩ e.target) ∈ 𝓝 z₀.1 :=
    hpcont.continuousAt.preimage_mem_nhds (inter_mem hV (e.open_target.mem_nhds hp₀mem))
  obtain ⟨ρ, hρ, hρmap⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  have hSLip : LipschitzOnWith (C * max 1 L) S (closedBall z₀.1 ρ) :=
    hVLip.comp hpLip.lipschitzOnWith (fun x hx ↦ (hρmap hx).1)
  have hScont : ContinuousWithinAt S (closedBall z₀.1 ρ) z₀.1 :=
    hSLip.continuousOn z₀.1 (mem_closedBall_self hρ.le)
  have hSAt : ContinuousAt S z₀.1 :=
    hScont.continuousAt (closedBall_mem_nhds _ hρ)
  have hSlegal (x : E) (hx : x ∈ closedBall z₀.1 ρ) :
      S x ∈ chartEnergyDomain old := hsub (e.map_target (hρmap hx).2)
  have hSbase (x : E) (hx : x ∈ closedBall z₀.1 ρ) : (S x).1 = x :=
    hbase (p x) (hρmap hx).2
  obtain ⟨Φ, hEL, hi, hΦ⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old 0
  have hinitial (z : E × E) (hz : z ∈ chartEnergyDomain old) :
      Φ z 0 = (extChartAt 𝓘(ℝ, E) old).symm z.1 := by
    have hb := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hi z hz)
    rw [tangentChart_symm_eq old hz.1 z.2] at hb
    exact hb
  let O := (chartEnergyDomain old ×ˢ (univ : Set ℝ)) ∩
    (fun q : (E × E) × ℝ ↦ Φ q.1 q.2) ⁻¹' (extChartAt 𝓘(ℝ, E) old).source
  have hO : IsOpen O :=
    (contMDiffOn_positionFamily_of_tangentFamily hΦ).continuousOn.isOpen_inter_preimage
      ((isOpen_chartEnergyDomain old).prod isOpen_univ) (isOpen_extChartAt_source old)
  have hO₀ : (z₀, (0 : ℝ)) ∈ O := by
    refine ⟨⟨hz₀, mem_univ _⟩, ?_⟩
    change Φ z₀ 0 ∈ (extChartAt 𝓘(ℝ, E) old).source
    rw [hinitial z₀ hz₀]
    exact (extChartAt 𝓘(ℝ, E) old).map_target hz₀.1
  let Ψ : (E × E) × ℝ → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Φ q.1 q.2)
  have hΨ : ContDiffOn ℝ 2 Ψ O :=
    (hF.contDiffOn_chartPhase_of_tangentFamily_C2 old
      (fun q hq ↦ hEL q.1 hq.1.1 q.2 (mem_univ _))
      (hΦ.mono inter_subset_left) (fun _ hq ↦ hq.2)).fst
  have hzero : ∀ᶠ z in 𝓝 z₀, Ψ (z, 0) = (ContinuousLinearMap.fst ℝ E E) z := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz₀] with z hz
    change extChartAt 𝓘(ℝ, E) old (Φ z 0) = z.1
    rw [hinitial z hz]
    exact (extChartAt 𝓘(ℝ, E) old).right_inv hz.1
  let Cₛ : ℝ≥0 := C * max 1 L
  let ε : ℝ≥0 := (2 * (Cₛ + 1))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R, τ, hR, hτ, hbox, hres⟩ :=
    exists_shortTime_lipschitz_of_initial_linear hO (hΨ.of_le (by norm_num)) hO₀
      (ContinuousLinearMap.fst ℝ E E) hzero ε hε
  obtain ⟨CΨ, hΨLip⟩ := (hΨ.mono hbox).exists_lipschitzOnWith (by norm_num)
    ((convex_closedBall z₀ R).prod (convex_Icc (-τ) τ))
    ((isCompact_closedBall z₀ R).prod isCompact_Icc)
  have hSball : S ⁻¹' ball z₀ R ∈ 𝓝 z₀.1 := by
    apply hSAt.preimage_mem_nhds
    rw [hS₀]
    exact ball_mem_nhds _ hR
  obtain ⟨r, hr, hrsub⟩ := nhds_basis_closedBall.mem_iff.mp
    (inter_mem (closedBall_mem_nhds z₀.1 hρ) hSball)
  have hsmall : closedBall z₀.1 r ⊆ closedBall z₀.1 ρ :=
    fun _ hx ↦ (hrsub hx).1
  have hSmap : MapsTo S (closedBall z₀.1 r) (closedBall z₀ R) :=
    fun _ hx ↦ ball_subset_closedBall (hrsub hx).2
  let Γ : E → ℝ → M := fun x ↦ Φ (S x)
  have hparam : ∀ q ∈ Icc (-τ) τ ×ˢ closedBall z₀.1 r, (S q.2, q.1) ∈ O :=
    fun _ hq ↦ hbox ⟨hSmap hq.2, hq.1⟩
  refine ⟨r, τ, Γ, hr, hτ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hSbase x (hsmall hx)]
    exact (hSlegal x (hsmall hx)).1
  · intro x hx
    have hs := hSlegal x (hsmall hx)
    refine ⟨(hinitial (S x) hs).trans (congrArg _ (hSbase x (hsmall hx))),
      hEL (S x) hs, ?_, ?_⟩
    · exact contMDiffOn_univ.mp (hF.contMDiffOn_of_isEulerLagrangeOn (hEL (S x) hs))
    · change eulerLagrangePhaseLift (F.chartEnergy old)
        (extChartAt 𝓘(ℝ, E) old ∘ Φ (S x)) 0 = p x
      rw [hF.chartMomentum_of_tangent_eq (hEL (S x) hs 0 (mem_univ _)) old hs
        (hi (S x) hs), ← he]
      exact e.right_inv (hρmap (hsmall hx)).2
  · exact hΨ.continuousOn.comp
      (((hSLip.mono hsmall).continuousOn.comp continuous_snd.continuousOn
        (fun _ hq ↦ hq.2)).prodMk continuous_fst.continuousOn) hparam
  · have hSjoint := (hSLip.mono hsmall).comp
      (LipschitzWith.prod_snd.lipschitzOnWith)
      (show MapsTo Prod.snd (Icc (-τ) τ ×ˢ closedBall z₀.1 r)
        (closedBall z₀.1 r) from fun _ hq ↦ hq.2)
    exact ⟨_, hΨLip.comp (hSjoint.prodMk LipschitzWith.prod_fst.lipschitzOnWith)
      (fun _ hq ↦ ⟨hSmap hq.2, hq.1⟩)⟩
  · intro t ht
    refine ⟨fun x hx ↦ (hparam (t, x) ⟨ht, hx⟩).2, ?_⟩
    have hcomp := (hres t ht).comp (hSLip.mono hsmall) hSmap
    have hC : ε * Cₛ ≤ (1 / 2 : ℝ≥0) := by
      dsimp [ε]
      rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      simp only [one_mul]
      calc
        Cₛ * 2 = 2 * Cₛ := mul_comm _ _
        _ ≤ 2 * (Cₛ + 1) := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right zero_le_one) (by norm_num)
    have hw := hcomp.weaken hC
    intro x hx y hy
    have hh := hw hx hy
    change edist (Ψ (S x, t) - (S x).1) (Ψ (S y, t) - (S y).1) ≤ _ at hh
    simpa only [hSbase x (hsmall hx), hSbase y (hsmall hy)] using hh

/-- Actual C1,1 initial covectors construct complete original geodesics whose coordinate
translations differ from the identity by a one-half-Lipschitz map for all small times.
All initial positions, original momenta, and chart membership are derived. -/
theorem exists_C11_short_geodesic_translation (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G)) {z₀ : E × E}
    (hz₀ : z₀ ∈ chartEnergyDomain old)
    (hp : fiberLegendre (F.chartEnergy old) z₀ = fderiv ℝ G z₀.1) :
    ∃ (r τ : ℝ) (Γ : E → ℝ → M), 0 < r ∧ 0 < τ ∧
      closedBall z₀.1 r ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      (∀ x ∈ closedBall z₀.1 r,
        Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x ∧
        F.IsEulerLagrangeOn (Γ x) univ ∧
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Γ x) ∧
        F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x)) ∧
      ContinuousOn (fun q : ℝ × E ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1))
        (Icc (-τ) τ ×ˢ closedBall z₀.1 r) ∧
      ∀ t ∈ Icc (-τ) τ,
        MapsTo (fun x ↦ Γ x t) (closedBall z₀.1 r) (extChartAt 𝓘(ℝ, E) old).source ∧
        LipschitzOnWith (1 / 2) (fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t) - x)
          (closedBall z₀.1 r) := by
  obtain ⟨r, τ, Γ, hr, hτ, hball, hinit, hcont, _, hflow⟩ :=
    hF.exists_C11_short_geodesic_translation_lipschitz hcomplete old hG hLip hz₀ hp
  exact ⟨r, τ, Γ, hr, hτ, hball, hinit, hcont, hflow⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
