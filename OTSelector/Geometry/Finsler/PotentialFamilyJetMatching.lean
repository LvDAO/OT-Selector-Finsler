import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Analysis.Calculus.MixedFlowJetMatching
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Geometry.Finsler.PotentialFamilyJetMatching

* **Conditions:** A given actual complete potential-level family and the original within-core covector jet matching its true initial phase.
* **Objects:** Actual rough trajectories whose within-core momentum derivative equals the ordinary derivative of that given family at every legal time.
* **Proof detail:** Represent both initial seeds in one actual complete tangent flow, identify the smooth seed composite by initial tangent uniqueness and apply the mixed chain rule.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The ordinary derivative is constructed first; no uniqueness of derivatives on a possibly thin allowed parameter set is assumed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialFamilyJetMatching.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialFamilyJetMatching`; the selected original proof blocks follow. -/
section

/-!
# Original rough covectors and a given complete potential-level family

The original within-core covector jet is transported by one actual complete tangent
family. The smooth normal seeds are identified with the given level family using their
actual initial tangents. Its ordinary parameter derivative is constructed before it is
compared with the rough within-set derivative; no uniqueness of derivatives on the
allowed parameter set is needed.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ContinuousFinslerNorm E M}

/-- The actual rough covector seed on a core constructs complete trajectories with the
same central curve and the same parameter first jet as the given potential-level
family. The normal derivative is an ordinary derivative, whereas the original rough
covector is differentiated only on the original allowed core. All initial data and
Legendre identities belong to the same supplied level family and inverse branch. -/
theorem exists_complete_family_matching_potentialLevel_jet (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ)
    {K : Set E} {x : E} {f : E → ℝ} {p : E →L[ℝ] ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} (hxK : x ∈ K)
    (hfirst : HasFDerivAt f p x)
    (hwithin : HasFDerivWithinAt (fderiv ℝ f) H K x)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ e.symm e.target) (hp : (x, p) ∈ e.target)
    {B : Set W} {σ v : W → E} {Γ : W → ℝ → M} {J : W →L[ℝ] E}
    (hB : IsOpen B) (h0 : (0 : W) ∈ B) (hσ0 : σ 0 = x)
    (hσ : HasFDerivAt σ J 0) (hv : ContinuousAt v 0)
    (hseed0 : (σ 0, v 0) = e.symm (x, p))
    (hstate : ∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain old)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hinit : ∀ w ∈ B, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σ w, v w))
    (hjet : HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, t₀))
      (J.prod (H.comp J)) 0) :
    let S := σ ⁻¹' K
    let R := fun w ↦ (σ w, fderiv ℝ f (σ w))
    ∃ Ψ : W → ℝ → M, Ψ 0 = Γ 0 ∧
      (∀ᶠ w in 𝓝[S] 0, R w ∈ e.target ∧
        F.IsEulerLagrangeOn (Ψ w) univ ∧
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Ψ w) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (e.symm (R w))) ∧
      ∀ (chart : M) (r : ℝ), Γ 0 r ∈ (extChartAt 𝓘(ℝ, E) chart).source →
        HasFDerivWithinAt (fun w ↦ F.chartMomentumFamily chart Ψ (w, r))
          (fderiv ℝ (fun w ↦ F.chartMomentumFamily chart Γ (w, r)) 0) S 0 := by
  let S := σ ⁻¹' K
  let R := fun w ↦ (σ w, fderiv ℝ f (σ w))
  let Q := fun w ↦ F.chartMomentumFamily old Γ (w, t₀)
  let Y := fun w ↦ (σ w, v w)
  let D := J.prod (H.comp J)
  have hR0 : R 0 = (x, p) := by simp only [R, hσ0, hfirst.fderiv]
  have hY0 : Y 0 ∈ e.source := by
    rw [show Y 0 = e.symm (x, p) from hseed0]
    exact e.map_target hp
  have hYS : ∀ᶠ w in 𝓝 0, Y w ∈ e.source :=
    (hσ.continuousAt.prodMk hv) (e.open_source.mem_nhds hY0)
  have hQY : ∀ᶠ w in 𝓝 0, Q w = e (Y w) := by
    filter_upwards [hB.mem_nhds h0] with w hw
    exact (hF.chartMomentum_of_tangent_eq (hEL w hw t₀ (mem_univ _)) old
      (hstate w hw) (hinit w hw)).trans (congrFun he (Y w)).symm
  have hQ0 : Q 0 = (x, p) := by
    rw [hQY.self_of_nhds, show Y 0 = e.symm (x, p) from hseed0]
    exact e.right_inv hp
  have hYQ : (fun w ↦ e.symm (Q w)) =ᶠ[𝓝 0] Y := by
    filter_upwards [hYS, hQY] with w hw hq
    rw [hq, e.left_inv hw]
  have hR : HasFDerivWithinAt R D S 0 := by
    have hcov : HasFDerivWithinAt (fderiv ℝ f) H K (σ 0) := hσ0.symm ▸ hwithin
    exact hσ.hasFDerivWithinAt.prodMk
      (hcov.comp 0 hσ.hasFDerivWithinAt (fun _ hw ↦ hw))
  have hRtarget : ∀ᶠ w in 𝓝[S] 0, R w ∈ e.target :=
    hR.continuousWithinAt (by simpa only [hR0] using e.open_target.mem_nhds hp)
  have hRlegal0 : e.symm (R 0) ∈ chartEnergyDomain old :=
    hsub (e.map_target (hRtarget.self_of_nhdsWithin (show (0 : W) ∈ S by
      change σ 0 ∈ K
      rwa [hσ0])))
  have hE : HasFDerivAt e.symm (fderiv ℝ e.symm (x, p)) (x, p) :=
    ((hInv.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hRX : HasFDerivWithinAt (fun w ↦ e.symm (R w))
      ((fderiv ℝ e.symm (x, p)).comp D) S 0 :=
    (show HasFDerivAt e.symm (fderiv ℝ e.symm (x, p)) (R 0) by rw [hR0]; exact hE)
      |>.comp_hasFDerivWithinAt 0 hR
  have hQX : HasFDerivAt (fun w ↦ e.symm (Q w))
      ((fderiv ℝ e.symm (x, p)).comp D) 0 :=
    (show HasFDerivAt e.symm (fderiv ℝ e.symm (x, p)) (Q 0) by rw [hQ0]; exact hE)
      |>.comp 0 hjet
  obtain ⟨Φ, hΦEL, hΦinit, hΦG⟩ :=
    hF.exists_complete_tangentFamily_C2 hcomplete old t₀
  let Ψ : W → ℝ → M := fun w ↦ Φ (e.symm (R w))
  have hnormal : (fun w ↦ Φ (e.symm (Q w))) =ᶠ[𝓝 0] Γ := by
    filter_upwards [hB.mem_nhds h0, hYQ] with w hw hy
    rw [hy]
    funext t
    exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
      (hΦEL (Y w) (hstate w hw)) (hEL w hw) (mem_univ t₀)
      ((hΦinit (Y w) (hstate w hw)).trans (hinit w hw).symm) (mem_univ t)
  have hcenter : Ψ 0 = Γ 0 := by
    change Φ (e.symm (R 0)) = Γ 0
    rw [hR0, ← hQ0]
    exact hnormal.self_of_nhds
  refine ⟨Ψ, hcenter, ?_, ?_⟩
  · filter_upwards [hRtarget] with w hw
    exact ⟨hw, hΦEL _ (hsub (e.map_target hw)), hΦinit _ (hsub (e.map_target hw))⟩
  · intro chart r hr
    have hsource : Φ (e.symm (R 0)) r ∈ (extChartAt 𝓘(ℝ, E) chart).source := by
      change Ψ 0 r ∈ _
      rw [hcenter]
      exact hr
    have hread := hF.contDiffAt_chartMomentumFamily_of_tangentFamily
      (isOpen_chartEnergyDomain old) hΦEL hΦG hRlegal0 chart r hsource
    have hmixed := flow_comp_sub_clock_same_firstJet_mixed
      (Φ := F.chartMomentumFamily chart Φ) (f := fun _ ↦ (0 : ℝ))
      (g := fun _ ↦ (0 : ℝ)) r hRX hQX
      ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : W)).hasFDerivWithinAt)
      (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : W))
      (show e.symm (R 0) = e.symm (Q 0) by rw [hR0, hQ0]) rfl
      (show DifferentiableAt ℝ (F.chartMomentumFamily chart Φ)
          (e.symm (Q 0), r - (0 : ℝ)) by
        simpa only [hR0, hQ0, sub_zero] using hread.differentiableAt (by norm_num))
    have heq : (fun w ↦ F.chartMomentumFamily chart Φ (e.symm (Q w), r)) =ᶠ[𝓝 0]
        (fun w ↦ F.chartMomentumFamily chart Γ (w, r)) := by
      filter_upwards [hnormal] with w hw
      simp only [ContinuousFinslerNorm.chartMomentumFamily, hw]
    have hrough : HasFDerivWithinAt
        (fun w ↦ F.chartMomentumFamily chart Φ (e.symm (R w), r))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily chart Φ (e.symm (Q w), r)) 0) S 0 := by
      simpa only [sub_zero] using hmixed.2.2
    rw [heq.fderiv_eq] at hrough
    simpa only [ContinuousFinslerNorm.chartMomentumFamily, Ψ] using hrough

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
