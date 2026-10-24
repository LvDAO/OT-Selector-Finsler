import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteTangentSmooth
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Finsler.TubeCoordinateEnergy
import OTSelector.Geometry.Finsler.TubeCoordinateFamily
import OTSelector.Geometry.Finsler.TubeCoordinateInitial
import OTSelector.Geometry.Finsler.TubeCoordinateKernel
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.TubeCoordinateEndpoint

* **Conditions:** The actual initial-state family, genuine inverse tube and calibrated central tube with the stated unit/normal identities.
* **Objects:** Invertibility of the original endpoint differential, including different initial and terminal old charts.
* **Proof detail:** Transfer zero endpoint derivatives through the genuine inverse tube, apply its endpoint-fixed kernel theorem and recover zero initial state by actual initial-rank injectivity.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (derived): No independent endpoint nonconjugacy premise is used in the calibrated-tube conclusion.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateEndpoint.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateEndpoint`; the selected original proof blocks follow. -/
section

/-!
# Invertibility of the original endpoint map through a genuine tube

The genuine inverse tube and the actual chart inverse transfer endpoint kernels by
manifold differentiation. The actual initial tangent identity transfers the initial
phase kernel back to the original initial-state parameter. No endpoint or coordinate
rank premise is supplied, and the initial and terminal charts may be different.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E V W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem inverseTube_position_fderiv_eq_zero_of_chart
    {Y : OpenPartialHomeomorph V M}
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {γ : W → M} {w : W} (hγ : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) γ w)
    (hx : γ w ∈ Y.target) (old : M)
    (ho : γ w ∈ (extChartAt 𝓘(ℝ, E) old).source) {ξ : W}
    (hz : fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w ξ = 0) :
    fderiv ℝ (Y.symm ∘ γ) w ξ = 0 := by
  have hχ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) old) (γ w) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using ho)
  have hdχ := mfderiv_comp w hχ hγ
  rw [mfderiv_eq_fderiv] at hdχ
  rw [hdχ] at hz
  obtain ⟨e, he⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) ho
  have hv : mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) γ w ξ = 0 := by
    apply e.injective
    change e.toContinuousLinearMap _ = e.toContinuousLinearMap _
    rw [he]
    exact hz.trans (_root_.map_zero _).symm
  have hd := mfderiv_comp w
    ((hi.contMDiffAt (Y.open_target.mem_nhds hx)).mdifferentiableAt (by simp)) hγ
  rw [mfderiv_eq_fderiv] at hd
  rw [hd]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) Y.symm (γ w)
    (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) γ w ξ) = 0
  rw [hv, _root_.map_zero]

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

private theorem tubeMomentum_fderiv_fst_eq
    (hF : F.IsSmoothStronglyConvex) {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (t : ℝ) (hx : Γ w t ∈ Y.target) (ξ : W) :
    (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w ξ).1 =
      fderiv ℝ (Y.symm ∘ (fun v ↦ Γ v t)) w ξ := by
  let D := (B ×ˢ (univ : Set ℝ)) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹' Y.target
  have hc : ContinuousOn (fun q : W × ℝ ↦ Γ q.1 q.2) (B ×ˢ univ) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn hG.continuousOn
  have hD : IsOpen D := hc.isOpen_inter_preimage (hB.prod isOpen_univ) Y.open_target
  have hq : (w, t) ∈ D := ⟨⟨hw, mem_univ _⟩, hx⟩
  have hp := ((hF.contDiffOn_tubeCoordinateMomentumFamily hY hi hD
    (hG.mono inter_subset_left) (fun _ h ↦ h.2)
    (fun q h ↦ hEL q.1 h.1.1 q.2 (mem_univ _))).contDiffAt (hD.mem_nhds hq)).comp w
      (contDiffAt_id.prodMk contDiffAt_const)
  have hd := (hp.differentiableAt (by norm_num)).hasFDerivAt.fst
  have hf : fderiv ℝ (Y.symm ∘ (fun v ↦ Γ v t)) w =
      (ContinuousLinearMap.fst ℝ V (V →L[ℝ] ℝ)).comp
        (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w) := hd.fderiv
  rw [hf]
  rfl


/-- The actual original endpoint differential is invertible whenever the genuine tube
energy has zero base Hessian columns along the given central segment. The original
initial tangent identity and actual chart derivatives supply all rank identifications. -/
theorem isInvertible_chartEndpointMap_of_tube_hessian_base_zero
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) (initial terminal : M)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {a b : ℝ} (hab : a < b) {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain initial ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain initial)
    (hx : ∀ t ∈ Icc a b, Γ z t ∈ Y.target)
    (hterminal : Γ z b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hzero : ∀ t ∈ Icc a b, ∀ u : V,
      fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y))
        (tubeCoordinateTangentFamily Y Γ (z, t)) (u, 0) = 0) :
    (fderiv ℝ (chartEndpointMap terminal Γ b) z).IsInvertible := by
  have hB := isOpen_chartEnergyDomain (E := E) initial
  have hza : Γ z a ∈ Y.target := hx a (left_mem_Icc.mpr hab.le)
  have hzb : Γ z b ∈ Y.target := hx b (right_mem_Icc.mpr hab.le)
  have hpos (t : ℝ) :
      MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun v ↦ Γ v t) z := by
    have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
      ((hB.prod isOpen_univ).mem_nhds
        (show (z, t) ∈ chartEnergyDomain initial ×ˢ univ from ⟨hz, mem_univ _⟩))
    have hs := hp.comp z ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)
    exact hs.mdifferentiableAt (by norm_num)
  have hχ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) terminal) (Γ z b) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hterminal)
  have hd : DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) terminal ∘ (fun v ↦ Γ v b)) z :=
    (hχ.comp z (hpos b)).differentiableAt
  have hDP : HasFDerivAt (chartEndpointMap terminal Γ b)
      ((ContinuousLinearMap.fst ℝ E E).prod
        (fderiv ℝ (extChartAt 𝓘(ℝ, E) terminal ∘ (fun v ↦ Γ v b)) z)) z :=
    hasFDerivAt_fst.prodMk hd.hasFDerivAt
  have hinitial : Γ z a ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    have hb := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit z hz)
    rw [tangentChart_symm_eq initial hz.1 z.2] at hb
    change Γ z a = (extChartAt 𝓘(ℝ, E) initial).symm z.1 at hb
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target hz.1
  have hstart : (extChartAt 𝓘(ℝ, E) initial ∘ (fun v ↦ Γ v a)) =ᶠ[𝓝 z]
      (fun v : E × E ↦ v.1) := by
    filter_upwards [hB.mem_nhds hz] with v hv
    exact congrArg Prod.fst (hF.chartPhase_of_tangent_eq
      (hEL v hv a (mem_univ _)) initial hv (hinit v hv))
  have hinj : Function.Injective (fderiv ℝ (chartEndpointMap terminal Γ b) z) := by
    apply (injective_iff_map_eq_zero _).2
    intro ξ hξ
    rw [hDP.fderiv] at hξ
    have hfirst : ξ.1 = 0 := congrArg Prod.fst hξ
    have hlast : fderiv ℝ
        (extChartAt 𝓘(ℝ, E) terminal ∘ (fun v ↦ Γ v b)) z ξ = 0 :=
      congrArg Prod.snd hξ
    have ha : (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, a)) z ξ).1 = 0 := by
      rw [tubeMomentum_fderiv_fst_eq hF hY hi hB hEL hG hz a hza ξ]
      apply inverseTube_position_fderiv_eq_zero_of_chart hi (hpos a) hza initial hinitial
      rw [hstart.fderiv_eq, fderiv_fst]
      exact hfirst
    have hb : (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, b)) z ξ).1 = 0 := by
      rw [tubeMomentum_fderiv_fst_eq hF hY hi hB hEL hG hz b hzb ξ]
      exact inverseTube_position_fderiv_eq_zero_of_chart hi (hpos b) hzb terminal
        hterminal hlast
    have hphase := hF.tubeCoordinateMomentumFamily_endpoint_kernel_eq_zero
      hY hi hB hEL hG hz hab hx hzero ha hb
    exact (hF.injective_fderiv_initial_tubeCoordinateMomentumFamily initial a
      hY hi hEL hinit hG hz hza) (hphase.trans (_root_.map_zero _).symm)
  exact ⟨(LinearEquiv.ofBijective
    (fderiv ℝ (chartEndpointMap terminal Γ b) z).toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv, rfl⟩


/-- A genuine calibrated unit-speed tube makes the original full endpoint differential
invertible. Actual initial tangent matching identifies the central geodesic by uniqueness;
the coordinate velocity, Hessian blocks, initial rank and terminal rank are all derived. -/
theorem isInvertible_chartEndpointMap_of_calibrated_manifoldTube
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] [T2Space M]
    (hF : F.IsSmoothStronglyConvex) (initial terminal : M)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {z : E × E} (hz : z ∈ chartEnergyDomain initial) {w : W}
    (hΛ : F.IsEulerLagrangeOn (Λ w) univ)
    (hseed : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ w) ⟨a, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (hterminal : Λ w b ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    (fderiv ℝ (chartEndpointMap terminal Γ b) z).IsInvertible := by
  have hsame : Γ z = Λ w := by
    funext t
    exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
      (hEL z hz) hΛ (mem_univ a) ((hinit z hz).trans hseed.symm) (mem_univ t)
  have hYval (t : ℝ) : Y (t, w) = Λ w t := congrFun heq (t, w)
  have hx (t : ℝ) (ht : t ∈ Icc a b) : Γ z t ∈ Y.target := by
    rw [hsame, ← hYval]
    exact Y.map_source (hstay t ht)
  have hphase (t : ℝ) (ht : t ∈ Icc a b) :
      tubeCoordinateTangentFamily Y Γ (z, t) = ((t, w), (1, 0)) := by
    have hn : (fun r : ℝ ↦ (r, w)) ⁻¹' Y.source ∈ 𝓝 t :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
        (Y.open_source.mem_nhds (hstay t ht))
    have he : (Y.symm ∘ Γ z) =ᶠ[𝓝 t] (fun r ↦ (r, w)) := by
      filter_upwards [hn] with r hr
      change Y.symm (Γ z r) = (r, w)
      rw [hsame, ← hYval]
      exact Y.left_inv hr
    change ((Y.symm ∘ Γ z) t, deriv (Y.symm ∘ Γ z) t) = _
    rw [he.eq_of_nhds, he.deriv_eq]
    congr 1
    exact (hasDerivAt_id t |>.prodMk (hasDerivAt_const t w)).deriv
  have hG := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth initial
    (isOpen_chartEnergyDomain initial) hEL contDiffOn_id (fun _ h ↦ h) hinit).1
  apply hF.isInvertible_chartEndpointMap_of_tube_hessian_base_zero initial terminal
    hY hi hab hEL hinit (hG.of_le (by simp)) hz hx (by simpa only [hsame] using hterminal)
  intro t ht u
  rw [hphase t ht]
  exact (hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀ heq hhalf hbound
    (hstay t ht)).2.2.2.2.2.2.1 u

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
