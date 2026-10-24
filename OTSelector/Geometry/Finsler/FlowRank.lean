import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.TangentChartCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFlowRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFlowRank`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.FlowRank

* **Conditions:** A complete intrinsic Finsler tangent family with its actual initial tangent identity and C2 dependence; an immersed seed for the seeded rank corollary.
* **Objects:** Invertibility of the full initial-phase derivative at every legal final chart and injectivity for actual seeded families.
* **Proof detail:** Start the same dynamics backwards from the final time, identify the local inverse by solution uniqueness and differentiate its identity.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Rank of the actual complete Finsler phase flow

Complete-solution uniqueness supplies a local inverse obtained by starting the same
intrinsic dynamics at the final time. Differentiating that actual inverse identity
proves invertibility of the full initial-phase derivative.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private abbrev actualTangent (c : ℝ → M) (t : ℝ) : TangentBundle 𝓘(ℝ, E) M :=
  tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩

private abbrev phaseChart (old : M) :=
  extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)

private theorem phaseChart_source (old : M) (v : TangentBundle 𝓘(ℝ, E) M) :
    v ∈ (phaseChart (E := E) old).source ↔
      v.1 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
  simp only [phaseChart, FiberBundle.chartedSpace_chartAt, mfld_simps]

private theorem invertible_fderiv_of_local_left_inverse [FiniteDimensional ℝ E]
    {f g : E → E} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g (f x)) (hleft : g ∘ f =ᶠ[𝓝 x] id) :
    (fderiv ℝ f x).IsInvertible := by
  have hd : (fderiv ℝ g (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E :=
    (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv.symm.trans
      (hleft.fderiv_eq.trans fderiv_id)
  have hi : Function.Injective (fderiv ℝ f x) := by
    intro u v huv
    have hu := congrArg (fun A : E →L[ℝ] E ↦ A u) hd
    have hv := congrArg (fun A : E →L[ℝ] E ↦ A v) hd
    exact hu.symm.trans ((congrArg (fderiv ℝ g (f x)) huv).trans hv)
  let d := (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  exact ⟨d, rfl⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

private theorem phaseChart_actualTangent_mem (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hsource : actualTangent (E := E) c t ∈ (phaseChart (E := E) old).source) :
    phaseChart (E := E) old (actualTangent (E := E) c t) ∈ chartEnergyDomain old := by
  have hs : c t ∈ (extChartAt 𝓘(ℝ, E) old).source :=
    (phaseChart_source old _).mp hsource
  obtain ⟨J, hJ, ht, hm, hx, hphase, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc old hs
  have heq : c =ᶠ[𝓝 t] (extChartAt 𝓘(ℝ, E) old).symm ∘
      (extChartAt 𝓘(ℝ, E) old ∘ c) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hm hs)).symm
  have htan : actualTangent (E := E) c t =
      actualTangent (E := E) ((extChartAt 𝓘(ℝ, E) old).symm ∘
        (extChartAt 𝓘(ℝ, E) old ∘ c)) t := by
    refine TotalSpace.ext heq.eq_of_nhds ?_
    rw [actualTangent, tangentMap, heq.eq_of_nhds, actualTangent, tangentMap, heq.mfderiv_eq]
  have hp := tangentMap_chart_symm_curve old (hphase t ht).1
    (((hx.contDiffAt (hJ.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt)
  have he := htan.trans hp
  rw [he, (phaseChart (E := E) old).right_inv]
  · exact hphase t ht
  · rw [tangentChart_target]
    exact ⟨(hphase t ht).1, mem_univ _⟩

omit [FiniteDimensional ℝ E] in
private theorem contDiffAt_chartPhaseSlice
    {Γ : (E × E) → ℝ → M} {B : Set (E × E)} (hB : IsOpen B)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ actualTangent (E := E) (Γ q.1) q.2) (B ×ˢ univ))
    {z : E × E} (hz : z ∈ B) (new : M) (t : ℝ)
    (hx : actualTangent (E := E) (Γ z) t ∈ (phaseChart (E := E) new).source) :
    ContDiffAt ℝ 2 (fun w ↦ phaseChart (E := E) new
      (actualTangent (E := E) (Γ w) t)) z := by
  have hslice := (hG.contMDiffAt ((hB.prod isOpen_univ).mem_nhds ⟨hz, mem_univ t⟩)).comp z
    ((contDiffAt_id.prodMk (contDiffAt_const (c := t))).contMDiffAt)
  have hchart : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E × E) 2
      (phaseChart (E := E) new) (actualTangent (E := E) (Γ z) t) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  exact (hchart.comp z hslice).contDiffAt

/-- The actual initial-state derivative of a complete intrinsic family is invertible in
any legal output chart. A backward complete family supplies a genuine local left inverse;
no position-block invertibility or absence of conjugate points is assumed. -/
theorem isInvertible_fderiv_complete_tangentFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ)
    {Γ : (E × E) → ℝ → M}
    (hΓ : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old) (new : M) (t : ℝ)
    (hx : Γ z t ∈ (extChartAt 𝓘(ℝ, E) new).source) :
    (fderiv ℝ (fun w ↦ (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨new, 0⟩ : TangentBundle 𝓘(ℝ, E) M))
        (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩)) z).IsInvertible := by
  let A : (E × E) → E × E := fun w ↦
    phaseChart (E := E) new (actualTangent (E := E) (Γ w) t)
  have hsrc : actualTangent (E := E) (Γ z) t ∈ (phaseChart (E := E) new).source :=
    (phaseChart_source new _).mpr hx
  have hAz : A z ∈ chartEnergyDomain new :=
    hF.phaseChart_actualTangent_mem (hΓ z hz t (mem_univ t)) new hsrc
  have hA : ContDiffAt ℝ 2 A z :=
    contDiffAt_chartPhaseSlice (isOpen_chartEnergyDomain old) hG hz new t hsrc
  obtain ⟨Δ, hΔ, hΔinit, hΔG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete new t
  let R : (E × E) → E × E := fun w ↦
    phaseChart (E := E) old (actualTangent (E := E) (Δ w) t₀)
  have hcentral : Δ (A z) = Γ z := by
    funext u
    apply hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
      (hΔ (A z) hAz) (hΓ z hz) (mem_univ t) ?_ (mem_univ u)
    exact (hΔinit (A z) hAz).trans ((phaseChart (E := E) new).left_inv hsrc)
  have hrsource : actualTangent (E := E) (Δ (A z)) t₀ ∈
      (phaseChart (E := E) old).source := by
    rw [hcentral, actualTangent, hinit z hz]
    apply (phaseChart (E := E) old).map_target
    rw [tangentChart_target]
    exact ⟨hz.1, mem_univ _⟩
  have hR : ContDiffAt ℝ 2 R (A z) :=
    contDiffAt_chartPhaseSlice (isOpen_chartEnergyDomain new) hΔG hAz old t₀ hrsource
  have hslice : ContinuousAt (fun w ↦ actualTangent (E := E) (Γ w) t) z :=
    ((hG.contMDiffAt (((isOpen_chartEnergyDomain old).prod isOpen_univ).mem_nhds
      ⟨hz, mem_univ t⟩)).comp z
        ((contDiffAt_id.prodMk (contDiffAt_const (c := t))).contMDiffAt)).continuousAt
  have hnear : ∀ᶠ w in 𝓝 z,
      actualTangent (E := E) (Γ w) t ∈ (phaseChart (E := E) new).source :=
    hslice.preimage_mem_nhds ((isOpen_extChartAt_source _).mem_nhds hsrc)
  have hleft : R ∘ A =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz, hnear] with w hw hs
    have hAw : A w ∈ chartEnergyDomain new :=
      hF.phaseChart_actualTangent_mem (hΓ w hw t (mem_univ t)) new hs
    have heq : Δ (A w) = Γ w := by
      funext u
      apply hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
        (hΔ (A w) hAw) (hΓ w hw) (mem_univ t) ?_ (mem_univ u)
      exact (hΔinit (A w) hAw).trans ((phaseChart (E := E) new).left_inv hs)
    change phaseChart (E := E) old (actualTangent (E := E) (Δ (A w)) t₀) = w
    rw [heq, actualTangent, hinit w hw, (phaseChart (E := E) old).right_inv]
    rw [tangentChart_target]
    exact ⟨hw.1, mem_univ _⟩
  exact invertible_fderiv_of_local_left_inverse
    (hA.differentiableAt (by norm_num)) (hR.differentiableAt (by norm_num)) hleft

/-- Every injected differentiable initial seed retains its full phase rank under the
actual complete flow, in every valid output chart. -/
theorem injective_fderiv_seeded_complete_tangentFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ)
    {Γ : (E × E) → ℝ → M}
    (hΓ : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {seed : W → E × E} {w₀ : W} (hs : DifferentiableAt ℝ seed w₀)
    (hinj : Function.Injective (fderiv ℝ seed w₀))
    (hz : seed w₀ ∈ chartEnergyDomain old) (new : M) (t : ℝ)
    (hx : Γ (seed w₀) t ∈ (extChartAt 𝓘(ℝ, E) new).source) :
    Function.Injective (fderiv ℝ (fun w ↦ (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨new, 0⟩ : TangentBundle 𝓘(ℝ, E) M))
        (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ (seed w)) ⟨t, (1 : ℝ)⟩)) w₀) := by
  let A : (E × E) → E × E := fun w ↦
    phaseChart (E := E) new (actualTangent (E := E) (Γ w) t)
  have hA : DifferentiableAt ℝ A (seed w₀) :=
    (contDiffAt_chartPhaseSlice (isOpen_chartEnergyDomain old) hG hz new t
      ((phaseChart_source new _).mpr hx)).differentiableAt (by norm_num)
  have hi : Function.Injective (fderiv ℝ A (seed w₀)) := by
    obtain ⟨d, hd⟩ := hF.isInvertible_fderiv_complete_tangentFamily
      hcomplete old t₀ hΓ hinit hG hz new t hx
    rw [← hd]
    exact d.injective
  change Function.Injective (fderiv ℝ (A ∘ seed) w₀)
  rw [(hA.hasFDerivAt.comp w₀ hs.hasFDerivAt).fderiv]
  exact hi.comp hinj

/-- Original Finsler completeness constructs a genuine joint C2 complete family whose
full initial-phase derivative is invertible at every time in every valid output chart. -/
theorem exists_complete_tangentFamily_invertible [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ) :
    ∃ Γ : (E × E) → ℝ → M,
      (∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ) ∧
      (∀ z ∈ chartEnergyDomain old,
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (chartEnergyDomain old ×ˢ univ) ∧
      ∀ z ∈ chartEnergyDomain old, ∀ new : M, ∀ t : ℝ,
        Γ z t ∈ (extChartAt 𝓘(ℝ, E) new).source →
        (fderiv ℝ (fun w ↦ (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨new, 0⟩ : TangentBundle 𝓘(ℝ, E) M))
            (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩)) z).IsInvertible := by
  obtain ⟨Γ, hΓ, hinit, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old t₀
  exact ⟨Γ, hΓ, hinit, hG, fun z hz new t hx ↦
    hF.isInvertible_fderiv_complete_tangentFamily hcomplete old t₀ hΓ hinit hG hz new t hx⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
