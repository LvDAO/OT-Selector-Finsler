import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Same initial phase jet for two prescribed sections

An ordinary derivative of the original extension covector and the actual momentum
jet of a given smooth family are read through one supplied inverse Legendre branch.
Both initial tangent sections retain their actual values and ordinary first jets;
no new family, section or inverse branch is selected.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {F : ContinuousFinslerNorm E M}

/-- Two prescribed sections with the same initial position derivative give the
same ordinary initial tangent-phase jet under one given inverse Legendre branch.
The second section is identified through the actual initial momentum of its
supplied family; no family, section or inverse branch is selected here. -/
theorem same_initial_phaseJet_of_two_sections (hF : F.IsSmoothStronglyConvex)
    (old : M) (t₀ : ℝ) {G : E → ℝ} {x : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ G) H x)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ e.symm e.target)
    (hp : (x, fderiv ℝ G x) ∈ e.target)
    {B : Set W} {σG σP v : W → E} {Γ : W → ℝ → M}
    {J : W →L[ℝ] E}
    (hB : IsOpen B) (h0 : (0 : W) ∈ B)
    (hσG0 : σG 0 = x) (hσG : HasFDerivAt σG J 0)
    (hσP0 : σP 0 = x) (hσP : HasFDerivAt σP J 0)
    (hv : ContinuousAt v 0)
    (hv0 : v 0 = (e.symm (x, fderiv ℝ G x)).2)
    (hstate : ∀ w ∈ B, (σP w, v w) ∈ chartEnergyDomain old)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeAt (Γ w) t₀)
    (hinit : ∀ w ∈ B,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σP w, v w))
    (hjet : HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, t₀))
      (J.prod (H.comp J)) 0) :
    let q₀ := (x, fderiv ℝ G x)
    let z₀ := e.symm q₀
    let R : W → E × E := fun w ↦ e.symm (σG w, fderiv ℝ G (σG w))
    let N : W → E × E := fun w ↦ (σP w, v w)
    let D : W →L[ℝ] (E × E) :=
      (fderiv ℝ e.symm q₀).comp (J.prod (H.comp J))
    R 0 = z₀ ∧ N 0 = z₀ ∧
      HasFDerivAt R D 0 ∧ HasFDerivAt N D 0 ∧
      ∀ᶠ w in 𝓝 (0 : W),
        (σG w, fderiv ℝ G (σG w)) ∈ e.target ∧
        R w ∈ chartEnergyDomain old ∧ N w ∈ chartEnergyDomain old := by
  let q₀ := (x, fderiv ℝ G x)
  let C := fun w ↦ (σG w, fderiv ℝ G (σG w))
  let R := fun w ↦ e.symm (C w)
  let N := fun w ↦ (σP w, v w)
  let Q := fun w ↦ F.chartMomentumFamily old Γ (w, t₀)
  let A := J.prod (H.comp J)
  let D := (fderiv ℝ e.symm q₀).comp A
  change R 0 = e.symm q₀ ∧ N 0 = e.symm q₀ ∧
    HasFDerivAt R D 0 ∧ HasFDerivAt N D 0 ∧
    ∀ᶠ w in 𝓝 (0 : W), C w ∈ e.target ∧
      R w ∈ chartEnergyDomain old ∧ N w ∈ chartEnergyDomain old
  have hC0 : C 0 = q₀ := by simp only [C, q₀, hσG0]
  have hN0 : N 0 = e.symm q₀ :=
    Prod.ext (hσP0.trans (parametricLegendre_inverse_components he hp).1.symm) hv0
  have hC : HasFDerivAt C A 0 := by
    have hsecond' : HasFDerivAt (fderiv ℝ G) H (σG 0) := hσG0.symm ▸ hsecond
    exact hσG.prodMk (hsecond'.comp 0 hσG)
  have hE : HasFDerivAt e.symm (fderiv ℝ e.symm q₀) q₀ :=
    ((hInv.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt
  have hR : HasFDerivAt R D 0 :=
    (show HasFDerivAt e.symm (fderiv ℝ e.symm q₀) (C 0) by
      rw [hC0]
      exact hE).comp 0 hC
  have hNsource : ∀ᶠ w in 𝓝 (0 : W), N w ∈ e.source := by
    have hcenter : N 0 ∈ e.source := by
      rw [hN0]
      exact e.map_target hp
    exact (hσP.continuousAt.prodMk hv) (e.open_source.mem_nhds hcenter)
  have hQe : ∀ᶠ w in 𝓝 (0 : W), Q w = e (N w) := by
    filter_upwards [hB.mem_nhds h0] with w hw
    exact (hF.chartMomentum_of_tangent_eq (hEL w hw) old
      (hstate w hw) (hinit w hw)).trans (congrFun he (N w)).symm
  have hQ0 : Q 0 = q₀ := by
    rw [hQe.self_of_nhds, hN0]
    exact e.right_inv hp
  have hNQ : (fun w ↦ e.symm (Q w)) =ᶠ[𝓝 (0 : W)] N := by
    filter_upwards [hNsource, hQe] with w hw hq
    rw [hq, e.left_inv hw]
  have hQX : HasFDerivAt (fun w ↦ e.symm (Q w)) D 0 :=
    (show HasFDerivAt e.symm (fderiv ℝ e.symm q₀) (Q 0) by
      rw [hQ0]
      exact hE).comp 0 hjet
  have hN : HasFDerivAt N D 0 := hQX.congr_of_eventuallyEq hNQ.symm
  have hCtarget : ∀ᶠ w in 𝓝 (0 : W), C w ∈ e.target :=
    hC.continuousAt (by simpa only [hC0] using e.open_target.mem_nhds hp)
  refine ⟨?_, hN0, hR, hN, ?_⟩
  · change e.symm (C 0) = e.symm q₀
    rw [hC0]
  · filter_upwards [hCtarget, hNsource] with w hwC hwN
    exact ⟨hwC, hsub (e.map_target hwC), hsub hwN⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
