import OTSelector.Analysis.Calculus.Variational.EndpointHessianCalculus
import OTSelector.Geometry.Finsler.LengthMomentumVariation
import OTSelector.Geometry.Finsler.EndpointCompliance
import OTSelector.Geometry.Finsler.EndpointDistanceC3

/-!
# The Hessian of the original endpoint distance

On the same actual endpoint inverse branch, the proved first variation is differentiated
using the original Jacobi equation. Calibration of a fixed unit velocity supplies the
zero energy base blocks and fixes the radial correction. The result uses the integral
of the original inverse energy Hessian along the central segment.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The original global endpoint distance has the compliance Hessian with its exact
radial correction. All momentum variations are obtained from the same actual family;
no second-derivative identity or independent Jacobi field is assumed. -/
theorem endpointDistance_hessian_of_calibrated_branch (hF : F.IsSmoothStronglyConvex)
    (old : M) {Γ : (E × E) → ℝ → M} {B : Set (E × E)}
    (hEL : ∀ z ∈ B, F.IsEulerLagrangeOn (Γ z) univ)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ r.1) ⟨r.2, (1 : ℝ)⟩)
      (B ×ˢ univ))
    {e : OpenPartialHomeomorph (E × E) (E × E)} (hsube : e.source ⊆ B)
    (hi : ContDiffOn ℝ 2 e.symm e.target) {W : Set (E × E)} (hW : IsOpen W)
    (hWe : W ⊆ e.target) {q₀ : E × E} (hq₀ : q₀ ∈ W)
    {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I) {a b : ℝ} (hab : a < b)
    (hsegment : Icc a b ⊆ I)
    (hmap : ∀ q ∈ W, MapsTo (Γ (e.symm q)) I (extChartAt 𝓘(ℝ, E) old).source)
    (hend : ∀ q ∈ W,
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) a) = q.1 ∧
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) b) = q.2)
    (hbranch : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      ∀ q ∈ W, (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal =
          (pathELength 𝓘(ℝ, E) (Γ (e.symm q)) a b).toReal)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, (F.chartLength old (x, v₀) : ℝ) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ (F.chartLength old (x, v) : ℝ))
    (hspace : ∀ t ∈ Icc a b, extChartAt 𝓘(ℝ, E) old (Γ (e.symm q₀) t) ∈ U)
    (hvelocity : ∀ t ∈ Icc a b,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ (e.symm q₀)) t = v₀)
    (h k : E × E) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    fderiv ℝ (fderiv ℝ d) q₀ h k =
      (F.chartEndpointCompliance old (Γ (e.symm q₀)) a b).inverse
        (h.2 - h.1) (k.2 - k.1) - p (h.2 - h.1) * p (k.2 - k.1) / (b - a) := by
  let Γ' : (E × E) → ℝ → M := fun q ↦ Γ (e.symm q)
  let Z (t : ℝ) := endpointChartPhase old Γ e t
  let c := Γ' q₀
  let C := F.chartInverseEnergyHessian old c
  let S := F.chartEndpointCompliance old c a b
  let d : E × E → ℝ := fun q ↦
    (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
      ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
  have hEL' : ∀ q ∈ W, F.IsEulerLagrangeOn (Γ' q) univ :=
    fun q hq ↦ hEL (e.symm q) (hsube (e.map_target (hWe hq)))
  have hG' : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ' r.1) ⟨r.2, (1 : ℝ)⟩)
      (W ×ˢ univ) := by
    have hpre : ContDiffOn ℝ 2 (fun r : (E × E) × ℝ ↦ (e.symm r.1, r.2))
        (W ×ˢ univ) :=
      ((hi.mono hWe).comp contDiffOn_fst (fun _ hr ↦ hr.1)).prodMk contDiffOn_snd
    exact hG.comp hpre.contMDiffOn
      (fun r hr ↦ ⟨hsube (e.map_target (hWe hr.1)), mem_univ _⟩)
  have hELI : ∀ q ∈ W, F.IsEulerLagrangeOn (Γ' q) I :=
    fun q hq t _ ↦ hEL' q hq t (mem_univ _)
  have hGI := hG'.mono (prod_mono (Subset.refl W) (subset_univ I))
  obtain ⟨hgrad, hPa, hPb, _⟩ := hF.endpointDistance_C3_of_branch old hW hI hconn hab.le
    hsegment hELI hGI hmap hend hbranch
  have hZd (t : ℝ) (ht : t ∈ I) : DifferentiableAt ℝ (Z t) q₀ :=
    ((hF.contDiffOn_endpointChartPhase old hELI hGI hmap ht).contDiffAt
      (hW.mem_nhds hq₀)).differentiableAt (by norm_num)
  have hx (t : ℝ) (ht : t ∈ Icc a b) :
      c t ∈ (extChartAt 𝓘(ℝ, E) old).source := hmap q₀ hq₀ (hsegment ht)
  have hz (t : ℝ) (ht : t ∈ Icc a b) : Z t q₀ ∈ chartEnergyDomain old :=
    (hF.chartTangent_of_isEulerLagrangeAt (hEL' q₀ hq₀ t (mem_univ _)) old (hx t ht)).2
  have hident (t : ℝ) (ht : t ∈ Icc a b) :=
    hF.chartEnergy_calibrated_identities old hU hsub p hp
      (fun x hx ↦ NNReal.coe_injective (by simpa using hunit x hx)) hbound (hspace t ht)
  have hzero (t : ℝ) (ht : t ∈ Icc a b) (u : E) :
      fderiv ℝ (fderiv ℝ (F.chartEnergy old))
        ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t)
          (u, 0) = 0 := by
    change fderiv ℝ (fderiv ℝ (F.chartEnergy old))
      ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ (e.symm q₀)) t) (u, 0) = 0
    rw [hvelocity t ht]
    exact (hident t ht).2.2.2.2.2.2.1 u
  have hC : ContinuousOn C (Icc a b) := fun t ht ↦
    (hF.continuousAt_chartInverseEnergyHessian hW hEL' hG' hq₀ old t
      (hx t ht)).continuousWithinAt
  have hSinv : S.IsInvertible :=
    hF.isInvertible_chartEndpointCompliance hW hEL' hG' hq₀ old hab hx
  have hrad (t : ℝ) (ht : t ∈ Icc a b) (Q : E →L[ℝ] ℝ) : p (C t Q) = Q v₀ := by
    have hmomentum : fiberLegendre (F.chartEnergy old) (Z t q₀) = p := by
      change fiberLegendre (F.chartEnergy old)
        ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
          deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ (e.symm q₀)) t) = p
      rw [hvelocity t ht]
      exact (hident t ht).2.2.1
    have hh := hF.chartEnergy_inverseHessian_radial_pairing old (hz t ht) Q
    rw [hmomentum] at hh
    exact hh.trans (congrArg Q (hvelocity t ht))
  have hradinv (v : E) : S.inverse v v₀ = p v / (b - a) :=
    endpointCompliance_inverse_radial_pairing hab hC p v₀ hrad hSinv v
  have hposition_a : (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ' q a)) =ᶠ[𝓝 q₀] Prod.fst :=
    Filter.Eventually.mono (hW.mem_nhds hq₀) (fun q hq ↦ (hend q hq).1)
  have hposition_b : (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ' q b)) =ᶠ[𝓝 q₀] Prod.snd :=
    Filter.Eventually.mono (hW.mem_nhds hq₀) (fun q hq ↦ (hend q hq).2)
  have hresponse (t : ℝ) (ht : t ∈ Icc a b) (u : E × E) :
      fderiv ℝ (fiberLegendre (F.chartEnergy old) ∘ Z t) q₀ u =
        S.inverse (u.2 - u.1) := by
    have hP : DifferentiableAt ℝ (fiberLegendre (F.chartEnergy old) ∘ Z t) q₀ :=
      ((contDiffAt_fiberLegendre ((hF.contDiffOn_chartEnergy old).contDiffAt
        ((isOpen_chartEnergyDomain old).mem_nhds (hz t ht)))).differentiableAt
          (by simp)).comp q₀ (hZd t (hsegment ht))
    have hΨ : DifferentiableAt ℝ (fun q ↦ F.chartMomentumFamily old Γ' (q, t)) q₀ :=
      ((hZd t (hsegment ht)).fst).prodMk hP
    have hsecond := congrArg (fun D : (E × E) →L[ℝ] (E →L[ℝ] ℝ) ↦ D u)
      hΨ.hasFDerivAt.snd.fderiv
    have hr := hF.chartMomentumVariation_eq_compliance_inverse hW hEL' hG' hq₀ old
      hab hx hzero u t ht
    rw [hposition_a.fderiv_eq, hposition_b.fderiv_eq, fderiv_fst, fderiv_snd] at hr
    exact hsecond.trans hr
  have hnormalized (t : ℝ) (ht : t ∈ Icc a b) (u : E × E) :
      fderiv ℝ (F.endpointLengthMomentum old Γ e t) q₀ u =
        S.inverse (u.2 - u.1) - (p (u.2 - u.1) / (b - a)) • p := by
    have hh := hF.chartLengthMomentum_parameter_fderiv_of_calibrated old hU hsub p hp
      hunit hbound (hZd t (hsegment ht)) (hspace t ht) (hvelocity t ht) u
    rw [hresponse t ht u, hradinv] at hh
    exact hh
  apply endpoint_hessian_of_momentum_response
    ((hPa.contDiffAt (hW.mem_nhds hq₀)).differentiableAt (by norm_num))
    ((hPb.contDiffAt (hW.mem_nhds hq₀)).differentiableAt (by norm_num))
    (Filter.Eventually.mono (hW.mem_nhds hq₀) (fun q hq ↦ (hgrad q hq).fderiv))
    S.inverse p (b - a)
    (hnormalized a (left_mem_Icc.mpr hab.le))
    (hnormalized b (right_mem_Icc.mpr hab.le)) h k

/-- On displacements annihilated by the actual calibrated covector, the radial
correction vanishes and the distance Hessian is the inverse integrated response. -/
theorem endpointDistance_hessian_on_kernel_displacement (hF : F.IsSmoothStronglyConvex)
    (old : M) {Γ : (E × E) → ℝ → M} {B : Set (E × E)}
    (hEL : ∀ z ∈ B, F.IsEulerLagrangeOn (Γ z) univ)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ r.1) ⟨r.2, (1 : ℝ)⟩)
      (B ×ˢ univ))
    {e : OpenPartialHomeomorph (E × E) (E × E)} (hsube : e.source ⊆ B)
    (hi : ContDiffOn ℝ 2 e.symm e.target) {W : Set (E × E)} (hW : IsOpen W)
    (hWe : W ⊆ e.target) {q₀ : E × E} (hq₀ : q₀ ∈ W)
    {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I) {a b : ℝ} (hab : a < b)
    (hsegment : Icc a b ⊆ I)
    (hmap : ∀ q ∈ W, MapsTo (Γ (e.symm q)) I (extChartAt 𝓘(ℝ, E) old).source)
    (hend : ∀ q ∈ W,
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) a) = q.1 ∧
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) b) = q.2)
    (hbranch : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      ∀ q ∈ W, (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal =
          (pathELength 𝓘(ℝ, E) (Γ (e.symm q)) a b).toReal)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, (F.chartLength old (x, v₀) : ℝ) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ (F.chartLength old (x, v) : ℝ))
    (hspace : ∀ t ∈ Icc a b, extChartAt 𝓘(ℝ, E) old (Γ (e.symm q₀) t) ∈ U)
    (hvelocity : ∀ t ∈ Icc a b,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ (e.symm q₀)) t = v₀)
    (h k : E × E) (hker : p (h.2 - h.1) = 0) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    fderiv ℝ (fderiv ℝ d) q₀ h k =
      (F.chartEndpointCompliance old (Γ (e.symm q₀)) a b).inverse
        (h.2 - h.1) (k.2 - k.1) := by
  have hh := hF.endpointDistance_hessian_of_calibrated_branch old hEL hG hsube hi hW
    hWe hq₀ hI hconn hab hsegment hmap hend hbranch hU hsub p hp hunit hbound
    hspace hvelocity h k
  simpa only [hker, zero_mul, zero_div, sub_zero] using hh

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
