import OTSelector.Geometry.Finsler.TubeCoordinateVariation
import OTSelector.Analysis.Calculus.Variational.EndpointJacobiCompliance

/-!
# Actual integral compliance in genuine smooth tube coordinates

The original tangent energy pulled back by the actual tube gives a smooth positive
inverse fiber Hessian. Its true time integral is positive, symmetric and invertible.
The original family's proved variation equation recovers every actual momentum
variation from its actual endpoint position derivatives in the same genuine coordinates.
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

/-- The inverse true fiber Hessian on an actual curve read through the inverse tube. -/
def tubeInverseEnergyHessian (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (c : ℝ → M) (t : ℝ) : (V →L[ℝ] ℝ) →L[ℝ] V :=
  (verticalEnergyHessian (F.tubeCoordinateEnergy Y)
    ((Y.symm ∘ c) t, deriv (Y.symm ∘ c) t)).inverse

/-- The actual time integral of the original inverse fiber Hessian in the genuine tube. -/
def tubeEndpointCompliance (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (c : ℝ → M) (a b : ℝ) : (V →L[ℝ] ℝ) →L[ℝ] V :=
  endpointCompliance (F.tubeInverseEnergyHessian Y c) a b

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ V] {F : ContinuousFinslerNorm E M}

/-- The actual inverse fiber Hessian is jointly smooth in the true tube slit domain.
Its inverse is justified by original strong convexity, not supplied as separate data. -/
theorem contDiffOn_tubeInverseVerticalEnergyHessian (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target) :
    ContDiffOn ℝ ∞ (fun z ↦ (verticalEnergyHessian (F.tubeCoordinateEnergy Y) z).inverse)
      (Y.source ×ˢ {v : V | v ≠ 0}) := by
  let L := F.tubeCoordinateEnergy Y
  let U := Y.source ×ˢ {v : V | v ≠ 0}
  have hU : IsOpen U := Y.open_source.prod isOpen_ne
  have hL : ∀ z ∈ U, ContDiffAt ℝ ∞ L z := fun z hz ↦
    (hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt (hU.mem_nhds hz)
  intro z hz
  have hH : ContDiffAt ℝ ∞ (verticalEnergyHessian L) z := by
    have hh := ((contDiffAt_fiberLegendre (hL z hz)).fderiv_right
      (m := ∞) (by simp)).clm_comp (contDiffAt_const (c := ContinuousLinearMap.inr ℝ V V))
    apply hh.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with q hq
    exact (fiberLegendre_fderiv_vertical (hL q hq)).symm
  have hpos : ∀ u : V, u ≠ 0 → 0 < verticalEnergyHessian L z u u :=
    fun u hu ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi hz.1 hz.2 hu
  have hinv : (verticalEnergyHessian L z).IsInvertible :=
    ⟨positive_dualMap_equiv _ hpos, rfl⟩
  exact ((hinv.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp z hH).contDiffWithinAt

/-- Intrinsic Euler--Lagrange regularity makes the true inverse response continuous
along the actual curve at every time contained in the genuine tube target. -/
theorem continuousAt_tubeInverseEnergyHessian (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (hx : c t ∈ Y.target) :
    ContinuousAt (F.tubeInverseEnergyHessian Y c) t := by
  obtain ⟨I, hI, ht, hmap, hy, hv, _⟩ :=
    hF.exists_tubeCoordinateEulerLagrangeOn_of_isEulerLagrangeAt hY hi hc hx
  have hZ : ContinuousAt (fun s ↦ ((Y.symm ∘ c) s, deriv (Y.symm ∘ c) s)) t :=
    (hy.contDiffAt (hI.mem_nhds ht)).continuousAt.prodMk
      ((hy.deriv_of_isOpen hI (m := 1) (by norm_num)).contDiffAt
        (hI.mem_nhds ht)).continuousAt
  have hz : ((Y.symm ∘ c) t, deriv (Y.symm ∘ c) t) ∈
      Y.source ×ˢ {v : V | v ≠ 0} := ⟨Y.map_target hx, hv t ht⟩
  exact ((hF.contDiffOn_tubeInverseVerticalEnergyHessian hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)).continuousAt.comp
      (f := fun s ↦ ((Y.symm ∘ c) s, deriv (Y.symm ∘ c) s)) hZ

/-- Original strong convexity makes the true tube inverse response strictly positive. -/
theorem tubeInverseEnergyHessian_pos (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (hx : c t ∈ Y.target)
    {p : V →L[ℝ] ℝ} (hp : p ≠ 0) :
    0 < p (F.tubeInverseEnergyHessian Y c t p) := by
  obtain ⟨I, _, ht, _, _, hv, _⟩ :=
    hF.exists_tubeCoordinateEulerLagrangeOn_of_isEulerLagrangeAt hY hi hc hx
  exact inverse_verticalEnergyHessian_pos
    (fun u hu ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi
      (Y.map_target hx) (hv t ht) hu) hp

/-- Symmetry of the true scalar energy Hessian gives symmetry of the inverse response. -/
theorem tubeInverseEnergyHessian_symm (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (hx : c t ∈ Y.target)
    (p q : V →L[ℝ] ℝ) :
    p (F.tubeInverseEnergyHessian Y c t q) = q (F.tubeInverseEnergyHessian Y c t p) := by
  obtain ⟨I, _, ht, _, _, hv, _⟩ :=
    hF.exists_tubeCoordinateEulerLagrangeOn_of_isEulerLagrangeAt hY hi hc hx
  let z := ((Y.symm ∘ c) t, deriv (Y.symm ∘ c) t)
  let H := verticalEnergyHessian (F.tubeCoordinateEnergy Y) z
  have hpos : ∀ v : V, v ≠ 0 → 0 < H v v := fun v hv' ↦
    hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi (Y.map_target hx) (hv t ht) hv'
  let e := positive_dualMap_equiv H hpos
  have hInv : H.inverse = e.symm.toContinuousLinearMap := ContinuousLinearMap.inverse_equiv e
  change p (H.inverse q) = q (H.inverse p)
  rw [hInv]
  have hL := (hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds
      (show z ∈ Y.source ×ˢ {v : V | v ≠ 0} from ⟨Y.map_target hx, hv t ht⟩))
  have hf : ContDiffAt ℝ ∞ (fun v ↦ F.tubeCoordinateEnergy Y (z.1, v)) z.2 :=
    hL.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  have hs := hf.isSymmSndFDerivAt (by simp) (e.symm p) (e.symm q)
  change e (e.symm p) (e.symm q) = e (e.symm q) (e.symm p) at hs
  simpa only [e.apply_symm_apply] using! hs

/-- The true integrated tube response is invertible on each nontrivial central segment. -/
theorem isInvertible_tubeEndpointCompliance (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, F.IsEulerLagrangeAt c t)
    (hx : ∀ t ∈ Icc a b, c t ∈ Y.target) :
    (F.tubeEndpointCompliance Y c a b).IsInvertible := by
  exact endpointCompliance_isInvertible hab
    (fun t ht ↦ (hF.continuousAt_tubeInverseEnergyHessian hY hi (hc t ht)
      (hx t ht)).continuousWithinAt)
    (fun t ht p hp ↦ hF.tubeInverseEnergyHessian_pos hY hi (hc t ht) (hx t ht) hp)


/-- The original integral and its actual inverse are positive and symmetric under the
vector-covector pairing. Every analytic premise is derived from the genuine tube energy. -/
theorem tubeEndpointCompliance_properties (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, F.IsEulerLagrangeAt c t)
    (hx : ∀ t ∈ Icc a b, c t ∈ Y.target) :
    let S := F.tubeEndpointCompliance Y c a b
    S.IsInvertible ∧
      (∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (S p)) ∧
      (∀ p q : V →L[ℝ] ℝ, p (S q) = q (S p)) ∧
      (∀ v : V, v ≠ 0 → 0 < S.inverse v v) ∧
      ∀ u v : V, S.inverse u v = S.inverse v u := by
  have hC : ContinuousOn (F.tubeInverseEnergyHessian Y c) (Icc a b) :=
    fun t ht ↦ (hF.continuousAt_tubeInverseEnergyHessian hY hi (hc t ht)
      (hx t ht)).continuousWithinAt
  have hp : ∀ t ∈ Icc a b, ∀ p : V →L[ℝ] ℝ, p ≠ 0 →
      0 < p (F.tubeInverseEnergyHessian Y c t p) :=
    fun t ht p hp ↦ hF.tubeInverseEnergyHessian_pos hY hi (hc t ht) (hx t ht) hp
  have hs : ∀ t ∈ Icc a b, ∀ p q : V →L[ℝ] ℝ,
      p (F.tubeInverseEnergyHessian Y c t q) = q (F.tubeInverseEnergyHessian Y c t p) :=
    fun t ht p q ↦ hF.tubeInverseEnergyHessian_symm hY hi (hc t ht) (hx t ht) p q
  exact ⟨endpointCompliance_isInvertible hab hC hp,
    fun p hp' ↦ endpointCompliance_pos hab hC hp hp',
    endpointCompliance_symm hab.le hC hs,
    fun v hv ↦ endpointCompliance_inverse_pos hab hC hp hv,
    endpointCompliance_inverse_symm hab hC hp hs⟩

/-- The real integral response solves the actual momentum parameter variation from its
endpoint phase positions, with the original Jacobi equation derived in the true tube. -/
theorem tubeMomentumVariation_eq_compliance_inverse_phase (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w t ∈ Y.target)
    (hzero : ∀ t ∈ Icc a b, ∀ u : V,
      fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y))
        (tubeCoordinateTangentFamily Y Γ (w, t)) (u, 0) = 0) (ξ : W) :
    ∀ t ∈ Icc a b,
      (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w ξ).2 =
        (F.tubeEndpointCompliance Y (Γ w) a b).inverse
          ((fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, b)) w ξ).1 -
            (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, a)) w ξ).1) := by
  let D := (B ×ˢ (univ : Set ℝ)) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹' Y.target
  have hc : ContinuousOn (fun q : W × ℝ ↦ Γ q.1 q.2) (B ×ˢ univ) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn hG.continuousOn
  have hD : IsOpen D := hc.isOpen_inter_preimage (hB.prod isOpen_univ) Y.open_target
  let R := fun t ↦ fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w ξ
  have hODE (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt R (F.tubeInverseEnergyHessian Y (Γ w) t (R t).2, 0) t :=
    hF.hasDerivAt_tubeCoordinateMomentumVariation_of_hessian_base_zero hY hi hD
      (hG.mono inter_subset_left) (fun _ h ↦ h.2)
      (fun q h ↦ hEL q.1 h.1.1 q.2 (mem_univ _))
      (show (w, t) ∈ D from ⟨⟨hw, mem_univ _⟩, hx t ht⟩) (hzero t ht) ξ
  exact momentum_eq_endpointCompliance_inverse hab
    (fun t ht ↦ (hF.continuousAt_tubeInverseEnergyHessian hY hi
      (hEL w hw t (mem_univ _)) (hx t ht)).continuousWithinAt)
    (fun t ht p hp ↦ hF.tubeInverseEnergyHessian_pos hY hi
      (hEL w hw t (mem_univ _)) (hx t ht) hp)
    (fun t ht ↦ (hODE t ht).fst) (fun t ht ↦ (hODE t ht).snd)


/-- The actual compliance formula uses the true inverse-tube endpoint position
Fréchet derivatives, retaining every intermediate momentum of the same family. -/
theorem tubeMomentumVariation_eq_compliance_inverse (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w t ∈ Y.target)
    (hzero : ∀ t ∈ Icc a b, ∀ u : V,
      fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y))
        (tubeCoordinateTangentFamily Y Γ (w, t)) (u, 0) = 0) (ξ : W) :
    ∀ t ∈ Icc a b,
      (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w ξ).2 =
        (F.tubeEndpointCompliance Y (Γ w) a b).inverse
          (fderiv ℝ (fun v ↦ Y.symm (Γ v b)) w ξ -
            fderiv ℝ (fun v ↦ Y.symm (Γ v a)) w ξ) := by
  let D := (B ×ˢ (univ : Set ℝ)) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹' Y.target
  have hc : ContinuousOn (fun q : W × ℝ ↦ Γ q.1 q.2) (B ×ˢ univ) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn hG.continuousOn
  have hD : IsOpen D := hc.isOpen_inter_preimage (hB.prod isOpen_univ) Y.open_target
  have hpos (t : ℝ) (ht : t ∈ Icc a b) :
      (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w ξ).1 =
        fderiv ℝ (fun v ↦ Y.symm (Γ v t)) w ξ := by
    have hq : (w, t) ∈ D := ⟨⟨hw, mem_univ _⟩, hx t ht⟩
    have hp := ((hF.contDiffOn_tubeCoordinateMomentumFamily hY hi hD
      (hG.mono inter_subset_left) (fun _ h ↦ h.2)
      (fun q h ↦ hEL q.1 h.1.1 q.2 (mem_univ _))).contDiffAt (hD.mem_nhds hq)).comp w
        (contDiffAt_id.prodMk contDiffAt_const)
    have hd := (hp.differentiableAt (by norm_num)).hasFDerivAt.fst.fderiv
    exact (congrArg (fun A : W →L[ℝ] V ↦ A ξ) hd).symm
  intro t ht
  rw [hF.tubeMomentumVariation_eq_compliance_inverse_phase hY hi hB hEL hG hw hab
    hx hzero ξ t ht, hpos b (right_mem_Icc.mpr hab.le), hpos a (left_mem_Icc.mpr hab.le)]

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
