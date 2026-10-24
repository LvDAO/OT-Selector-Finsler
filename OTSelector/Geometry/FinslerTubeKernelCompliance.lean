import OTSelector.Geometry.FinslerTubeCoordinateDistanceHessian
import OTSelector.Analysis.Calculus.Variational.KernelEndpointCompliance

/-!
# Restricted length-Hessian compliance in the same actual tube

The canonical time kernel carries the actual restricted length Hessian. Calibration
identifies its inverse with compression of the genuine inverse energy Hessian;
integration gives the same pure-label coefficient of the original distance.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E V W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The true fiber length Hessian restricted to a fixed covector kernel in the tube. -/
def tubeLengthKernelHessian (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (p : V →L[ℝ] ℝ) (z : V × V) :
    p.ker →L[ℝ] (p.ker →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ p.ker V ℝ).flip p.ker.subtypeL).comp
    ((fderiv ℝ (fderiv ℝ (fun v ↦ F.tubeCoordinateLength Y (z.1, v))) z.2).comp
      p.ker.subtypeL)

/-- Integrate the inverses of the actual restricted length Hessians along the same curve. -/
def tubeLengthKernelCompliance (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (p : V →L[ℝ] ℝ)
    (c : ℝ → M) (a b : ℝ) : (p.ker →L[ℝ] ℝ) →L[ℝ] p.ker :=
  endpointCompliance (fun t ↦ (F.tubeLengthKernelHessian Y p
    ((Y.symm ∘ c) t, deriv (Y.symm ∘ c) t)).inverse) a b

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] in
private theorem tube_kernel_compression_at
    (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ y ∈ Y.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) y z)
        (F.toFun ⟨y, z⟩ : ℝ))
    {q : ℝ × W} (hq : q ∈ Y.source) :
    let p := ContinuousLinearMap.fst ℝ ℝ W
    let v₀ : ℝ × W := (1, 0)
    covectorKernelCompression p v₀ (by simp [p, v₀])
      (verticalEnergyHessian (F.tubeCoordinateEnergy Y) (q, v₀)).inverse =
        (F.tubeLengthKernelHessian Y p (q, v₀)).inverse := by
  let p := ContinuousLinearMap.fst ℝ ℝ W
  let v₀ : ℝ × W := (1, 0)
  let H := verticalEnergyHessian (F.tubeCoordinateEnergy Y) (q, v₀)
  have hv : v₀ ≠ 0 := by simp [v₀]
  have hpv : p v₀ ≠ 0 := by simp [p, v₀]
  have hz : (q, v₀) ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} := ⟨hq, hv⟩
  have hcal := hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀ heq hhalf hbound hq
  have hLp : fderiv ℝ (fun v ↦ F.tubeCoordinateLength Y (q, v)) v₀ = p := hcal.1
  have hEp : fiberLegendre (F.tubeCoordinateEnergy Y) (q, v₀) = p := hcal.2.2.1
  have hunit : F.tubeCoordinateLength Y (q, v₀) = 1 :=
    (F.tubeCoordinate_timeColumn_unit hY heq hhalf hq).2
  have hLH (u : ℝ × W) :
      fderiv ℝ (fderiv ℝ (fun v ↦ F.tubeCoordinateLength Y (q, v))) v₀ u =
        H u - (p u) • p := by
    have h := hF.tubeLengthMomentum_parameter_fderiv_of_unit hY hi
      (Z := fun v : ℝ × W ↦ (q, v)) (p₀ := v₀)
      ((show ContDiffAt ℝ ∞ (fun v : ℝ × W ↦ (q, v)) v₀ from
        contDiffAt_const.prodMk contDiffAt_id).differentiableAt (by simp)) hz hunit u
    change fderiv ℝ (fderiv ℝ (fun v ↦ F.tubeCoordinateLength Y (q, v))) v₀ u =
      H u - (fderiv ℝ (fun v ↦ F.tubeCoordinateLength Y (q, v)) v₀ u) •
        fiberLegendre (F.tubeCoordinateEnergy Y) (q, v₀) at h
    rwa [hLp, hEp] at h
  have hK (u w : p.ker) :
      F.tubeLengthKernelHessian Y p (q, v₀) u w = H (u : ℝ × W) (w : ℝ × W) := by
    change fderiv ℝ (fderiv ℝ (fun v ↦ F.tubeCoordinateLength Y (q, v))) v₀
      (u : ℝ × W) (w : ℝ × W) = _
    rw [hLH, show p (u : ℝ × W) = 0 from u.property, zero_smul, sub_zero]
  have hposH (u : ℝ × W) (hu : u ≠ 0) : 0 < H u u :=
    hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi hq hv hu
  have hH : H.IsInvertible := ⟨positive_dualMap_equiv H hposH, rfl⟩
  have hC := (hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)
  have hCf : ContDiffAt ℝ ∞ (fun v ↦ F.tubeCoordinateEnergy Y (q, v)) v₀ :=
    hC.comp v₀ (contDiffAt_const.prodMk contDiffAt_id)
  have hsym (u w : ℝ × W) : H u w = H w u :=
    hCf.isSymmSndFDerivAt (by simp) u w
  have hrad : H v₀ = p := by
    apply ContinuousLinearMap.ext
    intro u
    rw [hsym]
    have h := hF.tubeEnergy_inverseHessian_radial_pairing hY hi hz (H u)
    rw [hEp] at h
    change p (H.inverse (H u)) = H u v₀ at h
    rw [hH.inverse_apply_self] at h
    exact h.symm
  have hposK (u : p.ker) (hu : u ≠ 0) :
      0 < F.tubeLengthKernelHessian Y p (q, v₀) u u := by
    rw [hK]
    exact hposH u (fun he ↦ hu (Subtype.ext he))
  let d := positive_dualMap_equiv (F.tubeLengthKernelHessian Y p (q, v₀)) hposK
  change covectorKernelCompression p v₀ hpv H.inverse =
    (F.tubeLengthKernelHessian Y p (q, v₀)).inverse
  rw [show (F.tubeLengthKernelHessian Y p (q, v₀)).inverse = d.symm.toContinuousLinearMap from
    ContinuousLinearMap.inverse_equiv d]
  apply ContinuousLinearMap.ext
  intro η
  apply d.injective
  change d (covectorKernelCompression p v₀ hpv H.inverse η) = d (d.symm η)
  rw [d.apply_symm_apply]
  apply ContinuousLinearMap.ext
  intro w
  change F.tubeLengthKernelHessian Y p (q, v₀)
    (covectorKernelCompression p v₀ hpv H.inverse η) w = η w
  rw [hK]
  exact covectorKernelCompression_inverse p v₀ hpv hsym hrad hH.self_apply_inverse η w


/-- Pure-label inverse energy compliance equals inverse integrated length response. -/
theorem tubeEndpointCompliance_inverse_on_timeKernel
    (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ y ∈ Y.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) y z)
        (F.toFun ⟨y, z⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {w : W}
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source) (α β : W) :
    let p := ContinuousLinearMap.fst ℝ ℝ W
    let ξ : p.ker := ⟨(0, α), by simp [p]⟩
    let η : p.ker := ⟨(0, β), by simp [p]⟩
    (F.tubeEndpointCompliance Y (Λ w) a b).inverse (0, α) (0, β) =
      (F.tubeLengthKernelCompliance Y p (Λ w) a b).inverse ξ η := by
  let p := ContinuousLinearMap.fst ℝ ℝ W
  let v₀ : ℝ × W := (1, 0)
  have hp : p v₀ ≠ 0 := by simp [p, v₀]
  let C := F.tubeInverseEnergyHessian Y (Λ w)
  have hphase (t : ℝ) (ht : t ∈ Icc a b) :
      ((Y.symm ∘ Λ w) t, deriv (Y.symm ∘ Λ w) t) = ((t, w), v₀) := by
    have hn : (fun r : ℝ ↦ (r, w)) ⁻¹' Y.source ∈ 𝓝 t :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
        (Y.open_source.mem_nhds (hstay t ht))
    have he : (Y.symm ∘ Λ w) =ᶠ[𝓝 t] (fun r ↦ (r, w)) := by
      filter_upwards [hn] with r hr
      change Y.symm (Λ w r) = (r, w)
      rw [← congrFun heq (r, w)]
      exact Y.left_inv hr
    rw [he.eq_of_nhds, he.deriv_eq]
    congr 1
    exact (hasDerivAt_id t |>.prodMk (hasDerivAt_const t w)).deriv
  have hCeq (t : ℝ) (ht : t ∈ Icc a b) :
      C t = (verticalEnergyHessian (F.tubeCoordinateEnergy Y) ((t, w), v₀)).inverse := by
    dsimp only [C, tubeInverseEnergyHessian]
    rw [hphase t ht]
  have hC : ContinuousOn C (Icc a b) := by
    have hrad : ContinuousOn
        (fun t ↦ (verticalEnergyHessian (F.tubeCoordinateEnergy Y) ((t, w), v₀)).inverse)
        (Icc a b) :=
      (hF.contDiffOn_tubeInverseVerticalEnergyHessian hY hi).continuousOn.comp
        ((continuous_id.prodMk continuous_const).prodMk continuous_const).continuousOn
        (fun t ht ↦ ⟨hstay t ht, by simp [v₀]⟩)
    exact hrad.congr (fun t ht ↦ hCeq t ht)
  have hpos (t : ℝ) (ht : t ∈ Icc a b) (θ : (ℝ × W) →L[ℝ] ℝ) (hθ : θ ≠ 0) :
      0 < θ (C t θ) := by
    rw [hCeq t ht]
    exact inverse_verticalEnergyHessian_pos
      (fun u hu ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi
        (hstay t ht) (by simp [v₀]) hu) hθ
  have hrad (t : ℝ) (ht : t ∈ Icc a b) (θ : (ℝ × W) →L[ℝ] ℝ) :
      p (C t θ) = θ v₀ := by
    rw [hCeq t ht]
    have h := hF.tubeEnergy_inverseHessian_radial_pairing hY hi
      (show ((t, w), v₀) ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} from
        ⟨hstay t ht, by simp [v₀]⟩) θ
    rw [(hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀ heq hhalf
      hbound (hstay t ht)).2.2.1] at h
    exact h
  have hK : endpointCompliance (fun t ↦ covectorKernelCompression p v₀ hp (C t)) a b =
      F.tubeLengthKernelCompliance Y p (Λ w) a b := by
    apply endpointCompliance_congr_on hab.le
    intro t ht
    dsimp only [tubeLengthKernelCompliance]
    rw [hCeq t ht]
    change covectorKernelCompression p v₀ hp
      (verticalEnergyHessian (F.tubeCoordinateEnergy Y) ((t, w), v₀)).inverse =
        (F.tubeLengthKernelHessian Y p
          ((Y.symm ∘ Λ w) t, deriv (Y.symm ∘ Λ w) t)).inverse
    rw [hphase t ht]
    exact tube_kernel_compression_at hF hY hi heq hhalf t₀ hbound (hstay t ht)
  have h := endpointCompliance_inverse_on_kernel p v₀ hp hab hC hpos hrad
    (⟨(0, α), by simp [p]⟩ : p.ker) (⟨(0, β), by simp [p]⟩ : p.ker)
  rw [hK] at h
  exact h

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
