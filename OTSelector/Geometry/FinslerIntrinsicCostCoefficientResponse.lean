import OTSelector.Geometry.FinslerIntrinsicCostCoefficientHessian
import OTSelector.LinearAlgebra.Matrix.OperatorIntervalIntegral

/-!
# The actual restricted length response of a calibrated tube

Calibration and strong convexity give positive restricted length Hessians and
continuous positive inverse responses. Their true operator integral is the
coefficient already appearing in the original distance expansion.
-/

open Set Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedTube

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}
  {Λ : W → ℝ → M} {a b : ℝ} {u : M → ℝ}
  (D : F.CalibratedTube Λ a b u)

local instance : NormedAddCommGroup
    (((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ) →L[ℝ]
      (ContinuousLinearMap.fst ℝ ℝ W).ker) := by
  exact_mod_cast (ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := (ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ)
    (F := (ContinuousLinearMap.fst ℝ ℝ W).ker))

local instance : NormedSpace ℝ
    (((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ) →L[ℝ]
      (ContinuousLinearMap.fst ℝ ℝ W).ker) := by
  exact_mod_cast (ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := (ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ)
    (F := (ContinuousLinearMap.fst ℝ ℝ W).ker))

local instance : NormedAddCommGroup
    ((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ]
      ((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ)) := by
  exact_mod_cast (ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := (ContinuousLinearMap.fst ℝ ℝ W).ker)
    (F := (ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ))

local instance : NormedSpace ℝ
    ((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ]
      ((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ)) := by
  exact_mod_cast (ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := (ContinuousLinearMap.fst ℝ ℝ W).ker)
    (F := (ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ))

/-- The actual restricted length Hessian along the central curve, in the canonical time kernel. -/
def lengthKernelHessian (t : ℝ) :
    (ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ]
      ((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ) :=
  F.tubeLengthKernelHessian D.toOpenPartialHomeomorph (ContinuousLinearMap.fst ℝ ℝ W)
    ((t, 0), (1, 0))

/-- The actual inverse of the restricted length Hessian in the same tube and time. -/
def lengthKernelResponse (t : ℝ) :
    ((ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ) →L[ℝ]
      (ContinuousLinearMap.fst ℝ ℝ W).ker :=
  (D.lengthKernelHessian t).inverse

omit [FiniteDimensional ℝ W] in
/-- The original central curve has exactly its original time and unit time velocity
when read through this same tube inverse. -/
theorem coordinatePhase {t : ℝ} (ht : t ∈ Icc a b) :
    ((D.toOpenPartialHomeomorph.symm ∘ Λ 0) t,
      deriv (D.toOpenPartialHomeomorph.symm ∘ Λ 0) t) = ((t, 0), (1, 0)) := by
  let Y := D.toOpenPartialHomeomorph
  have hn : (fun r : ℝ ↦ (r, (0 : W))) ⁻¹' Y.source ∈ 𝓝 t :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (Y.open_source.mem_nhds (D.stay t ht))
  have he : (Y.symm ∘ Λ 0) =ᶠ[𝓝 t] (fun r ↦ (r, (0 : W))) := by
    filter_upwards [hn] with r hr
    change Y.symm (Λ 0 r) = (r, 0)
    rw [← congrFun D.coe_eq (r, 0)]
    exact Y.left_inv hr
  rw [he.eq_of_nhds, he.deriv_eq]
  congr 1
  exact (hasDerivAt_id t |>.prodMk (hasDerivAt_const t (0 : W))).deriv

omit [FiniteDimensional ℝ W] in
/-- Calibration makes the actual restricted length Hessian strictly positive. -/
theorem lengthKernelHessian_pos (hF : F.IsSmoothStronglyConvex)
    {t : ℝ} (ht : t ∈ Icc a b)
    (ξ : (ContinuousLinearMap.fst ℝ ℝ W).ker) (hξ : ξ ≠ 0) :
    0 < D.lengthKernelHessian t ξ ξ := by
  let Y := D.toOpenPartialHomeomorph
  let p := ContinuousLinearMap.fst ℝ ℝ W
  let q : ℝ × W := (t, 0)
  let v : ℝ × W := (1, 0)
  have hcal := hF.tubeCoordinateEnergy_calibrated_identities Y D.smooth D.smooth_symm
    D.timeOrigin D.coe_eq D.energy_eq D.covector_le (D.stay t ht)
  have hunit := (F.tubeCoordinate_timeColumn_unit D.smooth D.coe_eq D.energy_eq (D.stay t ht)).2
  have hh := hF.tubeLengthMomentum_parameter_fderiv_of_unit D.smooth D.smooth_symm
    (Z := fun z : ℝ × W ↦ (q, z)) (p₀ := v)
    ((show ContDiffAt ℝ ∞ (fun z : ℝ × W ↦ (q, z)) v from
      contDiffAt_const.prodMk contDiffAt_id).differentiableAt (by simp))
    (show (q, v) ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} from ⟨D.stay t ht, by simp [v]⟩)
    hunit (ξ : ℝ × W)
  change fderiv ℝ (fderiv ℝ (fun z ↦ F.tubeCoordinateLength Y (q, z))) v ξ =
    fderiv ℝ (fderiv ℝ (fun z ↦ F.tubeCoordinateEnergy Y (q, z))) v ξ -
      (fderiv ℝ (fun z ↦ F.tubeCoordinateLength Y (q, z)) v ξ) •
        fiberLegendre (F.tubeCoordinateEnergy Y) (q, v) at hh
  rw [hcal.1, show p (ξ : ℝ × W) = 0 from ξ.property, zero_smul, sub_zero] at hh
  change 0 < fderiv ℝ (fderiv ℝ (fun z ↦ F.tubeCoordinateLength Y (q, z))) v ξ ξ
  rw [hh]
  exact hF.tubeCoordinateEnergy_fiber_hessian_pos D.smooth D.smooth_symm (D.stay t ht)
    (by simp [v]) (fun hz ↦ hξ (Subtype.ext hz))

include D in
/-- The true restricted inverse response is continuous on the actual closed segment. -/
theorem continuousOn_lengthKernelResponse (hF : F.IsSmoothStronglyConvex) :
    ContinuousOn (fun t : ℝ ↦ D.lengthKernelResponse t) (Icc a b) := by
  let Y := D.toOpenPartialHomeomorph
  let p := ContinuousLinearMap.fst ℝ ℝ W
  intro t ht
  let z : (ℝ × W) × (ℝ × W) := ((t, 0), (1, 0))
  have hz : z ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} := ⟨D.stay t ht, by simp [z]⟩
  have hL : ContDiffAt ℝ ∞ (F.tubeCoordinateLength Y) z :=
    (hF.contDiffOn_tubeCoordinateLength Y D.smooth D.smooth_symm).contDiffAt
      ((Y.open_source.prod isOpen_ne).mem_nhds hz)
  have hH : ContDiffAt ℝ ∞ (fun q : (ℝ × W) × (ℝ × W) ↦
      fderiv ℝ (fderiv ℝ (fun v ↦ F.tubeCoordinateLength Y (q.1, v))) q.2) z := by
    apply ContDiffAt.fderiv (n := ∞) (m := ∞)
      (g := fun q : (ℝ × W) × (ℝ × W) ↦ q.2)
      (f := fun q v ↦ fderiv ℝ (fun y ↦ F.tubeCoordinateLength Y (q.1, y)) v)
      _ contDiffAt_snd (by simp)
    exact (contDiffAt_fiberLegendre hL).comp (z, z.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hK : ContDiffAt ℝ ∞ (F.tubeLengthKernelHessian Y p) z :=
    contDiffAt_const.clm_comp (hH.clm_comp contDiffAt_const)
  have hinv : (D.lengthKernelHessian t).IsInvertible :=
    ⟨positive_dualMap_equiv _ (D.lengthKernelHessian_pos hF ht), rfl⟩
  have hKi : ContDiffAt ℝ ∞ (fun q ↦ (F.tubeLengthKernelHessian Y p q).inverse) z :=
    (hinv.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp z hK
  exact (hKi.continuousAt.comp (f := fun r : ℝ ↦ ((r, (0 : W)), (1, (0 : W))))
    ((continuousAt_id.prodMk continuousAt_const).prodMk continuousAt_const)).continuousWithinAt

/-- The actual inverse response is positive under the canonical dual pairing. -/
theorem lengthKernelResponse_pos (hF : F.IsSmoothStronglyConvex)
    {t : ℝ} (ht : t ∈ Icc a b)
    (p : (ContinuousLinearMap.fst ℝ ℝ W).ker →L[ℝ] ℝ) (hp : p ≠ 0) :
    0 < p (D.lengthKernelResponse t p) := by
  let e := positive_dualMap_equiv _ (D.lengthKernelHessian_pos hF ht)
  change 0 < p ((D.lengthKernelHessian t).inverse p)
  rw [show (D.lengthKernelHessian t).inverse = e.symm.toContinuousLinearMap from
    ContinuousLinearMap.inverse_equiv e]
  have hpos := D.lengthKernelHessian_pos hF ht (e.symm p)
    (e.symm.map_eq_zero_iff.not.mpr hp)
  change 0 < e (e.symm p) (e.symm p) at hpos
  simpa only [e.apply_symm_apply, ContinuousLinearEquiv.coe_coe] using! hpos

omit [FiniteDimensional ℝ W] in
/-- The coefficient's genuine operator integral is the integral of these same responses. -/
theorem lengthKernelCompliance_eq_response :
    F.tubeLengthKernelCompliance D.toOpenPartialHomeomorph
      (ContinuousLinearMap.fst ℝ ℝ W) (Λ 0) a b =
      endpointCompliance D.lengthKernelResponse a b := by
  apply endpointCompliance_congr_on D.ordered.le
  intro t ht
  dsimp only [tubeLengthKernelCompliance, lengthKernelResponse, lengthKernelHessian]
  rw [D.coordinatePhase ht]

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedTube
