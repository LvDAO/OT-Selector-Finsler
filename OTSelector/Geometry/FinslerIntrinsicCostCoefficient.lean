import OTSelector.Geometry.FinslerIntrinsicCostCoefficientResponse
import OTSelector.Geometry.FinslerTubeLengthQuadraticRemainder

/-!
# The actual distance coefficient as an intrinsic compliance integral

The original tube coefficient is the inverse of the integral of one intrinsic
label kernel in the original time variable. The fixed label basis is explicit,
and the actual distance remainder consequently uses this same matrix coefficient.
-/

open Set Filter MeasureTheory Matrix Module Manifold Asymptotics
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original-time integral of the intrinsic inverse label Hessian determines
this quadratic coefficient of the difference between endpoint labels. -/
def intrinsicLengthQuadratic (F : ContinuousFinslerNorm E M) (bW : Basis ι ℝ W)
    (Γ : W → ℝ → M) (w₀ : W) (a b : ℝ) (w : W × W) : ℝ :=
  (1 / 2 : ℝ) * (bW.equivFun (w.2 - w.1) ⬝ᵥ
    ((∫ t in a..b, (F.familyLabelHessianMatrix bW
      (fun q ↦ Γ q.1 q.2) (w₀, t))⁻¹)⁻¹ *ᵥ bW.equivFun (w.2 - w.1)))

namespace CalibratedTube

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}
  {Λ : W → ℝ → M} {a b : ℝ} {u : M → ℝ}
  (D : F.CalibratedTube Λ a b u)

/-- The actual tube response matrix is the intrinsic label Hessian inverse of the same family. -/
theorem lengthKernelResponse_matrix (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) {t : ℝ} (ht : t ∈ Icc a b) :
    hamiltonianMatrixC (timeKernelBasis bW) (D.lengthKernelResponse t) =
      (F.familyLabelHessianMatrix bW (fun q ↦ Λ q.1 q.2) (0, t))⁻¹ := by
  rw [lengthKernelResponse,
    ← hamiltonianMatrixA_inverse (timeKernelBasis bW) (D.lengthKernelHessian t)
      (D.lengthKernelHessian_pos hF ht)]
  have hh := hF.tubeLengthKernelHessian_matrix_eq_intrinsic D.smooth D.smooth_symm
    bW (D.stay t ht)
  rw [D.coe_eq] at hh
  exact congrArg Inv.inv hh

/-- The actual original-distance coefficient equals the inverse integral of the
same intrinsic label kernel, without changing the time parameter or label basis. -/
theorem quadratic_eq_intrinsicLengthQuadratic (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) (w : W × W) :
    D.quadratic w = F.intrinsicLengthQuadratic bW Λ 0 a b w := by
  let ξ : (ContinuousLinearMap.fst ℝ ℝ W).ker :=
    ⟨(0, w.2 - w.1), by simp⟩
  have hcoef := endpointCompliance_inverse_pairing_matrix (timeKernelBasis bW)
    D.ordered (D.continuousOn_lengthKernelResponse hF)
    (fun t ht p hp ↦ D.lengthKernelResponse_pos hF ht p hp) ξ ξ
  have hIntegral : (∫ t in a..b, hamiltonianMatrixC (timeKernelBasis bW)
      (D.lengthKernelResponse t)) = ∫ t in a..b,
      (F.familyLabelHessianMatrix bW (fun q ↦ Λ q.1 q.2) (0, t))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact D.lengthKernelResponse_matrix hF bW (by simpa only [uIcc_of_le D.ordered.le] using ht)
  rw [hIntegral] at hcoef
  have hcoords : (timeKernelBasis bW).equivFun ξ = bW.equivFun (w.2 - w.1) := rfl
  rw [hcoords] at hcoef
  change (1 / 2 : ℝ) * (F.tubeLengthKernelCompliance D.toOpenPartialHomeomorph
    (ContinuousLinearMap.fst ℝ ℝ W) (Λ 0) a b).inverse ξ ξ = _
  rw [D.lengthKernelCompliance_eq_response, hcoef]
  rfl

include D in
/-- The same actual distance deficit has this intrinsic matrix coefficient as its
second-order expansion; every tube and calibration input is retained. -/
theorem distance_sub_intrinsicLengthQuadratic_isLittleO
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hΛ : F.IsEulerLagrangeOn (Λ 0) univ) (bW : Basis ι ℝ W) :
    (fun w : W × W ↦
      (F.lengthEDist (Λ w.1 a) (Λ w.2 b)).toReal - (b - a) -
        F.intrinsicLengthQuadratic bW Λ 0 a b w) =o[𝓝 (0 : W × W)] fun w ↦ ‖w‖ ^ 2 := by
  have hh := hF.selected_tube_distance_sub_lengthQuadratic_isLittleO hcomplete
    D.smooth D.smooth_symm D.coe_eq D.energy_eq D.timeOrigin D.covector_le
    D.ordered hΛ D.stay D.minimizing hu D.saturation D.differentiable
  simpa only [zero_add, ← D.quadratic_eq_intrinsicLengthQuadratic hF bW, quadratic] using! hh

end CalibratedTube
end OTSelector.Geometry.ContinuousFinslerNorm
