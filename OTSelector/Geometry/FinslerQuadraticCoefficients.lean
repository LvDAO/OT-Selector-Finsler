import OTSelector.Geometry.FinslerPolynomialPhaseModel
import OTSelector.Geometry.FinslerTubeKernelCompliance

/-!
# Actual polynomial and length-kernel quadratic coefficients

Both coefficients scale quadratically in their label increments. In a calibrated
tube, the integrated restricted length Hessian yields the same coefficient as the
actual endpoint energy compliance.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

/-- Pulling a bilinear Hessian back by the actual linear label derivative gives
an exactly homogeneous quadratic function, without extra regularity assumptions. -/
theorem stationaryLabelQuadratic_smul
    {P Q Z W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : P × Z → ℝ) (g : Q × W → Z) (p : P) (q : Q) (z : Z)
    (a : ℝ) (w : W) :
    stationaryLabelQuadratic f g p q z (a • w) =
      a ^ 2 * stationaryLabelQuadratic f g p q z w := by
  let d := fderiv ℝ g (q, 0) (0, w)
  have hinput : ((0, a • w) : Q × W) = a • (0, w) := by simp
  have hd : fderiv ℝ g (q, 0) (0, a • w) = a • d := by
    rw [hinput, map_smul]
  have hstate : ((0, a • d) : P × Z) = a • (0, d) := by simp
  unfold stationaryLabelQuadratic
  dsimp only
  rw [hd, hstate, map_smul]
  simp only [_root_.smul_apply, _root_.map_smul, smul_eq_mul]
  dsimp only [d]
  ring

namespace ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual integrated length-response coefficient of the difference between
the two endpoint labels, restricted to the kernel of the tube time covector. -/
def tubeLengthQuadratic (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph (ℝ × W) M) (c : ℝ → M)
    (a b : ℝ) (w : W × W) : ℝ :=
  let p := ContinuousLinearMap.fst ℝ ℝ W
  let ξ : p.ker := ⟨(0, w.2 - w.1), by simp [p]⟩
  (1 / 2 : ℝ) * (F.tubeLengthKernelCompliance Y p c a b).inverse ξ ξ

/-- The actual polynomial-phase coefficient is exactly quadratic in its labels. -/
theorem polynomialPhaseQuadratic_smul (F : ContinuousFinslerNorm E M) (old : M)
    (Φ : (E × E) → ℝ → M)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (σ : ScalarSecondJet E × W → E)
    (j : ScalarSecondJet E) (t : ℝ × ℝ) (a : ℝ) (w : W × W) :
    F.polynomialPhaseQuadratic old Φ eL σ j t (a • w) =
      a ^ 2 * F.polynomialPhaseQuadratic old Φ eL σ j t w := by
  exact stationaryLabelQuadratic_smul (P := ScalarSecondJet E × (ℝ × ℝ))
    (Q := ScalarSecondJet E) (Z := (E × E) × (E × E))
    (F.parameterizedPhaseLengthAction old Φ) (F.polynomialPhasePair old eL σ)
    (j, t) j (eL.symm (j.1, j.2.2.1), eL.symm (j.1, j.2.2.1)) a w

/-- The actual length-kernel coefficient is exactly quadratic in its labels. -/
theorem tubeLengthQuadratic_smul (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph (ℝ × W) M) (c : ℝ → M)
    (a b s : ℝ) (w : W × W) :
    F.tubeLengthQuadratic Y c a b (s • w) =
      s ^ 2 * F.tubeLengthQuadratic Y c a b w := by
  let p := ContinuousLinearMap.fst ℝ ℝ W
  let ξ : W × W → p.ker := fun w ↦ ⟨(0, w.2 - w.1), by simp [p]⟩
  have hξ : ξ (s • w) = s • ξ w := by
    apply Subtype.ext
    simp [ξ, smul_sub]
  change (1 / 2 : ℝ) * (F.tubeLengthKernelCompliance Y p c a b).inverse
    (ξ (s • w)) (ξ (s • w)) =
    s ^ 2 * ((1 / 2 : ℝ) * (F.tubeLengthKernelCompliance Y p c a b).inverse (ξ w) (ξ w))
  rw [hξ, _root_.map_smul]
  simp only [_root_.smul_apply, _root_.map_smul, smul_eq_mul]
  ring

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  {F : ContinuousFinslerNorm E M}

/-- The actual integrated restricted-length coefficient equals the actual endpoint
energy-compliance coefficient in the same calibrated tube and on the same curve. -/
theorem tubeLengthQuadratic_eq_endpointCompliance
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
    {a b : ℝ} (hab : a < b) {v : W}
    (hstay : ∀ t ∈ Icc a b, (t, v) ∈ Y.source) (w : W × W) :
    F.tubeLengthQuadratic Y (Λ v) a b w =
      (1 / 2 : ℝ) * (F.tubeEndpointCompliance Y (Λ v) a b).inverse
        (0, w.2 - w.1) (0, w.2 - w.1) := by
  have hcoef := hF.tubeEndpointCompliance_inverse_on_timeKernel
    hY hi heq hhalf t₀ hbound hab hstay (w.2 - w.1) (w.2 - w.1)
  exact congrArg (fun r : ℝ ↦ (1 / 2 : ℝ) * r) hcoef.symm

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry
