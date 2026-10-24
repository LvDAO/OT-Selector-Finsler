import OTSelector.Geometry.FinslerIntrinsicKernelOriginal
import OTSelector.Geometry.FinslerCalibratedTubeData

/-!
# The tube coefficient uses the intrinsic label Hessian

The canonical time kernel is the actual label space. Its restricted tube length
Hessian, read in the transported label basis, is exactly the intrinsic Hessian of
the same family. Both derivatives are taken through the genuine tube tangent map.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {E V W ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual label space identifies canonically with the kernel of the time covector. -/
def timeKernelEquiv : W ≃L[ℝ] (ContinuousLinearMap.fst ℝ ℝ W).ker := by
  let e : W ≃ₗ[ℝ] (ContinuousLinearMap.fst ℝ ℝ W).ker := {
    toFun := fun w ↦ ⟨(0, w), by simp⟩
    invFun := fun v ↦ v.1.2
    map_add' := by intros; apply Subtype.ext; simp
    map_smul' := by intros; apply Subtype.ext; simp
    left_inv := fun _ ↦ rfl
    right_inv := by intro v; apply Subtype.ext; exact Prod.ext v.property.symm rfl }
  exact {
    toLinearEquiv := e
    continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk
      (fun w ↦ show (ContinuousLinearMap.fst ℝ ℝ W) (0, w) = 0 from rfl)
    continuous_invFun := continuous_subtype_val.snd }

/-- The fixed label basis in the true time kernel. -/
def timeKernelBasis (bW : Basis ι ℝ W) :
    Basis ι ℝ (ContinuousLinearMap.fst ℝ ℝ W).ker :=
  bW.map (timeKernelEquiv (W := W)).toLinearEquiv

/-- The second derivative transforms under a genuine linear change of model space. -/
theorem fderiv2_comp_linearEquiv_models {L : E → ℝ} (A : V ≃L[ℝ] E) {v : V}
    (h2 : DifferentiableAt ℝ (fderiv ℝ L) (A v)) (u w : V) :
    fderiv ℝ (fderiv ℝ (L ∘ A)) v u w =
      fderiv ℝ (fderiv ℝ L) (A v) (A u) (A w) := by
  have hfirst : fderiv ℝ (L ∘ A) = fun x ↦ (fderiv ℝ L (A x)).comp
      A.toContinuousLinearMap := by
    funext x
    exact A.comp_right_fderiv
  rw [hfirst]
  have hsecond := (h2.hasFDerivAt.comp v A.hasFDerivAt).clm_comp
    (hasFDerivAt_const A.toContinuousLinearMap v)
  have hs := hsecond.fderiv
  simp only [Function.comp_def] at hs
  rw [hs]
  simp

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The actual tube length Hessian is the original fiber-model length Hessian under
the true tangent equivalence, allowing different source and manifold model spaces. -/
theorem tubeCoordinateLength_fiber_hessian (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {q v : V} (hq : q ∈ Y.source) (hv : v ≠ 0) (u w : V) :
    let A := (tangentFiberModelEquiv (Y q)).symm.toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q)
    fderiv ℝ (fderiv ℝ (fun η ↦ F.tubeCoordinateLength Y (q, η))) v u w =
      fderiv ℝ (fderiv ℝ (fun η : E ↦
        (F.toFun ⟨Y q, tangentFiberModelEquiv (Y q) η⟩ : ℝ))) (A v) (A u) (A w) := by
  have hd : Y.MDifferentiable 𝓘(ℝ, V) 𝓘(ℝ, E) :=
    ⟨hY.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩
  let A : V ≃L[ℝ] E := (hd.mfderiv hq).trans (tangentFiberModelEquiv (Y q)).symm
  let L : E → ℝ := fun η ↦ (F.toFun ⟨Y q, tangentFiberModelEquiv (Y q) η⟩ : ℝ)
  have heq : (fun η ↦ F.tubeCoordinateLength Y (q, η)) = L ∘ A := by
    funext η
    rfl
  have hTube : ContDiffAt ℝ ∞ (fun η ↦ F.tubeCoordinateLength Y (q, η)) v :=
    ((hF.contDiffOn_tubeCoordinateLength Y hY hi).contDiffAt
      ((Y.open_source.prod isOpen_ne).mem_nhds
        (show (q, v) ∈ Y.source ×ˢ {v : V | v ≠ 0} from ⟨hq, hv⟩))).comp v
        (f := fun η : V ↦ (q, η)) (contDiffAt_const.prodMk contDiffAt_id)
  have hL : ContDiffAt ℝ ∞ L (A v) := by
    have hTube' : ContDiffAt ℝ ∞ (fun η ↦ F.tubeCoordinateLength Y (q, η))
        (A.symm (A v)) := by simpa only [A.symm_apply_apply] using! hTube
    have hh := hTube'.comp (A v) A.symm.contDiff.contDiffAt
    simpa only [heq, Function.comp_def, A.apply_symm_apply] using! hh
  rw [heq, fderiv2_comp_linearEquiv_models A
    ((hL.fderiv_right (m := 1) (by simp)).differentiableAt_one)]
  rfl

/-- In the actual label basis the restricted tube Hessian is precisely the intrinsic
label Hessian of the very same tube family. -/
theorem tubeLengthKernelHessian_matrix_eq_intrinsic
    (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph (ℝ × W) M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (bW : Basis ι ℝ W) {q : ℝ × W} (hq : q ∈ Y.source) :
    hamiltonianMatrixA (timeKernelBasis bW)
      (F.tubeLengthKernelHessian Y (ContinuousLinearMap.fst ℝ ℝ W) (q, (1, 0))) =
      F.familyLabelHessianMatrix bW (fun z : W × ℝ ↦ Y (z.2, z.1)) (q.2, q.1) := by
  let S := ContinuousLinearEquiv.prodComm ℝ W ℝ
  have hYat : MDifferentiableAt 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y q :=
    (hY.contMDiffAt (Y.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) (fun z : W × ℝ ↦ Y (z.2, z.1))
      (q.2, q.1) = (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y q).comp
        S.toContinuousLinearMap := by
    have hh := mfderiv_comp (q.2, q.1) hYat S.hasFDerivAt.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv, S.hasFDerivAt.fderiv] at hh
    exact hh
  ext i j
  have hh := hF.tubeCoordinateLength_fiber_hessian hY hi hq
    (show ((1, 0) : ℝ × W) ≠ 0 by simp) (0, bW j) (0, bW i)
  simpa only [hamiltonianMatrixA, timeKernelBasis, Basis.map_apply,
    timeKernelEquiv, LinearEquiv.coe_mk, ContinuousLinearEquiv.coe_coe,
    tubeLengthKernelHessian, familyLabelHessianMatrix, hd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.prodComm_apply, S] using! hh

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
