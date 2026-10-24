import OTSelector.Reconstruction.OriginalFinslerKernelLeftDoublePole
import OTSelector.Reconstruction.FinslerConcreteUpperModel
import OTSelector.Reconstruction.PositiveComplianceBounds
import Mathlib.Algebra.Order.Star.Real

/-!
# Whole-span lower bound of the actual original Finsler mobility

The same comparison's original length Hessian is continuous on the entire compact support
span, including focal endpoints. Its quadratic upper bound therefore yields a uniform
positive lower bound for its inverse at every regular interior clock. No inverse endpoint
value or nonfocal endpoint assumption is used.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- An ordinary fixed-coordinate quadratic upper bound is exactly an upper Loewner bound. -/
theorem posSemidef_scalar_identity_sub_of_quadratic_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {M : ℝ}
    (hM : 0<M) (hA : A.IsHermitian)
    (hquad : ∀v : ι→ℝ, v⬝ᵥ(A*ᵥv)≤M*∑i,v i^2) : (M•1-A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.PosDef.one.smul hM).isHermitian.sub hA)
  intro v
  have hb := hquad v
  have heq : v⬝ᵥv=∑i,v i^2 := by simp only [dotProduct,pow_two]
  simpa only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul,heq,sub_nonneg] using hb

/-- Inversion of a genuine positive coefficient upper bound yields the required mobility
lower bound, without an independently supplied inverse norm. -/
theorem posSemidef_inverse_sub_scalar_identity_of_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {M : ℝ}
    (hM : 0<M) (hA : A.PosDef) (hupper : (M•1-A).PosSemidef) :
    (A⁻¹-M⁻¹•1).PosSemidef := by
  let _ : Invertible M := invertibleOfNonzero hM.ne'
  have hb := posSemidef_inverse_sub_inverse hA (Matrix.PosDef.one.smul hM) hupper
  rw [Matrix.inv_smul (1 : Matrix ι ι ℝ) M (by simp),inv_one,invOf_eq_inv] at hb
  exact hb

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original mobility has a single uniform positive lower bound throughout its
whole regular open support span. Focal endpoints are allowed and are not inverted. -/
theorem exists_original_kernel_wholeSpan_uniform_lower
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ κ : ℝ, κ>0 ∧ ∀t∈Ioo D.lo D.hi,
      (originalSeedKernel S w t-κ•1).PosSemidef := by
  let bW := Module.finBasis ℝ S.covector.ker
  let H := fun t : ℝ ↦ F.familyLabelHessianMatrix bW
    (fun q ↦ D.comparison.curve q.1 q.2) (w,t)
  have hH : Continuous H := continuous_iff_continuousAt.mpr
    (fun t ↦ D.comparison.continuousAt_labelHessian hF bW t)
  have hKeq (t : ℝ) : originalSeedKernel S w t=(H t)⁻¹ :=
    congrFun (D.original_kernel_eq hF hw) t
  obtain ⟨C,hC,hbound⟩ := exists_compact_matrixQuadratic_sum_bound isCompact_Icc hH.continuousOn
  let M := 2*C+1
  have hM : 0<M := by dsimp [M]; linarith
  refine ⟨M⁻¹,inv_pos.mpr hM,fun t ht ↦ ?_⟩
  have hHi : (H t).PosDef := Matrix.posDef_inv_iff.mp (by
    rw [←hKeq t]
    exact (D.original_kernel_regular hF hw).2 t ht)
  have hupper : (M•1-H t).PosSemidef := by
    apply posSemidef_scalar_identity_sub_of_quadratic_upper hM hHi.isHermitian
    intro v
    have hq := hbound t (Ioo_subset_Icc_self ht) v
    have hs := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) ↦ sq_nonneg (v i))
    have hq' := (le_abs_self (matrixQuadratic (H t) v)).trans hq
    dsimp only [matrixQuadratic] at hq'
    dsimp only [M]
    nlinarith
  rw [hKeq t]
  exact posSemidef_inverse_sub_scalar_identity_of_upper hM hHi hupper

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
