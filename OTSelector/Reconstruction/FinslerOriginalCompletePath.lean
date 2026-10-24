import OTSelector.Reconstruction.FinslerOriginalClockOccupationPathMoment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The complete original compliance path

The actual original coefficient and full displacement determine one path between the unchanged
physical endpoints.  Its derivative is the original compliance velocity.  This module concerns
the exact complete path and does not assert the later traffic second-moment estimate.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The literal original path, anchored at the physical source, in the original physical clock. -/
def originalSeedCompletePath (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) (c : ℝ) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  x + (∫ r in (m.1.1 - S.level)..(c - S.level), originalSeedKernel S w r) *ᵥ
    originalSeedPairMomentum S w m

@[simp] theorem originalSeedCompletePath_source (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
    originalSeedCompletePath S w x m m.1.1 = x := by
  simp [originalSeedCompletePath]

/-- Matrix multiplication by a fixed vector is a continuous linear operation on matrices. -/
def completePathMatrixApply {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    Matrix ι ι ℝ →L[ℝ] (ι → ℝ) :=
  ({ toFun := fun A ↦ A *ᵥ p
     map_add' := fun A B ↦ Matrix.add_mulVec A B p
     map_smul' := fun c A ↦ by simp only [Matrix.smul_mulVec, RingHom.id_apply] } :
    Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)).toContinuousLinearMap

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every pair of interior clocks has an integrable original kernel between them. -/
theorem original_kernel_intervalIntegrable (hF : F.IsSmoothStronglyConvex)
    (hw : w ∈ S.labels) {a b : ℝ} (ha : a ∈ Ioo D.lo D.hi)
    (hb : b ∈ Ioo D.lo D.hi) : IntervalIntegrable (originalSeedKernel S w) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (D.original_kernel_regular hF hw).1.mono
  rcases le_total a b with hab | hba
  · simpa only [uIcc_of_le hab] using Icc_subset_Ioo ha.1 hb.2
  · simpa only [uIcc_of_ge hba] using Icc_subset_Ioo hb.1 ha.2

/-- The complete original path reaches the unchanged physical target. -/
theorem originalSeedCompletePath_target (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2) :
    originalSeedCompletePath S w x m m.1.2 = x + m.2 := by
  let A := ∫ r in (m.1.1 - S.level)..(m.1.2 - S.level), originalSeedKernel S w r
  have hp : A.PosDef := (D.pair_compliance_posDef hF hw ha hb hab).1
  let _ := hp.isUnit.invertible
  change x + A *ᵥ (A⁻¹ *ᵥ m.2) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- At every interior physical clock, the derivative is the actual original compliance
velocity, with no change of endpoint marks or displacement. -/
theorem hasDerivAt_originalSeedCompletePath (hF : F.IsSmoothStronglyConvex)
    (hw : w ∈ S.labels) (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c : ℝ}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hc : c - (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    HasDerivAt (originalSeedCompletePath S w x m)
      (originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m) c := by
  have hK := (D.original_kernel_regular hF hw).1
  have hcont : ContinuousAt (originalSeedKernel S w) (c - (S.level : ℝ)) :=
    hK.continuousAt (isOpen_Ioo.mem_nhds hc)
  have hprimitive := intervalIntegral.integral_hasDerivAt_right
    (D.original_kernel_intervalIntegrable hF hw ha hc)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hK _ hc) hcont
  have hshift := hprimitive.scomp c ((hasDerivAt_id c).sub_const (S.level : ℝ))
  have hvec := (completePathMatrixApply (originalSeedPairMomentum S w m)).hasFDerivAt
    |>.comp_hasDerivAt c hshift
  have hv : HasDerivAt (fun c ↦
      (∫ r in (m.1.1 - S.level)..(c - S.level), originalSeedKernel S w r) *ᵥ
        originalSeedPairMomentum S w m)
      (originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m) c := by
    simpa [completePathMatrixApply, Function.comp_def] using hvec
  exact hv.const_add x

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
