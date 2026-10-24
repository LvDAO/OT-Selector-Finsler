import OTSelector.Reconstruction.ActualJacobiKernelDoublePole
import OTSelector.Geometry.JacobiComplianceReflection

/-!
# Actual right-endpoint mobility by symplectic time reflection

Reversing the original time and negating the same momentum preserves the positive
Hamiltonian velocity block. Applying the proved left-endpoint result to this unchanged
reflected system yields the actual right-endpoint double pole in inward distance.
-/

open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reversing actual time and negating actual momentum preserves all closed Hamiltonian
phase data, with positive C and the same complete rank. -/
theorem ClosedHamiltonianJacobiSystem.reflect_at_right
    {J P A B C : ℝ→Matrix n n ℝ} {a b : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b) :
    ClosedHamiltonianJacobiSystem (fun t ↦ J (b-t)) (fun t ↦ -P (b-t))
      (fun t ↦ A (b-t)) (fun t ↦ -B (b-t)) (fun t ↦ C (b-t)) 0 (b-a) := by
  have hmap : MapsTo (fun t : ℝ ↦ b-t) (Icc 0 (b-a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hclock : ContinuousOn (fun t : ℝ ↦ b-t) (Icc 0 (b-a)) := continuousOn_const.sub continuousOn_id
  refine {
    position_derivative := ?_
    momentum_derivative := ?_
    continuous_A := H.continuous_A.comp hclock hmap
    continuous_B := (H.continuous_B.comp hclock hmap).neg
    continuous_C := H.continuous_C.comp hclock hmap
    symmetric_A := fun t ht ↦ H.symmetric_A (b-t) (hmap ht)
    symmetric_C := fun t ht ↦ H.symmetric_C (b-t) (hmap ht)
    positive_C := fun t ht ↦ H.positive_C (b-t) (hmap ht)
    wronskian := ?_
    phase_rank := ?_ }
  · intro t ht
    have heq : (-B (b-t))*J (b-t)+C (b-t)*(-P (b-t)) =
        (-1:ℝ)•(B (b-t)*J (b-t)+C (b-t)*P (b-t)) := by
      simp only [Matrix.neg_mul,Matrix.mul_neg,neg_smul,one_smul]
      abel
    rw [heq]
    exact (H.position_derivative (b-t) (hmap ht)).scomp t ((hasDerivAt_id t).const_sub b)
  · intro t ht
    convert! (H.momentum_derivative (b-t) (hmap ht)).neg.scomp t
      ((hasDerivAt_id t).const_sub b) using 1
    simp only [neg_smul,one_smul,neg_neg,Matrix.transpose_neg,Matrix.neg_mul,Matrix.mul_neg]
  · intro t ht
    simp only [Matrix.mul_neg,Matrix.transpose_neg,Matrix.neg_mul]
    rw [H.wronskian (b-t) (hmap ht)]
  · intro t ht u hJu hPu
    apply H.phase_rank (b-t) (hmap ht) u hJu
    simpa only [Matrix.neg_mulVec,neg_eq_zero] using hPu

/-- The actual right endpoint has an exact inward-distance double pole plus a remainder
smooth through zero. Its coefficient regularity is the actual original right-endpoint data. -/
theorem ClosedHamiltonianJacobiSystem.exists_actual_right_kernel_double_pole
    {J P A B C : ℝ→Matrix n n ℝ} {a b c : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀ t∈Ioo a b, (J t).det≠0) (hc : c∈Ioo a b)
    {U : Set ℝ} (hU : IsOpen U) (hbU : b∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U) (hCs : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ (G : Matrix n n ℝ) (R : ℝ→Matrix n n ℝ),
      ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧ ∀ s∈Ioo 0 ε,
        (J (b-s))⁻¹*C (b-s)*(J (b-s))⁻¹ᵀ=(s^2)⁻¹•G+R s := by
  let V := (fun t : ℝ ↦ b-t) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.sub continuous_id)
  have h0V : (0:ℝ)∈V := by simpa only [V,mem_preimage,sub_zero] using hbU
  have hmaps : MapsTo (fun t : ℝ ↦ b-t) V U := fun _ ht ↦ ht
  have hA := hAs.comp (contDiffOn_const.sub contDiffOn_id) hmaps
  have hB := (hBs.comp (contDiffOn_const.sub contDiffOn_id) hmaps).neg
  have hC := hCs.comp (contDiffOn_const.sub contDiffOn_id) hmaps
  have hdref : ∀ t∈Ioo 0 (b-a), (J (b-t)).det≠0 := by
    intro t ht
    exact hd (b-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hcref : b-c∈Ioo 0 (b-a) := ⟨by linarith [hc.2],by linarith [hc.1]⟩
  obtain ⟨ε,hε,hεb,G,R,hR,hpole⟩ :=
    H.reflect_at_right.exists_actual_left_kernel_double_pole hdref hcref hV h0V hA hB hC
  exact ⟨ε,hε,by simpa only [sub_zero] using hεb,G,R,hR,
    fun s hs ↦ by simpa only [zero_add] using hpole s hs⟩

end OTSelector.Reconstruction
