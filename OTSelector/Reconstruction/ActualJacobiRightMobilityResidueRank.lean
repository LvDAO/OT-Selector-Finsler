import OTSelector.Reconstruction.ActualJacobiMobilityResidueRank
import OTSelector.Reconstruction.ActualJacobiKernelRightDoublePole

/-!
# Rank of the actual right focal mobility residue

The same symplectic reflection transfers the actual left rank identity to the actual
right endpoint, retaining the unchanged original endpoint position matrix.
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

/-- Every true right mobility residue has the original right endpoint Jacobi nullity. -/
theorem ClosedHamiltonianJacobiSystem.actual_right_kernel_doublePole_rank
    {J P A B C : ℝ→Matrix n n ℝ} {a b : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b) (hab : a<b)
    {U : Set ℝ} (hU : IsOpen U) (hbU : b∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U)
    (hCs : ContDiffOn ℝ ∞ C U)
    {ε : ℝ} (hε : 0<ε) {G : Matrix n n ℝ} {Rem : ℝ→Matrix n n ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀s∈Ioo 0 ε,
      (J (b-s))⁻¹*C (b-s)*(J (b-s))⁻¹ᵀ=(s^2)⁻¹•G+Rem s) :
    G.rank=Module.finrank ℝ (LinearMap.ker (J b).mulVecLin) := by
  let V := (fun t : ℝ ↦ b-t) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.sub continuous_id)
  have h0V : (0:ℝ)∈V := by simpa only [V,mem_preimage,sub_zero] using hbU
  have hmaps : MapsTo (fun t : ℝ ↦ b-t) V U := fun _ ht ↦ ht
  have hA := hAs.comp (contDiffOn_const.sub contDiffOn_id) hmaps
  have hB := (hBs.comp (contDiffOn_const.sub contDiffOn_id) hmaps).neg
  have hC := hCs.comp (contDiffOn_const.sub contDiffOn_id) hmaps
  have h := H.reflect_at_right.actual_left_kernel_doublePole_rank (sub_pos.mpr hab)
    hV h0V hA hB hC hε hRem
    (fun s hs ↦ by simpa only [zero_add] using hpole s hs)
  change G.rank=Module.finrank ℝ (LinearMap.ker (J (b-0)).mulVecLin) at h
  rw [sub_zero] at h
  exact h

/-- The actual right pole producer can retain this exact endpoint rank internally. -/
theorem ClosedHamiltonianJacobiSystem.exists_actual_right_kernel_double_pole_rank
    {J P A B C : ℝ→Matrix n n ℝ} {a b c : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀t∈Ioo a b, (J t).det≠0) (hc : c∈Ioo a b)
    {U : Set ℝ} (hU : IsOpen U) (hbU : b∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U)
    (hCs : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ (G : Matrix n n ℝ) (Rem : ℝ→Matrix n n ℝ),
      ContDiffOn ℝ ∞ Rem (Ioo (-ε) ε) ∧
      G.rank=Module.finrank ℝ (LinearMap.ker (J b).mulVecLin) ∧ ∀s∈Ioo 0 ε,
        (J (b-s))⁻¹*C (b-s)*(J (b-s))⁻¹ᵀ=(s^2)⁻¹•G+Rem s := by
  obtain ⟨ε,hε,hεb,G,Rem,hRem,hpole⟩ :=
    H.exists_actual_right_kernel_double_pole hd hc hU hbU hAs hBs hCs
  exact ⟨ε,hε,hεb,G,Rem,hRem,H.actual_right_kernel_doublePole_rank
    (hc.1.trans hc.2) hU hbU hAs hBs hCs hε
    (hRem.continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hε)) hpole,hpole⟩

end OTSelector.Reconstruction
