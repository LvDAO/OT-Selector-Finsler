import OTSelector.Reconstruction.ActualJacobiInversePoleRank
import OTSelector.Reconstruction.ActualJacobiKernelDoublePole
import OTSelector.Analysis.Asymptotics.DoublePoleResidueGram

/-!
# Actual focal mobility rank equals actual Jacobi nullity

The fixed leading coefficient of any genuine smooth double-pole expansion is identified
with the same actual inverse residue and the actual positive endpoint Hamiltonian weight.
Thus its rank is exactly the original endpoint nullity. The existing actual double-pole
producer can retain that rank information without changing the original kernel.
-/

open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every actual mobility double-pole residue has the original endpoint Jacobi nullity. -/
theorem ClosedHamiltonianJacobiSystem.actual_left_kernel_doublePole_rank
    {J P A B C : ℝ→Matrix n n ℝ} {a b : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b) (hab : a<b)
    {U : Set ℝ} (hU : IsOpen U) (haU : a∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U)
    (hCs : ContDiffOn ℝ ∞ C U)
    {ε : ℝ} (hε : 0<ε) {G : Matrix n n ℝ} {Rem : ℝ→Matrix n n ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀s∈Ioo 0 ε,
      (J (a+s))⁻¹*C (a+s)*(J (a+s))⁻¹ᵀ=(s^2)⁻¹•G+Rem s) :
    G.rank=Module.finrank ℝ (LinearMap.ker (J a).mulVecLin) := by
  obtain ⟨δ,hδ,_,R,Brem,hBrem,hrank,hinv⟩ :=
    H.exists_actual_left_inverse_pole_rank hab hU haU hAs hBs hCs
  have ηpos : 0<min ε δ := lt_min hε hδ
  have hC : ContinuousAt (fun s ↦ C (a+s)) 0 := by
    have hCa : ContinuousAt C (a+(0:ℝ)) := by
      simpa only [add_zero] using hCs.continuousOn.continuousAt (hU.mem_nhds haU)
    exact hCa.comp (continuousAt_const.add continuousAt_id)
  have hb := hBrem.continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hδ)
  have heq : G.rank=R.rank := doublePole_residue_rank_eq_inverseResidue ηpos hC hb hRem
    (by simpa only [add_zero] using H.positive_C a (show a∈Icc a b from ⟨le_rfl,hab.le⟩))
    (fun s hs ↦ hinv s ⟨hs.1,hs.2.trans_le (min_le_right ε δ)⟩)
    (fun s hs ↦ hpole s ⟨hs.1,hs.2.trans_le (min_le_left ε δ)⟩)
  exact heq.trans hrank

/-- The existing genuine mobility pole producer retains its exact original endpoint rank. -/
theorem ClosedHamiltonianJacobiSystem.exists_actual_left_kernel_double_pole_rank
    {J P A B C : ℝ→Matrix n n ℝ} {a b c : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀t∈Ioo a b, (J t).det≠0) (hc : c∈Ioo a b)
    {U : Set ℝ} (hU : IsOpen U) (haU : a∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U)
    (hCs : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ (G : Matrix n n ℝ) (Rem : ℝ→Matrix n n ℝ),
      ContDiffOn ℝ ∞ Rem (Ioo (-ε) ε) ∧
      G.rank=Module.finrank ℝ (LinearMap.ker (J a).mulVecLin) ∧ ∀s∈Ioo 0 ε,
        (J (a+s))⁻¹*C (a+s)*(J (a+s))⁻¹ᵀ=(s^2)⁻¹•G+Rem s := by
  obtain ⟨ε,hε,hεb,G,Rem,hRem,hpole⟩ :=
    H.exists_actual_left_kernel_double_pole hd hc hU haU hAs hBs hCs
  exact ⟨ε,hε,hεb,G,Rem,hRem,H.actual_left_kernel_doublePole_rank
    (hc.1.trans hc.2) hU haU hAs hBs hCs hε
    (hRem.continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hε)) hpole,hpole⟩

end OTSelector.Reconstruction
