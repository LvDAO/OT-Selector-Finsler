import OTSelector.Analysis.ODE.Hamiltonian.SmoothEndpointGerm
import OTSelector.Reconstruction.ClosedJacobiConditionalMoments
import OTSelector.Geometry.FocalSmoothPole

/-!
# Rank of the actual endpoint inverse residue

The already constructed smooth Hamiltonian endpoint germ supplies the actual inverse
pole. Its residue rank equals the nullity of the unchanged original endpoint position
matrix. This is a strengthening of the actual germ interface, not an additional crossing
or smoothness condition.
-/

open Set Filter Matrix Metric
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The genuine closed-system endpoint inverse pole has the genuine endpoint nullity. -/
theorem ClosedHamiltonianJacobiSystem.exists_actual_left_inverse_pole_rank
    {J P A B C : ℝ→Matrix n n ℝ} {a b : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b) (hab : a<b)
    {U : Set ℝ} (hU : IsOpen U) (haU : a∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U)
    (hCs : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ (R : Matrix n n ℝ) (Brem : ℝ→Matrix n n ℝ),
      ContDiffOn ℝ ∞ Brem (Ioo (-ε) ε) ∧
      R.rank=Module.finrank ℝ (LinearMap.ker (J a).mulVecLin) ∧
      ∀s∈Ioo 0 ε, (J (a+s))⁻¹=s⁻¹•R+Brem s := by
  have ha : a∈Icc a b := ⟨le_rfl,hab.le⟩
  obtain ⟨δ,hδ,hδb,Jbar,Pbar,hJa,hPa,_,hJs,_,hJeq,_,hJODE⟩ :=
    exists_smooth_hamiltonian_leftEndpoint_germ hab
      (fun t ht ↦ (H.position_derivative t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (H.momentum_derivative t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ H.position_derivative t (Ioo_subset_Icc_self ht))
      (fun t ht ↦ H.momentum_derivative t (Ioo_subset_Icc_self ht)) hU haU hAs hBs hCs
  have hJshift : ContDiffOn ℝ ∞ (fun s ↦ Jbar (a+s)) (Ioo (-δ) δ) :=
    hJs.comp (contDiffOn_const.add contDiffOn_id)
      (fun s hs ↦ ⟨by linarith [hs.1],by linarith [hs.2]⟩)
  have hda := (hJODE a (show a∈Ioo (a-δ) (a+δ) from ⟨by linarith,by linarith⟩)).1
  have hda0 : HasDerivAt Jbar (B a*Jbar a+C a*Pbar a) (a+(0:ℝ)) := by
    simpa only [add_zero] using hda
  have hdshift : HasDerivAt (fun s ↦ Jbar (a+s)) (B a*Jbar a+C a*Pbar a) 0 := by
    simpa only [Function.comp_def,add_zero,one_smul] using
      hda0.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add a)
  have hcross : ∀u, Jbar (a+0)*ᵥu=0 →
      deriv (fun s ↦ Jbar (a+s)) 0*ᵥu∈LinearMap.range (Jbar (a+0)).mulVecLin → u=0 := by
    intro u hu hrange
    rw [hdshift.deriv,hJa,hPa] at hrange
    simp only [add_zero,hJa] at hu hrange
    exact focal_crossing_kernel_eq_zero (H.wronskian a ha) (H.phase_rank a ha)
      (H.positive_C a ha) hu hrange
  obtain ⟨V,R,Brem,hV,h0,_,hBrem,hpole,hrank,_⟩ := exists_smooth_focal_inverse_pole
    isOpen_Ioo (show (0:ℝ)∈Ioo (-δ) δ from ⟨by linarith,hδ⟩) hJshift hcross
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let ε := min (r/2) δ
  have hε : 0<ε := lt_min (half_pos hr) hδ
  have hεr : ε<r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hεδ : ε≤δ := min_le_right _ _
  have hεV : Ioo (-ε) ε ⊆ V := by
    intro s hs
    apply hrV
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith [hs.1,hs.2]
  refine ⟨ε,hε,hεδ.trans_lt hδb,R,Brem,hBrem.mono hεV,?_,fun s hs ↦ ?_⟩
  · change R.rank=Module.finrank ℝ (LinearMap.ker (Jbar (a+0)).mulVecLin) at hrank
    rw [add_zero,hJa] at hrank
    exact hrank
  · have hsV := hεV (show s∈Ioo (-ε) ε from ⟨by linarith [hs.1],hs.2⟩)
    have hsJ : a+s∈Ioo a (a+δ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    simpa only [hJeq hsJ] using (hpole s hsV (ne_of_gt hs.1)).2

end OTSelector.Reconstruction
