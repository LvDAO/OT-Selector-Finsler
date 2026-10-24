import OTSelector.Geometry.IntegralSecondSolutionSmoothGerm
import OTSelector.Reconstruction.ClosedJacobiConditionalMoments
import OTSelector.Geometry.FocalSmoothPole

/-!
# Simple pole of the actual Hamiltonian compliance primitive

Both the original Jacobi pair and its actual integral second solution acquire smooth
endpoint germs from their actual Hamiltonian equations. The regular crossing follows from
actual closed-system phase rank, Wronskian and positive C. Applying the proven smooth pole
factorization to these same germs gives a simple pole for the actual compliance primitive.
-/

open Set Filter Matrix Metric
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The unchanged compliance primitive has an exact left-endpoint simple pole with a
remainder smooth through zero. Smooth endpoint germs and the regular crossing are produced
internally; no smoothness or pole premise on the primitive or second solution is assumed. -/
theorem ClosedHamiltonianJacobiSystem.exists_actual_left_primitive_simple_pole
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀ t∈Ioo a b, (J t).det≠0) (hc : c∈Ioo a b)
    {U : Set ℝ} (hU : IsOpen U) (haU : a∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U) (hCs : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ (R : Matrix n n ℝ) (Brem : ℝ → Matrix n n ℝ),
      ContDiffOn ℝ ∞ Brem (Ioo (-ε) ε) ∧ ∀ s∈Ioo 0 ε,
        jacobiCompliancePrimitive J C c (a+s)=s⁻¹•R+Brem s := by
  have hab : a<b := hc.1.trans hc.2
  have ha : a∈Icc a b := ⟨le_rfl,hab.le⟩
  have hJ := fun t (ht : t∈Ioo a b) ↦ H.position_derivative t (Ioo_subset_Icc_self ht)
  have hP := fun t (ht : t∈Ioo a b) ↦ H.momentum_derivative t (Ioo_subset_Icc_self ht)
  obtain ⟨εJ,hεJ,hεJb,Jbar,Pbar,hJa,hPa,_,hJs,_,hJeq,_,hJODE⟩ :=
    exists_smooth_hamiltonian_leftEndpoint_germ hab
      (fun t ht ↦ (H.position_derivative t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (H.momentum_derivative t ht).continuousAt.continuousWithinAt)
      hJ hP hU haU hAs hBs hCs
  obtain ⟨εK,hεK,hεKb,Kbar,Rbar,hKs,_,hKeq,_,_⟩ :=
    exists_smooth_integral_second_jacobi_leftEndpoint_germ hJ hP
      H.continuous_A H.continuous_B H.continuous_C
      (fun t ht ↦ H.symmetric_A t (Ioo_subset_Icc_self ht))
      (fun t ht ↦ H.symmetric_C t (Ioo_subset_Icc_self ht)) hd hc
      (H.wronskian c (Ioo_subset_Icc_self hc)) hU haU hAs hBs hCs
  let ε := min εJ εK
  have hε : 0<ε := lt_min hεJ hεK
  have hsubJ : Ioo (-ε) ε ⊆ {s : ℝ | a+s∈Ioo (a-εJ) (a+εJ)} := by
    intro s hs
    constructor <;> dsimp [ε] at hs <;> linarith [min_le_left εJ εK,hs.1,hs.2]
  have hsubK : Ioo (-ε) ε ⊆ {s : ℝ | a+s∈Ioo (a-εK) (a+εK)} := by
    intro s hs
    constructor <;> dsimp [ε] at hs <;> linarith [min_le_right εJ εK,hs.1,hs.2]
  have hJshift : ContDiffOn ℝ ∞ (fun s ↦ Jbar (a+s)) (Ioo (-ε) ε) :=
    hJs.comp (contDiffOn_const.add contDiffOn_id) hsubJ
  have hKshift : ContDiffOn ℝ ∞ (fun s ↦ Kbar (a+s)) (Ioo (-ε) ε) :=
    hKs.comp (contDiffOn_const.add contDiffOn_id) hsubK
  have hda := (hJODE a (show a∈Ioo (a-εJ) (a+εJ) from ⟨by linarith,by linarith⟩)).1
  have hda0 : HasDerivAt Jbar (B a*Jbar a+C a*Pbar a) (a+(0:ℝ)) := by
    simpa only [add_zero] using hda
  have hdshift : HasDerivAt (fun s ↦ Jbar (a+s)) (B a*Jbar a+C a*Pbar a) 0 := by
    simpa only [Function.comp_def,add_zero,one_smul] using
      hda0.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add a)
  have hcross : ∀ u, Jbar (a+0)*ᵥu=0 →
      deriv (fun s ↦ Jbar (a+s)) 0*ᵥu∈LinearMap.range (Jbar (a+0)).mulVecLin → u=0 := by
    intro u hu hrange
    rw [hdshift.deriv,hJa,hPa] at hrange
    simp only [add_zero,hJa] at hu hrange
    exact focal_crossing_kernel_eq_zero (H.wronskian a ha) (H.phase_rank a ha)
      (H.positive_C a ha) hu hrange
  obtain ⟨V,R,Brem,hV,h0,hVU,hBrem,_,hpole⟩ :=
    exists_smooth_focal_product_pole isOpen_Ioo (show (0:ℝ)∈Ioo (-ε) ε by constructor <;> linarith)
      hJshift hKshift hcross
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let η := min (r/2) ε
  have hη : 0<η := lt_min (half_pos hr) hε
  have hηr : η<r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hηε : η≤ε := min_le_right _ _
  have hηV : Ioo (-η) η ⊆ V := by
    intro s hs
    apply hrV
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith [hs.1,hs.2]
  refine ⟨η,hη,?_,R*Kbar a,Brem,hBrem.mono hηV,fun s hs ↦ ?_⟩
  · exact (hηε.trans (min_le_left εJ εK)).trans_lt hεJb
  · have hsV := hηV (show s∈Ioo (-η) η by constructor <;> linarith [hs.1,hs.2])
    have hsJ : a+s∈Ioo a (a+εJ) := by
      constructor <;> linarith [hs.1,hs.2,hηε.trans (min_le_left εJ εK)]
    have hsK : a+s∈Ioo a (a+εK) := by
      constructor <;> linarith [hs.1,hs.2,hηε.trans (min_le_right εJ εK)]
    have hsold : a+s∈Ioo a b := ⟨by linarith [hs.1],by linarith [hsJ.2,hεJb]⟩
    have hp := hpole s hsV (ne_of_gt hs.1)
    simp only [add_zero] at hp
    rw [hJeq hsJ,hKeq hsK,Matrix.nonsing_inv_mul_cancel_left _ _
      (isUnit_iff_ne_zero.mpr (hd (a+s) hsold))] at hp
    exact hp

end OTSelector.Reconstruction
