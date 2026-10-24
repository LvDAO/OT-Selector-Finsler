import OTSelector.Reconstruction.ActualJacobiPrimitiveSimplePole
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Actual mobility has a double pole and no simple-pole term

The compliance primitive's actual integral second solution internally gives its exact
simple-pole expansion. Differentiating that same primitive proves the actual Hamiltonian
mobility equals a fixed double pole plus a remainder smooth through the focal endpoint.
No cancellation of a potential simple-pole coefficient is postulated.
-/

open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual mobility of a closed Hamiltonian system has a double pole with a smooth
remainder. This follows from smooth endpoint continuation and differentiation of its actual
compliance primitive; there is no simple-pole term. -/
theorem ClosedHamiltonianJacobiSystem.exists_actual_left_kernel_double_pole
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀ t∈Ioo a b, (J t).det≠0) (hc : c∈Ioo a b)
    {U : Set ℝ} (hU : IsOpen U) (haU : a∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U) (hCs : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ (G : Matrix n n ℝ) (R : ℝ → Matrix n n ℝ),
      ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧ ∀ s∈Ioo 0 ε,
        (J (a+s))⁻¹*C (a+s)*(J (a+s))⁻¹ᵀ=(s^2)⁻¹•G+R s := by
  obtain ⟨ε,hε,hεb,R,Brem,hBrem,hpole⟩ :=
    H.exists_actual_left_primitive_simple_pole hd hc hU haU hAs hBs hCs
  have hJdiff : DifferentiableOn ℝ J (Ioo a b) :=
    fun t ht ↦ (H.position_derivative t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  refine ⟨ε,hε,hεb,-R,deriv Brem,hBrem.deriv_of_isOpen isOpen_Ioo (by simp),fun s hs ↦ ?_⟩
  have hsold : a+s∈Ioo a b := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hT := hasDerivAt_jacobiCompliancePrimitive hJdiff
    (H.continuous_C.mono Ioo_subset_Icc_self) hd hc hsold
  have hTs : HasDerivAt (fun r ↦ jacobiCompliancePrimitive J C c (a+r))
      ((J (a+s))⁻¹*C (a+s)*(J (a+s))⁻¹ᵀ) s := by
    simpa only [Function.comp_def,one_smul] using
      hT.scomp s ((hasDerivAt_id s).const_add a)
  have hsB : s∈Ioo (-ε) ε := ⟨by linarith [hs.1],hs.2⟩
  have hBd := ((hBrem.contDiffAt (isOpen_Ioo.mem_nhds hsB)).differentiableAt (by simp)).hasDerivAt
  have hpolD : HasDerivAt (fun r ↦ r⁻¹•R+Brem r)
      (-(s^2)⁻¹•R+deriv Brem s) s := (hasDerivAt_inv (ne_of_gt hs.1)).smul_const R |>.add hBd
  have hTpole := hpolD.congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr ↦ hpole r hr)
  simpa only [smul_neg,neg_smul] using hTs.unique hTpole

end OTSelector.Reconstruction
