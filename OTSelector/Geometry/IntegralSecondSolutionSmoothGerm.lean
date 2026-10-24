import OTSelector.Geometry.JacobiEndpoint
import OTSelector.Analysis.ODE.Hamiltonian.SmoothEndpointGerm
import OTSelector.Geometry.JacobiPrimitive

/-!
# Smooth endpoint germ of the actual integral second Jacobi solution

The second solution is constructed from the unchanged original compliance integral. Its
continuous endpoint values are produced by the existing Hamiltonian extension theorem.
Smooth local existence and endpoint uniqueness then supply a smooth continuation through
the focal endpoint which agrees with that same integral construction on the original side.
-/

open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual integral second solution has a smooth left-endpoint germ derived from its
Hamiltonian equations and the actual coefficients' smoothness near that endpoint. -/
theorem exists_smooth_integral_second_jacobi_leftEndpoint_germ
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ t∈Ioo a b, HasDerivAt J (B t*J t+C t*P t) t)
    (hP : ∀ t∈Ioo a b, HasDerivAt P (-A t*J t-(B t)ᵀ*P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t∈Ioo a b, (A t)ᵀ=A t)
    (hCsym : ∀ t∈Ioo a b, (C t)ᵀ=C t)
    (hd : ∀ t∈Ioo a b, (J t).det≠0) (hc : c∈Ioo a b)
    (hinit : (J c)ᵀ*P c=(P c)ᵀ*J c)
    {U : Set ℝ} (hU : IsOpen U) (ha : a∈U)
    (hAs : ContDiffOn ℝ ∞ A U) (hBs : ContDiffOn ℝ ∞ B U) (hCs : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ K R : ℝ → Matrix n n ℝ,
      ContDiffOn ℝ ∞ K (Ioo (a-ε) (a+ε)) ∧
      ContDiffOn ℝ ∞ R (Ioo (a-ε) (a+ε)) ∧
      EqOn K (fun t ↦ J t*jacobiCompliancePrimitive J C c t) (Ioo a (a+ε)) ∧
      EqOn R (fun t ↦ P t*jacobiCompliancePrimitive J C c t+(J t)⁻¹ᵀ) (Ioo a (a+ε)) ∧
      ∀ t∈Ioo (a-ε) (a+ε),
        HasDerivAt K (B t*K t+C t*R t) t ∧
        HasDerivAt R (-A t*K t-(B t)ᵀ*R t) t := by
  have hsol := fun t (ht : t∈Ioo a b) ↦ hasDerivAt_integral_second_jacobi_solution
    hJ hP hAsym hCsym (hC.mono Ioo_subset_Icc_self) hd hc hinit ht
  obtain ⟨Kbar,Rbar,hKbar,hRbar,hKeq,hReq⟩ := exists_continuous_integral_second_jacobi_extension
    hJ hP hA hB hC hAsym hCsym hd hc hinit
  have hKd : ∀ t∈Ioo a b, HasDerivAt Kbar (B t*Kbar t+C t*Rbar t) t := by
    intro t ht
    rw [hKeq ht,hReq ht]
    exact ((hsol t ht).1).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs ↦ hKeq hs)
  have hRd : ∀ t∈Ioo a b, HasDerivAt Rbar (-A t*Kbar t-(B t)ᵀ*Rbar t) t := by
    intro t ht
    rw [hKeq ht,hReq ht]
    exact ((hsol t ht).2).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs ↦ hReq hs)
  obtain ⟨ε,hε,hεb,K,R,_,_,_,hKs,hRs,hK,hR,hODE⟩ :=
    exists_smooth_hamiltonian_leftEndpoint_germ (hc.1.trans hc.2) hKbar hRbar hKd hRd
      hU ha hAs hBs hCs
  have hsub : Ioo a (a+ε) ⊆ Ioo a b := Ioo_subset_Ioo le_rfl (by linarith)
  exact ⟨ε,hε,hεb,K,R,hKs,hRs,fun t ht ↦ (hK ht).trans (hKeq (hsub ht)),
    fun t ht ↦ (hR ht).trans (hReq (hsub ht)),hODE⟩

end OTSelector.Geometry
