import OTSelector.Analysis.ODE.Hamiltonian.SmoothNonautonomousLocalCurve
import OTSelector.Analysis.ODE.HamiltonianEndpointUniqueness
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SmoothHamiltonianEndpointGerm.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SmoothHamiltonianEndpointGerm`; the selected original proof blocks follow. -/
section

/-!
Conditions: Smooth coefficients of the stated linear Hamiltonian system and a one-sided continuous solution with actual endpoint value.

Objects: A local smooth pair through that actual endpoint and equality with the original pair on the one-sided germ.

Proof detail: Solve the smooth endpoint IVP and use one-sided uniqueness to identify it with the original solution.

Sources: Gerald Teschl, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49); Gerald Teschl, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57); Gerald Teschl, Section 2.4, Lemma 2.7 and Theorem 2.8, pp. 42–44, equations (2.38)–(2.43) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=53).
Relation: Endpoint extension/uniqueness corollary; endpoint smoothness of the original second solution is proved rather than assumed.
-/

/-!
# Smooth continuation of actual Hamiltonian endpoint values

Smooth coefficients produce a new local solution through the actual endpoint value of a
continuous original solution. Endpoint uniqueness then identifies the new solution with
the original one on the original side. Thus smoothness through the endpoint is a conclusion;
it is never a hypothesis on the original integral second solution.
-/

open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Smooth actual Hamiltonian coefficients give an open-interval smooth solution through
any prescribed position and momentum matrices at the unchanged original clock. -/
theorem exists_smooth_local_hamiltonian_pair
    {A B C : ℝ → Matrix n n ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U)
    {a : ℝ} (ha : a∈U) (J₀ P₀ : Matrix n n ℝ) :
    ∃ ε : ℝ, ε>0 ∧ ∃ J P : ℝ → Matrix n n ℝ,
      J a=J₀ ∧ P a=P₀ ∧ Ioo (a-ε) (a+ε) ⊆ U ∧
      ContDiffOn ℝ ∞ J (Ioo (a-ε) (a+ε)) ∧
      ContDiffOn ℝ ∞ P (Ioo (a-ε) (a+ε)) ∧
      ∀ t∈Ioo (a-ε) (a+ε),
        HasDerivAt J (B t*J t+C t*P t) t ∧
        HasDerivAt P (-A t*J t-(B t)ᵀ*P t) t := by
  let X : ℝ → (Matrix n n ℝ×Matrix n n ℝ) → (Matrix n n ℝ×Matrix n n ℝ) :=
    fun t z ↦ (B t*z.1+C t*z.2,-A t*z.1-(B t)ᵀ*z.2)
  let L := (Matrix.transposeLinearEquiv n n ℝ ℝ).toLinearMap.toContinuousLinearMap
  have hBT : ContDiffOn ℝ ∞ (fun t ↦ (B t)ᵀ) U := L.contDiff.comp_contDiffOn hB
  have hAt : ContDiffOn ℝ ∞ (fun q : ℝ×(Matrix n n ℝ×Matrix n n ℝ) ↦ A q.1)
      (U×ˢuniv) := hA.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  have hBt : ContDiffOn ℝ ∞ (fun q : ℝ×(Matrix n n ℝ×Matrix n n ℝ) ↦ B q.1)
      (U×ˢuniv) := hB.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  have hCt : ContDiffOn ℝ ∞ (fun q : ℝ×(Matrix n n ℝ×Matrix n n ℝ) ↦ C q.1)
      (U×ˢuniv) := hC.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  have hBTt : ContDiffOn ℝ ∞ (fun q : ℝ×(Matrix n n ℝ×Matrix n n ℝ) ↦ (B q.1)ᵀ)
      (U×ˢuniv) := hBT.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  have hX : ContDiffOn ℝ ∞ (Function.uncurry X) (U×ˢuniv) :=
    ((hBt.mul contDiffOn_snd.fst).add (hCt.mul contDiffOn_snd.snd)).prodMk
      ((hAt.neg.mul contDiffOn_snd.fst).sub (hBTt.mul contDiffOn_snd.snd))
  obtain ⟨ε,hε,γ,hγa,hsub,hsmooth,hγ⟩ :=
    exists_smooth_nonautonomous_localCurve hU hX ha (J₀,P₀)
  exact ⟨ε,hε,fun t ↦ (γ t).1,fun t ↦ (γ t).2,
    congrArg Prod.fst hγa,congrArg Prod.snd hγa,hsub,hsmooth.fst,hsmooth.snd,
    fun t ht ↦ ⟨(hγ t ht).fst,(hγ t ht).snd⟩⟩

/-- A continuous actual Hamiltonian solution has a smooth germ through its left endpoint
when its actual coefficients are smooth there. Equality on the original side is proved
by endpoint uniqueness for the unchanged linear Hamiltonian system. -/
theorem exists_smooth_hamiltonian_leftEndpoint_germ
    {J P A B C : ℝ → Matrix n n ℝ} {a b : ℝ} (hab : a<b)
    (hJcont : ContinuousOn J (Icc a b)) (hPcont : ContinuousOn P (Icc a b))
    (hJ : ∀ t∈Ioo a b, HasDerivAt J (B t*J t+C t*P t) t)
    (hP : ∀ t∈Ioo a b, HasDerivAt P (-A t*J t-(B t)ᵀ*P t) t)
    {U : Set ℝ} (hU : IsOpen U) (ha : a∈U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) :
    ∃ ε : ℝ, ε>0 ∧ ε<b-a ∧ ∃ Jbar Pbar : ℝ → Matrix n n ℝ,
      Jbar a=J a ∧ Pbar a=P a ∧ Ioo (a-ε) (a+ε) ⊆ U ∧
      ContDiffOn ℝ ∞ Jbar (Ioo (a-ε) (a+ε)) ∧
      ContDiffOn ℝ ∞ Pbar (Ioo (a-ε) (a+ε)) ∧
      EqOn Jbar J (Ioo a (a+ε)) ∧ EqOn Pbar P (Ioo a (a+ε)) ∧
      ∀ t∈Ioo (a-ε) (a+ε),
        HasDerivAt Jbar (B t*Jbar t+C t*Pbar t) t ∧
        HasDerivAt Pbar (-A t*Jbar t-(B t)ᵀ*Pbar t) t := by
  obtain ⟨δ,hδ,Jbar,Pbar,hJa,hPa,hδU,hJs,hPs,hsol⟩ :=
    exists_smooth_local_hamiltonian_pair hU hA hB hC ha (J a) (P a)
  let ε := min (δ/2) ((b-a)/2)
  have hε : 0<ε := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hab))
  have hεδ : ε<δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hεb : ε<b-a := (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hab))
  have hsub : Icc a (a+ε) ⊆ Ioo (a-δ) (a+δ) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hsmall : Ioo (a-ε) (a+ε) ⊆ Ioo (a-δ) (a+δ) :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have hold : Icc a (a+ε) ⊆ Icc a b := Icc_subset_Icc le_rfl (by linarith)
  have holdI : Ioo a (a+ε) ⊆ Ioo a b := Ioo_subset_Ioo le_rfl (by linarith)
  have hdiffJ : ∀ t∈Ioo a (a+ε),
      HasDerivAt (fun t ↦ Jbar t-J t)
        (B t*(Jbar t-J t)+C t*(Pbar t-P t)) t := by
    intro t ht
    have heq : B t*(Jbar t-J t)+C t*(Pbar t-P t) =
        (B t*Jbar t+C t*Pbar t)-(B t*J t+C t*P t) := by
      simp only [Matrix.mul_sub]
      abel
    rw [heq]
    exact ((hsol t (hsub (Ioo_subset_Icc_self ht))).1).sub (hJ t (holdI ht))
  have hdiffP : ∀ t∈Ioo a (a+ε),
      HasDerivAt (fun t ↦ Pbar t-P t)
        (-A t*(Jbar t-J t)-(B t)ᵀ*(Pbar t-P t)) t := by
    intro t ht
    have heq : -A t*(Jbar t-J t)-(B t)ᵀ*(Pbar t-P t) =
        (-A t*Jbar t-(B t)ᵀ*Pbar t)-(-A t*J t-(B t)ᵀ*P t) := by
      simp only [Matrix.mul_sub]
      abel
    rw [heq]
    exact ((hsol t (hsub (Ioo_subset_Icc_self ht))).2).sub (hP t (holdI ht))
  have heq : ∀ t∈Ioo a (a+ε), Jbar t=J t ∧ Pbar t=P t := by
    intro t ht
    have hz := hamiltonian_pair_eq_zero_of_endpoint_eq_zero
      ((hJs.continuousOn.mono hsub).sub (hJcont.mono hold))
      ((hPs.continuousOn.mono hsub).sub (hPcont.mono hold)) hdiffJ hdiffP
      (hA.continuousOn.mono (hsub.trans hδU))
      (hB.continuousOn.mono (hsub.trans hδU))
      (hC.continuousOn.mono (hsub.trans hδU)) ht
      (show a∈Icc a (a+ε) from ⟨le_rfl,by linarith⟩)
      (sub_eq_zero.mpr hJa) (sub_eq_zero.mpr hPa)
    exact ⟨sub_eq_zero.mp hz.1,sub_eq_zero.mp hz.2⟩
  exact ⟨ε,hε,hεb,Jbar,Pbar,hJa,hPa,hsmall.trans hδU,hJs.mono hsmall,hPs.mono hsmall,
    fun t ht ↦ (heq t ht).1,fun t ht ↦ (heq t ht).2,fun t ht ↦ hsol t (hsmall ht)⟩

end OTSelector.Geometry

end
end
