import OTSelector.Geometry.Finsler.Hamiltonian.IntegralCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SmoothNonautonomousLocalCurve.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SmoothNonautonomousLocalCurve`; the selected original proof blocks follow. -/
section

/-!
Conditions: A smooth time-dependent vector field satisfies the stated local existence hypotheses.

Objects: A smooth local curve solving the original nonautonomous equation.

Proof detail: Adjoin the clock with derivative one, solve the autonomous lifted ODE and use the initial condition to identify its clock with original time.

Sources: Gerald Teschl, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49); Gerald Teschl, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57).
Relation: Classical autonomous lift of a nonautonomous ODE, implemented for the stated spaces.
-/

/-!
# Actual smooth local continuation for nonautonomous equations

Time is adjoined to the actual state and evolves at speed one. Smooth autonomous local
existence then produces a smooth solution of the unchanged nonautonomous equation on an
open interval through its prescribed initial value. The adjoined clock is proved to equal
the original time, so no reparameterized or substitute equation is used.
-/

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local smooth nonautonomous existence is internally derived by adjoining the actual
clock; both sides of the initial time are included in the resulting open interval. -/
theorem exists_smooth_nonautonomous_localCurve
    {X : ℝ → E → E} {U : Set ℝ} (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ (Function.uncurry X) (U×ˢuniv))
    {a : ℝ} (ha : a∈U) (z : E) :
    ∃ ε : ℝ, ε>0 ∧ ∃ γ : ℝ → E, γ a=z ∧
      Ioo (a-ε) (a+ε) ⊆ U ∧ ContDiffOn ℝ ∞ γ (Ioo (a-ε) (a+ε)) ∧
      ∀ t∈Ioo (a-ε) (a+ε), HasDerivAt γ (X t (γ t)) t := by
  let Y : ℝ×E → ℝ×E := fun q ↦ (1,X q.1 q.2)
  have hY : ContDiffOn ℝ ∞ Y (U×ˢuniv) := contDiffOn_const.prodMk hX
  obtain ⟨ε,hε,α,hαa,hmap,hα,hsmooth,_⟩ :=
    exists_smooth_integralCurve_in_open (hU.prod isOpen_univ) hY
      (show (a,z)∈U×ˢ(univ : Set E) from ⟨ha,mem_univ _⟩) a
  have haI : a∈Ioo (a-ε) (a+ε) := ⟨by linarith,by linarith⟩
  have htimeD : ∀ t∈Ioo (a-ε) (a+ε), HasDerivAt (fun t ↦ (α t).1) 1 t := by
    intro t ht
    exact (hα t ht).fst
  have htime : EqOn (fun t ↦ (α t).1) id (Ioo (a-ε) (a+ε)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun t ht ↦ (htimeD t ht).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
      (fun t ht ↦ (htimeD t ht).deriv.trans (hasDerivAt_id t).deriv.symm) haI
    exact congrArg Prod.fst hαa
  refine ⟨ε,hε,fun t ↦ (α t).2,congrArg Prod.snd hαa,?_,hsmooth.snd,?_⟩
  · intro t ht
    simpa only [htime ht,id_eq] using (hmap ht).1
  · intro t ht
    have hd := (hα t ht).snd
    change HasDerivAt (fun t ↦ (α t).2) (X (α t).1 (α t).2) t at hd
    simpa only [htime ht,id_eq] using hd

end OTSelector.Geometry

end
end
