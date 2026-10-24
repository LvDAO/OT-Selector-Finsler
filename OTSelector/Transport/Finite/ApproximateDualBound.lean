import LeanPool.Vlasov.OT.Coupling

/-!
# Transport.Finite.ApproximateDualBound

## Lemma skeleton

* **Conditions:** Finite nonnegative probability masses, a real cost matrix and a uniform dual upper bound budget+epsilon*entropy for every positive epsilon.

* **Objects:** One actual finite coupling with cost at most the limiting budget.

* **Proof detail:** Choose an optimal finite transport plan by linear-programming/Kantorovich duality. Bound its fixed cost by each approximate soft-dual budget and send epsilon to zero without changing the primal plan.

## Mathematical sources

- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31): Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20).
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation (corollary): Soft-error removal around a fixed finite optimum; no continuous Hamilton–Jacobi or PDE solver theorem is assumed by this lemma.
-/

/-! A fixed optimal finite plan consumes approximate soft dual bounds, so
removing smoothing errors never changes the primal finite experiment. -/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
variable {I J : Type*} [Fintype I] [Fintype J]

/-- A price-uniform approximate dual estimate bounds one fixed genuine finite
transport plan after both dual and soft errors vanish. -/
theorem exists_finiteTransport_plan_le_of_soft_dual_bounds
    (α : I→ℝ) (β : J→ℝ) (cost : I→J→ℝ)
    (hα : ∀i,0≤α i) (hβ : ∀j,0≤β j)
    (hαmass : ∑i,α i=1) (hβmass : ∑j,β j=1) (budget entropy : ℝ)
    (hdual : ∀ε:ℝ,0<ε→∀u:I→ℝ,∀v:J→ℝ,
      (∀i j,u i+v j≤cost i j)→
      (∑i,α i*u i)+(∑j,β j*v j)≤budget+ε*entropy) :
    ∃P:I→J→ℝ,(∀i j,0≤P i j)∧(∀i,∑j,P i j=α i)∧(∀j,∑i,P i j=β j)∧
      (∑i,∑j,cost i j*P i j)≤budget := by
  obtain ⟨P,hP,hrow,hcol,hmin⟩:=Vlasov.exists_transport_min α β cost hα hβ hαmass hβmass
  refine ⟨P,hP,hrow,hcol,?_⟩
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨ε,hε,heps⟩:=exists_pos_mul_lt (half_pos hη) entropy
  obtain ⟨u,v,huv,hvalue⟩:=Vlasov.finiteTransport_dual_eps α β cost P hP hrow hcol hmin
    (η/2) (half_pos hη)
  have hb:=hdual ε hε u v huv
  nlinarith only [hvalue,hb,heps]

end OTSelector.Reconstruction
