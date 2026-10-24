import OTSelector.Transport.Finite.ApproximateDualBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiFiniteMassPlan.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiFiniteMassPlan`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiFiniteMassPlan

**Conditions:** Nonnegative finite marginals have the same positive total mass; every feasible finite dual obeys budget+ε entropy for all ε>0.

**Objects:** A nonnegative finite transport matrix with the original unnormalized marginals and exact budget bound.

**Proof detail:** Normalize the marginals, apply finite transport duality, scale the resulting plan back by the common mass, and send the arbitrary entropy slack ε to zero.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test); [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! The finite quadratic LP budget scales to the original common positive mass;
the Neumann energy constant is not multiplied by an artificial normalization. -/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Approximate soft dual bounds produce an actual finite plan for any common
positive original mass; normalization is internal and is undone exactly. -/
theorem exists_finiteMassTransport_plan_le_of_soft_dual_bounds
    (α : I→ℝ) (β : J→ℝ) (cost : I→J→ℝ)
    (hα : ∀i,0≤α i) (hβ : ∀j,0≤β j) {mass : ℝ} (hmass : 0<mass)
    (hαmass : ∑i,α i=mass) (hβmass : ∑j,β j=mass) (budget entropy : ℝ)
    (hdual : ∀ε:ℝ,0<ε→∀u:I→ℝ,∀v:J→ℝ,
      (∀i j,u i+v j≤cost i j)→
      (∑i,α i*u i)+(∑j,β j*v j)≤budget+ε*entropy) :
    ∃P:I→J→ℝ,(∀i j,0≤P i j)∧(∀i,∑j,P i j=α i)∧(∀j,∑i,P i j=β j)∧
      (∑i,∑j,cost i j*P i j)≤budget := by
  have hsumα : (∑i,α i/mass)=1 := by rw [← Finset.sum_div,hαmass,div_self hmass.ne']
  have hsumβ : (∑j,β j/mass)=1 := by rw [← Finset.sum_div,hβmass,div_self hmass.ne']
  obtain ⟨P,hP,hrow,hcol,hcost⟩:=exists_finiteTransport_plan_le_of_soft_dual_bounds
    (fun i↦α i/mass) (fun j↦β j/mass) cost
    (fun i↦div_nonneg (hα i) hmass.le) (fun j↦div_nonneg (hβ j) hmass.le)
    hsumα hsumβ (budget/mass) (entropy/mass) (by
      intro ε hε u v huv
      have hb:=div_le_div_of_nonneg_right (hdual ε hε u v huv) hmass.le
      simp_rw [div_mul_eq_mul_div,← Finset.sum_div] at ⊢
      calc
        (∑i,α i*u i)/mass+(∑j,β j*v j)/mass =
            ((∑i,α i*u i)+(∑j,β j*v j))/mass := by ring
        _ ≤ (budget+ε*entropy)/mass := hb
        _ = budget/mass+ε*(entropy/mass) := by ring)
  refine ⟨fun i j↦mass*P i j,fun i j↦mul_nonneg hmass.le (hP i j),?_,?_,?_⟩
  · intro i
    rw [← Finset.mul_sum,hrow,mul_div_cancel₀ _ hmass.ne']
  · intro j
    rw [← Finset.mul_sum,hcol,mul_div_cancel₀ _ hmass.ne']
  · calc
      (∑i,∑j,cost i j*(mass*P i j))=mass*(∑i,∑j,cost i j*P i j) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ mass*(budget/mass) := mul_le_mul_of_nonneg_left hcost hmass.le
      _ = budget := mul_div_cancel₀ _ hmass.ne'

end OTSelector.Reconstruction

end
end
