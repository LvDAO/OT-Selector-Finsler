import Mathlib.Data.Nat.Choose.Multinomial
import OTSelector.Finite.CapacityAssignment

/-!
Conditions: Natural finite row/label sizes and natural capacities whose sum equals the row count; no probability law or cost function is used.

Objects: Fiber equivalence codes, the induced permutation bijection and the exact multinomial count of all assignments with those capacities.

Proof detail: Encode each permutation by its capacity-feasible target word and within-fiber bijections. Prove both reconstruction directions and compare finite cardinalities to the factorial quotient.

References: Terence Tao: Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; OTSelector project: main.tex label thm:iid-cavity-dirichlet, line 4290.
Relation: This is the project’s explicit finite combinatorial implementation of the multinomial coefficient; it does not infer independence or a probability formula from cardinality alone.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityDirichletWordCount.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityDirichletWordCount`; the selected original proof blocks follow. -/
section

/-!
# The exact multiplicity of cavity allocation words

Target-count words are counted by labelled slot permutations. Once the target word is
fixed, the remaining choices are precisely independent bijections on each target fiber.
This gives the factorial multiplicity needed in the cavity mixed-moment identity.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n K : ℕ}

private abbrev wordFiberEquivs (r : Fin (n + 1) → ℕ) (target : Fin K → Fin (n + 1)) :=
  Σ a : {a : Fin K → Fin (n + 1) // CapacityFeasible r a},
    ∀ j, {k // a.val k = j} ≃ {k // target k = j}

private def wordFiberPerm (r : Fin (n + 1) → ℕ) (target : Fin K → Fin (n + 1))
    (x : wordFiberEquivs r target) : Equiv.Perm (Fin K) :=
  Equiv.ofFiberEquiv x.2

private theorem wordFiberPerm_bijective
    (r : Fin (n + 1) → ℕ) (target : Fin K → Fin (n + 1))
    (ht : CapacityFeasible r target) : Function.Bijective (wordFiberPerm r target) := by
  constructor
  · rintro ⟨a, e⟩ ⟨b, f⟩ hef
    have hab : a = b := by
      apply Subtype.ext
      funext k
      exact (Equiv.ofFiberEquiv_map e k).symm.trans
        ((congrArg (fun σ : Equiv.Perm (Fin K) ↦ target (σ k)) hef).trans
          (Equiv.ofFiberEquiv_map f k))
    subst b
    apply Sigma.mk.inj_iff.mpr
    refine ⟨rfl, heq_of_eq ?_⟩
    funext j
    apply Equiv.ext
    rintro ⟨k, rfl⟩
    apply Subtype.ext
    exact congrArg (fun σ : Equiv.Perm (Fin K) ↦ σ k) hef
  · intro σ
    let a : {a : Fin K → Fin (n + 1) // CapacityFeasible r a} :=
      ⟨target ∘ σ, capacityFeasible_comp_perm r target ht σ⟩
    refine ⟨⟨a, fun j ↦ σ.subtypeEquiv (p := fun k ↦ a.val k = j)
      (q := fun k ↦ target k = j) (fun _ ↦ Iff.rfl)⟩, ?_⟩
    apply Equiv.ext
    intro k
    rfl

/-- The number of words with prescribed target counts is the multinomial coefficient. -/
theorem card_capacityFeasible_eq_multinomial
    (r : Fin (n + 1) → ℕ) (hr : ∑ j, r j = K) :
    Nat.card {a : Fin K → Fin (n + 1) // CapacityFeasible r a} =
      Nat.multinomial Finset.univ r := by
  classical
  let target := capacitySlotLabel r hr
  have ht : CapacityFeasible r target := capacitySlotLabel_feasible r hr
  have he := Fintype.card_congr (Equiv.ofBijective (wordFiberPerm r target)
    (wordFiberPerm_bijective r target ht))
  have hf (a : {a : Fin K → Fin (n + 1) // CapacityFeasible r a}) (j : Fin (n + 1)) :
      Fintype.card ({k // a.val k = j} ≃ {k // target k = j}) = (r j).factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq ((a.property j).trans (ht j).symm)),
      a.property j]
  change Fintype.card (Σ a : {a : Fin K → Fin (n + 1) // CapacityFeasible r a},
    ∀ j, {k // a.val k = j} ≃ {k // target k = j}) = Fintype.card (Equiv.Perm (Fin K)) at he
  rw [Fintype.card_sigma] at he
  simp_rw [Fintype.card_pi, hf] at he
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_fin] at he
  rw [Nat.card_eq_fintype_card]
  apply Nat.eq_of_mul_eq_mul_right
    (show 0 < ∏ j, (r j).factorial from Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _)
  calc
    _ = K.factorial := by simpa using he
    _ = _ := by rw [mul_comm (Nat.multinomial _ _), Nat.multinomial_spec, hr]

end OTSelector.Probability

end
end
